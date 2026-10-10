import Mathlib
import OAI.Analysis.BiholderTransport.Regularity.HopfApproximation
import OAI.Analysis.BiholderTransport.Regularity.ActualParameter

namespace OAI

noncomputable section
open Set Filter
open scoped Topology NNReal BoundedContinuousFunction

namespace WeakMTWTransport
variable {M : Type*} [MetricSpace M] [CompactSpace M] [Nonempty M]

def boundedModifiedDatum (v : M → ℝ) (hv : Continuous v) (a D : ℝ)
    (B : ℝ → ℝ) (hB : Continuous B) (b : ℝ) : M →ᵇ ℝ :=
  BoundedContinuousFunction.mkOfCompact ⟨v,hv⟩ + b •
    BoundedContinuousFunction.mkOfCompact ⟨fun y => B ((v y-a)/D),
      hB.comp ((hv.sub continuous_const).div_const D)⟩

omit [Nonempty M] in
lemma continuous_boundedModifiedDatum (v : M → ℝ) (hv : Continuous v) (a D : ℝ)
    (B : ℝ → ℝ) (hB : Continuous B) : Continuous (boundedModifiedDatum v hv a D B hB) :=
  continuous_const.add (continuous_id.smul continuous_const)

lemma continuous_cTransform_family {X : Type*} [TopologicalSpace X]
    {U : X → M →ᵇ ℝ} (hU : Continuous U) :
    Continuous (fun q : X×M => cTransform (U q.1) q.2) := by
  exact continuous_eval.comp ((boundedCTransform_nonexpansive.continuous.comp
    (hU.comp continuous_fst)).prodMk continuous_snd)

lemma continuous_hopfLax_family {X : Type*} [TopologicalSpace X]
    {U : X → M →ᵇ ℝ} (hU : Continuous U) {t : ℝ} (ht : 0<t) :
    Continuous (fun q : X×M => hopfLax t (U q.1) q.2) := by
  have H := (continuous_cTransform_family ((continuous_const : Continuous (fun _ : X => t)).smul hU)).neg.div_const t
  convert H using 1
  funext q
  exact hopfLax_eq_neg_transform (U q.1).continuous ht q.2

lemma continuous_regularizedComparison {v : M → ℝ} (hv : Continuous v)
    (a D bplus : ℝ) {t : ℝ} (ht : 0<t) (ht1 : t<1)
    {Bc Bo : ℝ → ℝ} (hc : Continuous Bc) (ho : Continuous Bo) :
    Continuous (regularizedComparison v a D bplus t Bc Bo) := by
  have H1 := continuous_hopfLax_family
    (boundedCTransform_nonexpansive.continuous.comp
      (continuous_boundedModifiedDatum v hv a D Bo ho)) ht
  have H2 := continuous_hopfLax_family
    (continuous_boundedModifiedDatum v hv a D Bc hc) (sub_pos.mpr ht1)
  have HP : Continuous (fun q : ℝ×M => parameterPenalty bplus q.1) := by
    unfold parameterPenalty
    fun_prop
  exact (H1.add H2).sub HP

lemma regularizedComparison_error {v : M → ℝ} (hv : Continuous v)
    {a D bplus t b H : ℝ} {Bc Bo : ℝ → ℝ} (ho : Continuous Bo)
    {L : ℝ≥0} (hc : LipschitzWith L (modifiedDatum v a D b Bc))
    (hH : ∀ x y : M,cost x y≤H) (_ : 0<t) (ht1 : t<1) (z : M) :
    |regularizedComparison v a D bplus t Bc Bo (b,z)-
      (modifiedExcess v a D b Bc Bo z-parameterPenalty bplus b)|≤
        H*|1/t-1|+(L:ℝ)^2*(1-t)/2 := by
  have Hg := continuous_cTransform (continuous_modifiedDatum hv a D b ho)
  have H1 := hopfLax_time_comparison Hg hH t 1 z
  rw [one_div_one,hopfLax_one _ Hg] at H1
  have H2 := hopfLax_short_approx hc (sub_pos.mpr ht1) z
  have H3 := abs_le.mp H1
  rw [abs_le]
  dsimp only [regularizedComparison,modifiedExcess]
  constructor <;> linarith only [H3.1,H3.2,H2.1,H2.2,
    mul_nonneg (sq_nonneg (L:ℝ)) (sub_nonneg.mpr ht1.le)]

lemma regularized_interior_maximum {v : M → ℝ} (hv : Continuous v)
    {a D bplus bminus t err : ℝ} {Bc Bo : ℝ → ℝ}
    (hc : Continuous Bc) (ho : Continuous Bo) (ht : 0<t) (ht1 : t<1)
    (hp : 0<bplus) (hm : 0≤bminus)
    (hsmall : bminus≤bplus/(64*1024^2))
    (herr : err≤bplus/(128*1024^2))
    (hupper : ∀ b∈Icc bminus bplus,∀ z, modifiedExcess v a D b Bc Bo z≤b)
    (hlower : ∃ y, bplus/(8*1024^2)≤ modifiedExcess v a D (bplus/(8*1024)) Bc Bo y)
    (he : ∀ b∈Icc bminus bplus,∀ z,
      |regularizedComparison v a D bplus t Bc Bo (b,z)-
        (modifiedExcess v a D b Bc Bo z-parameterPenalty bplus b)|≤err) :
    ∃ q : ℝ×M, q.1∈Ioo bminus bplus ∧
      0<regularizedComparison v a D bplus t Bc Bo q ∧
      ∀ w : ℝ×M,w.1∈Icc bminus bplus →
        regularizedComparison v a D bplus t Bc Bo w≤regularizedComparison v a D bplus t Bc Bo q := by
  let bs := bplus/(8*1024)
  have hbs : bs∈Icc bminus bplus := by dsimp [bs]; constructor <;> linarith only [hsmall,hp]
  have hmp : bminus≤bplus := hbs.1.trans hbs.2
  obtain ⟨y,hy⟩ := hlower
  change bplus/(8*1024^2)≤ modifiedExcess v a D bs Bc Bo y at hy
  let F := regularizedComparison v a D bplus t Bc Bo
  have hPstar : parameterPenalty bplus bs=bplus/(16*1024^2) := by
    dsimp [parameterPenalty,bs]
    field_simp [hp.ne']
    ring
  have Hstar := (abs_le.mp (he bs hbs y)).1
  rw [hPstar] at Hstar
  have hstar : bplus/(16*1024^2)-err≤F (bs,y) := by
    change _≤regularizedComparison v a D bplus t Bc Bo (bs,y)
    linarith only [Hstar,hy]
  have HS : IsCompact (Icc bminus bplus×ˢ(univ : Set M)) := isCompact_Icc.prod isCompact_univ
  obtain ⟨q,hq,hqmax⟩ := HS.exists_isMaxOn ⟨(bs,y),hbs,mem_univ y⟩
    (continuous_regularizedComparison hv a D bplus ht ht1 hc ho).continuousOn
  have hmax : F (bs,y)≤F q := hqmax ⟨hbs,mem_univ y⟩
  have hpos : 0<F q := by linarith only [hmax,hstar,herr,hp]
  have hminus : q.1≠bminus := by
    intro h
    have H := (abs_le.mp (he q.1 hq.1 q.2)).2
    have U := hupper q.1 hq.1 q.2
    have hP : 0≤parameterPenalty bplus bminus := by dsimp [parameterPenalty]; positivity
    change F q-(modifiedExcess v a D q.1 Bc Bo q.2-parameterPenalty bplus q.1)≤err at H
    rw [h] at H U
    linarith only [H,U,hP,hmax,hstar,hsmall,herr,hp]
  have hplus : q.1≠bplus := by
    intro h
    have H := (abs_le.mp (he q.1 hq.1 q.2)).2
    have U := hupper q.1 hq.1 q.2
    have hP : parameterPenalty bplus bplus=bplus/4096+2*bplus := by
      dsimp [parameterPenalty]
      field_simp [hp.ne']
    change F q-(modifiedExcess v a D q.1 Bc Bo q.2-parameterPenalty bplus q.1)≤err at H
    rw [h,hP] at H
    rw [h] at U
    linarith only [H,U,hpos,herr,hp]
  exact ⟨q,⟨lt_of_le_of_ne hq.1.1 hminus.symm,lt_of_le_of_ne hq.1.2 hplus⟩,
    hpos,fun w hw => hqmax ⟨hw,mem_univ _⟩⟩

end WeakMTWTransport

end

end OAI
