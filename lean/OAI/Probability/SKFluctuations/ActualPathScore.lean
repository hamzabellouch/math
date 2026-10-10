import Mathlib
import OAI.Probability.SKFluctuations.ScoreMGF

namespace OAI

/-! Actual Path Score. -/

noncomputable section

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology
open MeasureTheory Filter Set
open scoped Topology
open MeasureTheory ProbabilityTheory Filter Set
namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set GaussianCalculus
open scoped Topology NNReal ENNReal BigOperators
variable {ι S : Type*} [Fintype ι] [Fintype S] [Nonempty S]

theorem scaledTransitionLaw_eq {w : S → ℝ} (hw : ∀ s, 0 < w s)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) (steps : List (GaussianStep ι))
    {a m : ℝ} (ha : OrderedSteps a steps) (hm : m ≠ 0)
    (q : ι → ℝ≥0) (x : ι → ℝ) :
    (standardDrivers ι).withDensity (hierarchyTransitions w φ ((m,q)::steps) 0 x) =
      tiltedLaw (standardDrivers ι) m (fun z => gaussianHierarchy w φ steps (x+scaleDriver q z)) := by
  have hi := gaussianHierarchy_exp_integrable hw φ steps ha q m x
  have hF : AEStronglyMeasurable (fun z => Real.exp (m*gaussianHierarchy w φ steps (x+z)))
      (Measure.pi fun i => gaussianReal 0 (q i)) := hi.aestronglyMeasurable
  have he : (∫ z, Real.exp (m*gaussianHierarchy w φ steps (x+scaleDriver q z)) ∂standardDrivers ι) =
      ∫ z, Real.exp (m*gaussianHierarchy w φ steps (x+z)) ∂Measure.pi (fun i => gaussianReal 0 (q i)) := by
    rw [← (scaleDriver_gaussian q).map_eq]
    exact (integral_map (scaleDriver q).measurable.aemeasurable
      (by rwa [(scaleDriver_gaussian q).map_eq])).symm
  congr 1
  funext z
  change ENNReal.ofReal (plantedTransitionDensity (Measure.pi fun i => gaussianReal 0 (q i))
    m (gaussianHierarchy w φ steps) x (scaleDriver q z)) = _
  rw [plantedTransitionDensity_eq hm x _ hi]
  simp only [he]

noncomputable def hierarchyScores (w : S → ℝ) (φ : S → (ι → ℝ) →L[ℝ] ℝ) :
    (steps : List (GaussianStep ι)) → (Fin steps.length → ι → ℝ) →
      Fin steps.length → (ι → ℝ) → (ι → ℝ) → ℝ
  | [], _ => fun i => Fin.elim0 i
  | (m,q)::tail, v => Fin.cons
      (fun x z => hierarchyAffineScore w φ (scaleDriver q) tail x m (v 0) z)
      (hierarchyScores w φ tail (Fin.tail v))

theorem hierarchyScores_measurable {w : S → ℝ} (hw : ∀ s, 0 < w s)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) (steps : List (GaussianStep ι))
    {a : ℝ} (ha : OrderedSteps a steps) (v : Fin steps.length → ι → ℝ) :
    ∀ i, Measurable (Function.uncurry (hierarchyScores w φ steps v i)) := by
  induction steps generalizing a with
  | nil => intro i; exact Fin.elim0 i
  | cons step tail ih =>
    rcases step with ⟨m,q⟩
    refine Fin.cases ?_ (ih ha.2.2.2 (Fin.tail v))
    have hM := (gaussianHierarchyMean_smooth hw φ
      (fun s => φ s (scaleDriver q (v 0))) tail ha.2.2.2 0).1
    have hdot : Measurable (fun xz : (ι → ℝ) × (ι → ℝ) => vectorDot (v 0) xz.2) := by
      apply Finset.measurable_sum Finset.univ
      intro i _
      exact measurable_const.mul ((measurable_pi_apply i).comp measurable_snd)
    exact hdot.sub
      ((hM.comp (continuous_fst.add ((scaleDriver q).continuous.comp continuous_snd))).measurable.const_mul m)

theorem hierarchyScores_hasSubgaussianMGF {n : ℕ} {w : S → ℝ} (hw : ∀ s, 0 < w s)
    (φ : S → (Fin (n+1) → ℝ) →L[ℝ] ℝ) (steps : List (GaussianStep (Fin (n+1))))
    {a : ℝ} (ha : OrderedSteps a steps) (v : Fin steps.length → Fin (n+1) → ℝ) :
    ∀ i x, HasSubgaussianMGF (hierarchyScores w φ steps v i x)
      ⟨∑ j, (v i j)^2, Finset.sum_nonneg (fun j _ => sq_nonneg (v i j))⟩
      ((standardDrivers (Fin (n+1))).withDensity (hierarchyTransitions w φ steps i x)) := by
  induction steps generalizing a with
  | nil => intro i; exact Fin.elim0 i
  | cons step tail ih =>
    rcases step with ⟨m,q⟩
    refine Fin.cases ?_ (ih ha.2.2.2 (Fin.tail v))
    intro x
    rw [scaledTransitionLaw_eq hw φ tail ha.2.2.2 ha.2.2.1.ne']
    exact hierarchyAffineScore_hasSubgaussianMGF hw φ (scaleDriver q) tail ha.2.2.2 x ha.2.2.1.le (v 0)

noncomputable def hierarchyPathScore (w : S → ℝ) (φ : S → (ι → ℝ) →L[ℝ] ℝ)
    (steps : List (GaussianStep ι)) (v : Fin steps.length → ι → ℝ)
    (x : ι → ℝ) (p : Fin steps.length → (ι → ℝ)) : ℝ :=
  forwardScore steps.length (hierarchyIncrements steps) (hierarchyScores w φ steps v) x p

 

theorem hierarchyPathScore_hasSubgaussianMGF {n : ℕ} {w : S → ℝ} (hw : ∀ s, 0 < w s)
    (φ : S → (Fin (n+1) → ℝ) →L[ℝ] ℝ) (steps : List (GaussianStep (Fin (n+1))))
    {a : ℝ} (ha : OrderedSteps a steps) (v : Fin steps.length → Fin (n+1) → ℝ)
    (x : Fin (n+1) → ℝ) :
    HasSubgaussianMGF (hierarchyPathScore w φ steps v x)
      (∑ i, ⟨∑ j, (v i j)^2, Finset.sum_nonneg (fun j _ => sq_nonneg (v i j))⟩)
      (forwardLaw steps.length (fun _ => standardDrivers (Fin (n+1)))
        (hierarchyIncrements steps) (hierarchyTransitions w φ steps) x) :=
  forwardScore_hasSubgaussianMGF steps.length _ (hierarchyIncrements_measurable steps)
    (hierarchyTransitions_measurable hw φ steps ha) (hierarchyScores_measurable hw φ steps ha v)
    _ (hierarchyScores_hasSubgaussianMGF hw φ steps ha v) x

end SKFluctuations.Hierarchy

 

 

namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal BigOperators
variable {E D : Type*} [AddCommMonoid E] [MeasurableSpace E]
  [MeasurableAdd₂ E] [MeasurableSpace D]

noncomputable def forwardKernel (n : ℕ) (μ : Fin n → Measure D)
    [∀ i, IsProbabilityMeasure (μ i)]
    (inc : Fin n → D → E) (T : Fin n → E → D → ℝ≥0∞) : Kernel E (Fin n → D) :=
  (Kernel.const E (Measure.pi μ)).withDensity (forwardWeight n inc T)

theorem forwardKernel_apply (n : ℕ) (μ : Fin n → Measure D)
    [∀ i, IsProbabilityMeasure (μ i)] {inc : Fin n → D → E} {T : Fin n → E → D → ℝ≥0∞}
    (hinc : ∀ i, Measurable (inc i)) (hT : ∀ i, Measurable (Function.uncurry (T i)))
    (x : E) : forwardKernel n μ inc T x = forwardLaw n μ inc T x := by
  rw [forwardKernel,Kernel.withDensity_apply _ (measurable_forwardWeight n hinc hT)]
  rfl

theorem forwardKernel_isMarkov (n : ℕ) (μ : Fin n → Measure D)
    [∀ i, IsProbabilityMeasure (μ i)] {inc : Fin n → D → E} {T : Fin n → E → D → ℝ≥0∞}
    (hinc : ∀ i, Measurable (inc i)) (hT : ∀ i, Measurable (Function.uncurry (T i)))
    (h1 : ∀ i x, ∫⁻ z, T i x z ∂μ i = 1) : IsMarkovKernel (forwardKernel n μ inc T) := by
  refine ⟨fun x => ?_⟩
  rw [forwardKernel_apply n μ hinc hT]
  exact forwardLaw_isProbability n μ hinc hT h1 x

theorem measurable_finCons {n : ℕ} :
    Measurable (fun zp : D × (Fin n → D) => (Fin.cons zp.1 zp.2 : Fin (n+1) → D)) := by
  apply Measurable.of_eval
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · exact measurable_fst
  · exact (measurable_pi_apply j).comp measurable_snd

noncomputable def forwardTailKernel {n : ℕ} (μ : Fin (n+1) → Measure D)
    [∀ i, IsProbabilityMeasure (μ i)]
    (inc : Fin (n+1) → D → E) (T : Fin (n+1) → E → D → ℝ≥0∞)
    (hinc : ∀ i, Measurable (inc i)) (x : E) : Kernel D (Fin n → D) :=
  (forwardKernel n (fun i => μ i.succ) (fun i => inc i.succ) (fun i => T i.succ)).comap
    (fun z => x+inc 0 z) (measurable_const.add (hinc 0))

theorem forwardLaw_cons {n : ℕ} (μ : Fin (n+1) → Measure D)
    [∀ i, IsProbabilityMeasure (μ i)] {inc : Fin (n+1) → D → E} {T : Fin (n+1) → E → D → ℝ≥0∞}
    (hinc : ∀ i, Measurable (inc i)) (hT : ∀ i, Measurable (Function.uncurry (T i)))
    (h1 : ∀ i x, ∫⁻ z, T i x z ∂μ i = 1) (x : E) :
    forwardLaw (n+1) μ inc T x =
      (((μ 0).withDensity (T 0 x)).compProd (forwardTailKernel μ inc T hinc x)).map
        (fun zp : D × (Fin n → D) => Fin.cons zp.1 zp.2) := by
  let :=  forwardKernel_isMarkov n (fun i => μ i.succ) (fun i => hinc i.succ)
    (fun i => hT i.succ) (fun i => h1 i.succ)
  have : IsMarkovKernel (forwardTailKernel μ inc T hinc x) := by
    dsimp only [forwardTailKernel]; infer_instance
  have : IsProbabilityMeasure ((μ 0).withDensity (T 0 x)) := by
    refine ⟨?_⟩
    simpa only [withDensity_apply _ MeasurableSet.univ,Measure.restrict_univ] using h1 0 x
  have hw : Measurable (forwardWeight (n+1) inc T x) :=
    (measurable_forwardWeight _ hinc hT).comp (measurable_const.prodMk measurable_id)
  have ht : Measurable (T 0 x) := (hT 0).comp (measurable_const.prodMk measurable_id)
  apply Measure.ext_of_lintegral
  intro f hf
  rw [forwardLaw,lintegral_withDensity_eq_lintegral_mul _ hw hf,
    lintegral_map hf measurable_finCons,
    Measure.lintegral_compProd (show Measurable (fun zp : D × (Fin n → D) => f (Fin.cons zp.1 zp.2)) from hf.comp measurable_finCons)]
  rw [lintegral_fin_cons μ (hw.mul hf)]
  simp only [Pi.mul_apply]
  have houter : Measurable (fun z => ∫⁻ p, f (Fin.cons z p)
      ∂forwardTailKernel μ inc T hinc x z) :=
    (show Measurable (Function.uncurry (fun z p => f (Fin.cons z p))) from hf.comp measurable_finCons).lintegral_kernel_prod_right
  rw [lintegral_withDensity_eq_lintegral_mul _ ht houter]
  apply lintegral_congr
  intro z
  have hwm : Measurable (forwardWeight n (fun i => inc i.succ) (fun i => T i.succ)
      (x+inc 0 z)) := (measurable_forwardWeight n (fun i => hinc i.succ) (fun i => hT i.succ)).comp
        (measurable_const.prodMk measurable_id)
  have hfm : Measurable (fun p : Fin n → D => f (Fin.cons z p)) :=
    (hf.comp measurable_finCons).comp (measurable_const.prodMk measurable_id)
  simp only [forwardTailKernel,Kernel.comap_apply,forwardKernel_apply n _
    (fun i => hinc i.succ) (fun i => hT i.succ),forwardLaw]
  simp only [Pi.mul_apply]
  rw [lintegral_withDensity_eq_lintegral_mul _ hwm hfm]
  simp only [forwardWeight,Fin.cons_zero,Fin.tail_cons,mul_assoc]
  have heq := lintegral_const_mul (T 0 x z) (hwm.mul hfm)
    (μ := Measure.pi (fun i => μ i.succ))
  simpa only [Pi.mul_apply] using heq

theorem integral_forwardLaw_cons {n : ℕ} (μ : Fin (n+1) → Measure D)
    [∀ i, IsProbabilityMeasure (μ i)] {inc : Fin (n+1) → D → E} {T : Fin (n+1) → E → D → ℝ≥0∞}
    (hinc : ∀ i, Measurable (inc i)) (hT : ∀ i, Measurable (Function.uncurry (T i)))
    (h1 : ∀ i x, ∫⁻ z, T i x z ∂μ i = 1) (x : E) {f : (Fin (n+1) → D) → ℝ}
    (hf : Integrable f (forwardLaw (n+1) μ inc T x)) :
    (∫ p, f p ∂forwardLaw (n+1) μ inc T x) =
      ∫ z, ∫ p, f (Fin.cons z p)
        ∂forwardLaw n (fun i => μ i.succ) (fun i => inc i.succ) (fun i => T i.succ) (x+inc 0 z)
        ∂(μ 0).withDensity (T 0 x) := by
  let :=  forwardKernel_isMarkov n (fun i => μ i.succ) (fun i => hinc i.succ)
    (fun i => hT i.succ) (fun i => h1 i.succ)
  have : IsMarkovKernel (forwardTailKernel μ inc T hinc x) := by
    dsimp only [forwardTailKernel]; infer_instance
  have : IsProbabilityMeasure ((μ 0).withDensity (T 0 x)) := by
    refine ⟨?_⟩
    simpa only [withDensity_apply _ MeasurableSet.univ,Measure.restrict_univ] using h1 0 x
  rw [forwardLaw_cons μ hinc hT h1 x] at hf ⊢
  rw [integral_map measurable_finCons.aemeasurable hf.aestronglyMeasurable,
    Measure.integral_compProd (show Integrable (fun zp : D × (Fin n → D) => f (Fin.cons zp.1 zp.2)) _ from hf.comp_measurable measurable_finCons)]
  apply integral_congr_ae
  filter_upwards [] with z
  simp only [forwardTailKernel,Kernel.comap_apply,forwardKernel_apply n _
    (fun i => hinc i.succ) (fun i => hT i.succ)]

end SKFluctuations.Hierarchy

 

 

namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

noncomputable def subgaussianMomentConstant (k : ℕ) : ℝ :=
  2*((2*(k+1)).factorial : ℝ)*Real.exp (1/2)

theorem abs_pow_le_two_exp (x : ℝ) (p : ℕ) :
    |x|^p ≤ (p.factorial : ℝ)*(Real.exp x+Real.exp (-x)) := by
  have h := Real.pow_div_factorial_le_exp |x| (abs_nonneg x) p
  have hf : (0:ℝ) < p.factorial := by exact_mod_cast Nat.factorial_pos p
  have h₀ : |x|^p ≤ (p.factorial : ℝ)*Real.exp |x| := by
    have hh := (div_le_iff₀ hf).mp h
    simpa only [mul_comm] using hh
  apply h₀.trans
  apply mul_le_mul_of_nonneg_left _ hf.le
  rcases le_total 0 x with hx | hx
  · rw [abs_of_nonneg hx]
    exact le_add_of_nonneg_right (Real.exp_nonneg _)
  · rw [abs_of_nonpos hx]
    exact le_add_of_nonneg_left (Real.exp_nonneg _)

theorem subgaussian_integrable_abs_natPow {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} {X : Ω → ℝ} {c : ℝ≥0} (hX : ProbabilityTheory.HasSubgaussianMGF X c μ)
    (p : ℕ) : Integrable (fun ω => |X ω|^p) μ := by
  have hi := ((hX.integrable_exp_mul 1).add (hX.integrable_exp_mul (-1))).const_mul
    (p.factorial : ℝ)
  apply hi.mono' (hX.integrable.aestronglyMeasurable.norm.pow p)
  filter_upwards [] with ω
  simpa only [Real.norm_eq_abs,Pi.pow_apply,abs_pow,abs_abs,
    one_mul,neg_one_mul,Pi.add_apply] using abs_pow_le_two_exp (X ω) p

theorem subgaussian_abs_natPow_le {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} {X : Ω → ℝ} {c : ℝ≥0} (hX : ProbabilityTheory.HasSubgaussianMGF X c μ)
    (p : ℕ) :
    (∫ ω, |X ω|^p ∂μ) ≤ 2*(p.factorial : ℝ)*Real.exp (c/2) := by
  have hi (t : ℝ) := hX.integrable_exp_mul t
  have hh := integral_mono (subgaussian_integrable_abs_natPow hX p)
    (((hi 1).add (hi (-1))).const_mul (p.factorial : ℝ)) (fun ω => by
      simpa only [one_mul,neg_one_mul,Pi.add_apply] using abs_pow_le_two_exp (X ω) p)
  simp only [Pi.add_apply,integral_const_mul,integral_add (hi 1) (hi (-1))] at hh
  have hpos := hX.mgf_le 1
  have hneg := hX.mgf_le (-1)
  simp only [mgf,one_pow,mul_one,neg_one_sq] at hpos hneg
  calc
    _ ≤ (p.factorial : ℝ)*((∫ ω, Real.exp (1*X ω) ∂μ)+(∫ ω, Real.exp (-1*X ω) ∂μ)) := hh
    _ ≤ (p.factorial : ℝ)*(Real.exp (c/2)+Real.exp (c/2)) := by gcongr
    _ = _ := by ring

 

theorem subgaussian_even_moment_le {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} {X : Ω → ℝ} {c : ℝ≥0} (hX : ProbabilityTheory.HasSubgaussianMGF X c μ)
    (k : ℕ) :
    (∫ ω, |X ω|^(2*(k+1)) ∂μ) ≤ subgaussianMomentConstant k*(c:ℝ)^(k+1) := by
  by_cases hc : c = 0
  · subst c
    have hz := hX.ae_eq_zero_of_hasSubgaussianMGF_zero
    rw [show (∫ ω, |X ω|^(2*(k+1)) ∂μ) = 0 by
      apply integral_eq_zero_of_ae
      filter_upwards [hz] with ω hω
      simp [hω]]
    simp
  have hc' : (0:ℝ) < c := NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr hc)
  let r := (Real.sqrt (c:ℝ))⁻¹
  have hr : 0 < r := inv_pos.mpr (Real.sqrt_pos.mpr hc')
  have hrc : r^2*(c:ℝ) = 1 := by
    dsimp only [r]
    rw [inv_pow,Real.sq_sqrt hc'.le,inv_mul_cancel₀ hc'.ne']
  have hZ : ProbabilityTheory.HasSubgaussianMGF (fun ω => r*X ω) 1 μ := by
    convert hX.const_mul r using 1
    apply NNReal.coe_injective
    exact hrc.symm
  have hb := subgaussian_abs_natPow_le hZ (2*(k+1))
  have he (ω : Ω) : |r*X ω|^(2*(k+1)) = (r^2)^(k+1)*|X ω|^(2*(k+1)) := by
    rw [abs_mul,abs_of_pos hr,mul_pow,pow_mul]
  simp_rw [he] at hb
  rw [integral_const_mul] at hb
  have hm := mul_le_mul_of_nonneg_left hb (pow_nonneg hc'.le (k+1))
  have hcancel : (c:ℝ)^(k+1)*(r^2)^(k+1) = 1 := by
    rw [← mul_pow,mul_comm (c:ℝ),hrc,one_pow]
  rw [← mul_assoc,hcancel,one_mul] at hm
  simpa only [subgaussianMomentConstant,NNReal.coe_one,mul_comm ((c:ℝ)^(k+1))] using hm

end SKFluctuations.Hierarchy

 

 

namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set GaussianCalculus
open scoped Topology NNReal ENNReal BigOperators
variable {ι S : Type*} [Fintype ι] [Fintype S] [Nonempty S]

omit [Fintype ι] in
theorem orderedSteps_append_right (pre tail : List (GaussianStep ι))
    {a : ℝ} (ha : OrderedSteps a (pre++tail)) : ∃ b, OrderedSteps b tail := by
  induction pre generalizing a with
  | nil => exact ⟨a,ha⟩
  | cons step rest ih => exact ih ha.2.2.2

noncomputable def segmentTransitions (w : S → ℝ) (φ : S → (ι → ℝ) →L[ℝ] ℝ)
    (tail : List (GaussianStep ι)) :
    (pre : List (GaussianStep ι)) → Fin pre.length → (ι → ℝ) → (ι → ℝ) → ℝ≥0∞
  | [] => fun i => Fin.elim0 i
  | (m,q)::rest => Fin.cons
      (hierarchyTransitions w φ ((m,q)::(rest++tail)) 0)
      (segmentTransitions w φ tail rest)

noncomputable def segmentScores (w : S → ℝ) (φ : S → (ι → ℝ) →L[ℝ] ℝ)
    (tail : List (GaussianStep ι)) :
    (pre : List (GaussianStep ι)) → (Fin pre.length → ι → ℝ) →
      Fin pre.length → (ι → ℝ) → (ι → ℝ) → ℝ
  | [], _ => fun i => Fin.elim0 i
  | (m,q)::rest, v => Fin.cons
      (fun x z => hierarchyAffineScore w φ (scaleDriver q) (rest++tail) x m (v 0) z)
      (segmentScores w φ tail rest (Fin.tail v))

theorem segmentTransitions_measurable {w : S → ℝ} (hw : ∀ s, 0 < w s)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) (tail pre : List (GaussianStep ι))
    {a : ℝ} (ha : OrderedSteps a (pre++tail)) :
    ∀ i, Measurable (Function.uncurry (segmentTransitions w φ tail pre i)) := by
  induction pre generalizing a with
  | nil => intro i; exact Fin.elim0 i
  | cons step rest ih =>
    rcases step with ⟨m,q⟩
    exact Fin.cases (hierarchyTransitions_measurable hw φ ((m,q)::(rest++tail)) ha 0) (ih ha.2.2.2)

theorem segmentTransitions_normalized {w : S → ℝ} (hw : ∀ s, 0 < w s)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) (tail pre : List (GaussianStep ι))
    {a : ℝ} (ha : OrderedSteps a (pre++tail)) :
    ∀ i x, ∫⁻ z, segmentTransitions w φ tail pre i x z ∂standardDrivers ι = 1 := by
  induction pre generalizing a with
  | nil => intro i; exact Fin.elim0 i
  | cons step rest ih =>
    rcases step with ⟨m,q⟩
    exact Fin.cases (hierarchyTransitions_normalized hw φ ((m,q)::(rest++tail)) ha 0) (ih ha.2.2.2)

theorem segmentScores_measurable {w : S → ℝ} (hw : ∀ s, 0 < w s)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) (tail pre : List (GaussianStep ι))
    {a : ℝ} (ha : OrderedSteps a (pre++tail)) (v : Fin pre.length → ι → ℝ) :
    ∀ i, Measurable (Function.uncurry (segmentScores w φ tail pre v i)) := by
  induction pre generalizing a with
  | nil => intro i; exact Fin.elim0 i
  | cons step rest ih =>
    rcases step with ⟨m,q⟩
    refine Fin.cases ?_ (ih ha.2.2.2 (Fin.tail v))
    have hM := (gaussianHierarchyMean_smooth hw φ
      (fun s => φ s (scaleDriver q (v 0))) (rest++tail) ha.2.2.2 0).1
    have hdot : Measurable (fun xz : (ι → ℝ) × (ι → ℝ) => vectorDot (v 0) xz.2) := by
      apply Finset.measurable_sum Finset.univ
      intro i _
      exact measurable_const.mul ((measurable_pi_apply i).comp measurable_snd)
    exact hdot.sub
      ((hM.comp (continuous_fst.add ((scaleDriver q).continuous.comp continuous_snd))).measurable.const_mul m)

noncomputable def segmentLaw (w : S → ℝ) (φ : S → (ι → ℝ) →L[ℝ] ℝ)
    (tail pre : List (GaussianStep ι)) (x : ι → ℝ) :
    Measure (Fin pre.length → (ι → ℝ)) :=
  forwardLaw pre.length (fun _ => standardDrivers ι) (hierarchyIncrements pre)
    (segmentTransitions w φ tail pre) x

theorem segmentLaw_isProbability {w : S → ℝ} (hw : ∀ s, 0 < w s)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) (tail pre : List (GaussianStep ι))
    {a : ℝ} (ha : OrderedSteps a (pre++tail)) (x : ι → ℝ) :
    IsProbabilityMeasure (segmentLaw w φ tail pre x) :=
  forwardLaw_isProbability _ _ (hierarchyIncrements_measurable pre)
    (segmentTransitions_measurable hw φ tail pre ha)
    (segmentTransitions_normalized hw φ tail pre ha) x

noncomputable def segmentPathScore (w : S → ℝ) (φ : S → (ι → ℝ) →L[ℝ] ℝ)
    (tail pre : List (GaussianStep ι)) (v : Fin pre.length → ι → ℝ)
    (x : ι → ℝ) (p : Fin pre.length → (ι → ℝ)) : ℝ :=
  forwardScore pre.length (hierarchyIncrements pre) (segmentScores w φ tail pre v) x p

theorem segmentScores_hasSubgaussianMGF {n : ℕ} {w : S → ℝ} (hw : ∀ s, 0 < w s)
    (φ : S → (Fin (n+1) → ℝ) →L[ℝ] ℝ) (tail pre : List (GaussianStep (Fin (n+1))))
    {a : ℝ} (ha : OrderedSteps a (pre++tail)) (v : Fin pre.length → Fin (n+1) → ℝ) :
    ∀ i x, HasSubgaussianMGF (segmentScores w φ tail pre v i x)
      ⟨∑ j, (v i j)^2, Finset.sum_nonneg (fun j _ => sq_nonneg (v i j))⟩
      ((standardDrivers (Fin (n+1))).withDensity (segmentTransitions w φ tail pre i x)) := by
  induction pre generalizing a with
  | nil => intro i; exact Fin.elim0 i
  | cons step rest ih =>
    rcases step with ⟨m,q⟩
    refine Fin.cases ?_ (ih ha.2.2.2 (Fin.tail v))
    intro x
    change HasSubgaussianMGF (hierarchyAffineScore w φ (scaleDriver q) (rest++tail) x m (v 0)) _
      ((standardDrivers (Fin (n+1))).withDensity (hierarchyTransitions w φ ((m,q)::(rest++tail)) 0 x))
    rw [scaledTransitionLaw_eq hw φ (rest++tail) ha.2.2.2 ha.2.2.1.ne' q x]
    exact hierarchyAffineScore_hasSubgaussianMGF hw φ (scaleDriver q) _ ha.2.2.2 x ha.2.2.1.le (v 0)

theorem segmentPathScore_hasSubgaussianMGF {n : ℕ} {w : S → ℝ} (hw : ∀ s, 0 < w s)
    (φ : S → (Fin (n+1) → ℝ) →L[ℝ] ℝ) (tail pre : List (GaussianStep (Fin (n+1))))
    {a : ℝ} (ha : OrderedSteps a (pre++tail)) (v : Fin pre.length → Fin (n+1) → ℝ)
    (x : Fin (n+1) → ℝ) :
    HasSubgaussianMGF (segmentPathScore w φ tail pre v x)
      (∑ i, ⟨∑ j, (v i j)^2, Finset.sum_nonneg (fun j _ => sq_nonneg (v i j))⟩)
      (segmentLaw w φ tail pre x) :=
  forwardScore_hasSubgaussianMGF _ _ (hierarchyIncrements_measurable pre)
    (segmentTransitions_measurable hw φ tail pre ha) (segmentScores_measurable hw φ tail pre ha v)
    _ (segmentScores_hasSubgaussianMGF hw φ tail pre ha v) x

theorem segmentPathScore_even_moment {n : ℕ} {w : S → ℝ} (hw : ∀ s, 0 < w s)
    (φ : S → (Fin (n+1) → ℝ) →L[ℝ] ℝ) (tail pre : List (GaussianStep (Fin (n+1))))
    {a : ℝ} (ha : OrderedSteps a (pre++tail)) (v : Fin pre.length → Fin (n+1) → ℝ)
    (x : Fin (n+1) → ℝ) (k : ℕ) :
    (∫ p, |segmentPathScore w φ tail pre v x p|^(2*(k+1)) ∂segmentLaw w φ tail pre x) ≤
      subgaussianMomentConstant k*(∑ i, ∑ j, (v i j)^2)^(k+1) := by
  have hh := subgaussian_even_moment_le
    (segmentPathScore_hasSubgaussianMGF hw φ tail pre ha v x) k
  have he := NNReal.coe_sum Finset.univ
    (fun i : Fin pre.length => (⟨∑ j, (v i j)^2, Finset.sum_nonneg (fun j _ => sq_nonneg (v i j))⟩ : ℝ≥0))
  exact hh.trans_eq (congrArg (fun c : ℝ => subgaussianMomentConstant k*c^(k+1)) he)

theorem integral_scaledTransition_mean {w : S → ℝ} (hw : ∀ s, 0 < w s)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) (A : S → ℝ) (steps : List (GaussianStep ι))
    {a m : ℝ} (ha : OrderedSteps a steps) (hm : m ≠ 0) (q : ι → ℝ≥0) (x : ι → ℝ) :
    (∫ z, gaussianHierarchyMean w φ A steps (x+scaleDriver q z)
      ∂(standardDrivers ι).withDensity (hierarchyTransitions w φ ((m,q)::steps) 0 x)) =
      gaussianHierarchyMean w φ A ((m,q)::steps) x := by
  have hF : Continuous (fun z => gaussianHierarchy w φ steps (x+z)) := (gaussianHierarchy_continuous hw φ steps ha).comp (continuous_const.add continuous_id)
  have hA : Continuous (fun z => gaussianHierarchyMean w φ A steps (x+z)) := (gaussianHierarchyMean_smooth hw φ A steps ha 0).1.comp (continuous_const.add continuous_id)
  have he : (∫ z, Real.exp (m*gaussianHierarchy w φ steps (x+scaleDriver q z)) ∂standardDrivers ι) =
      ∫ z, Real.exp (m*gaussianHierarchy w φ steps (x+z)) ∂Measure.pi (fun i => gaussianReal 0 (q i)) := by
    rw [← (scaleDriver_gaussian q).map_eq]
    exact (integral_map (scaleDriver q).measurable.aemeasurable
      (hF.const_mul m |>.rexp |>.aestronglyMeasurable)).symm
  have hn : (∫ z, gaussianHierarchyMean w φ A steps (x+scaleDriver q z)*
      Real.exp (m*gaussianHierarchy w φ steps (x+scaleDriver q z)) ∂standardDrivers ι) =
      ∫ z, gaussianHierarchyMean w φ A steps (x+z)*Real.exp (m*gaussianHierarchy w φ steps (x+z))
        ∂Measure.pi (fun i => gaussianReal 0 (q i)) := by
    rw [← (scaleDriver_gaussian q).map_eq]
    exact (integral_map (scaleDriver q).measurable.aemeasurable
      (hA.mul (hF.const_mul m |>.rexp) |>.aestronglyMeasurable)).symm
  obtain ⟨C,hL⟩ := gaussianHierarchy_lipschitz hw φ steps ha
  have hshift : LipschitzWith _ (fun z => gaussianHierarchy w φ steps (x+scaleDriver q z)) :=
    hL.comp ((isometry_add_left x).lipschitzWith.comp (scaleDriver q).lipschitzWith)
  rw [scaledTransitionLaw_eq hw φ steps ha hm]
  have hi : Integrable (fun z => Real.exp (m*gaussianHierarchy w φ steps (x+scaleDriver q z)))
      (standardDrivers ι) := (ExpNormBounded.exp_lipschitz hshift m).integrable (fun _ => 1)
  rw [integral_tiltedLaw hshift.continuous.measurable hi]
  simp only [gaussianHierarchyMean,shiftedMean,tiltedMean,he,hn]

end SKFluctuations.Hierarchy

namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal BigOperators
variable {ι S : Type*} [Fintype ι] [Fintype S] [Nonempty S]

theorem BddSmooth.integrable_comp_measurable {E Ω : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
    [MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ] {A : E → ℝ}
    {r : ℕ} (hA : BddSmooth r A) {f : Ω → E} (hf : Measurable f) :
    Integrable (fun ω => A (f ω)) μ := by
  obtain ⟨B,_,hB⟩ := hA.bound
  exact memLp_one_iff_integrable.mp
    (MemLp.of_bound ((hA.continuous.measurable.comp hf).aestronglyMeasurable) B
      (ae_of_all _ (fun ω => hB (f ω))))

theorem integral_segmentLaw_cons {w : S → ℝ} (hw : ∀ s, 0 < w s)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) (tail rest : List (GaussianStep ι))
    {a m : ℝ} (q : ι → ℝ≥0) (ha : OrderedSteps a (((m,q)::rest)++tail)) (x : ι → ℝ)
    {f : (Fin (((m,q)::rest).length) → (ι → ℝ)) → ℝ}
    (hf : Integrable f (segmentLaw w φ tail ((m,q)::rest) x)) :
    (∫ p, f p ∂segmentLaw w φ tail ((m,q)::rest) x) =
      ∫ z, ∫ p, f (Fin.cons z p) ∂segmentLaw w φ tail rest (x+scaleDriver q z)
        ∂(standardDrivers ι).withDensity (hierarchyTransitions w φ ((m,q)::(rest++tail)) 0 x) := by
  simpa only [segmentLaw,List.length_cons,hierarchyIncrements,segmentTransitions,Fin.cons_zero,Fin.cons_succ] using
    integral_forwardLaw_cons (fun _ => standardDrivers ι)
      (hierarchyIncrements_measurable ((m,q)::rest))
      (segmentTransitions_measurable hw φ tail ((m,q)::rest) ha)
      (segmentTransitions_normalized hw φ tail ((m,q)::rest) ha) x hf

 
theorem integral_segmentLaw_mean {w : S → ℝ} (hw : ∀ s, 0 < w s)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) (A : S → ℝ) (tail pre : List (GaussianStep ι))
    {a : ℝ} (ha : OrderedSteps a (pre++tail)) (x : ι → ℝ) :
    (∫ p, gaussianHierarchyMean w φ A tail
      (forwardEnd pre.length (hierarchyIncrements pre) x p) ∂segmentLaw w φ tail pre x) =
      gaussianHierarchyMean w φ A (pre++tail) x := by
  induction pre generalizing a x with
  | nil =>
    have := segmentLaw_isProbability hw φ tail [] ha x
    simp [forwardEnd]
  | cons step rest ih =>
    rcases step with ⟨m,q⟩
    have := segmentLaw_isProbability hw φ tail ((m,q)::rest) ha x
    obtain ⟨b,hb⟩ := orderedSteps_append_right ((m,q)::rest) tail ha
    have hf := (gaussianHierarchyMean_smooth hw φ A tail hb 0).integrable_comp_measurable
      (f := forwardEnd (((m,q)::rest).length) (hierarchyIncrements ((m,q)::rest)) x)
      ((measurable_forwardEnd _ (hierarchyIncrements_measurable ((m,q)::rest))).comp
        (measurable_const.prodMk measurable_id)) (μ := segmentLaw w φ tail ((m,q)::rest) x)
    rw [integral_segmentLaw_cons hw φ tail rest q ha x hf]
    simp only [List.length_cons,forwardEnd,hierarchyIncrements,Fin.cons_zero,Fin.cons_succ,Fin.tail_cons]
    simp_rw [ih ha.2.2.2]
    exact integral_scaledTransition_mean hw φ A (rest++tail) ha.2.2.2 ha.2.2.1.ne' q x

end SKFluctuations.Hierarchy

 

 
namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set GaussianCalculus
open scoped Topology NNReal BigOperators

theorem polynomial_young_split {x y ε : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y)
    (hε : 0 < ε) (q : ℕ) :
    x^q*y ≤ ε*x^(q+1)+(ε⁻¹)^q*y^(q+1) := by
  by_cases h : y ≤ ε*x
  · have hh := mul_le_mul_of_nonneg_left h (pow_nonneg hx q)
    have he : x^q*(ε*x) = ε*x^(q+1) := by rw [pow_succ]; ring
    rw [he] at hh
    exact hh.trans (le_add_of_nonneg_right (by positivity))
  · have hx' : x ≤ ε⁻¹*y := by
      rw [← div_eq_inv_mul]
      exact (le_div_iff₀ hε).mpr (by nlinarith)
    have hh := mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hx hx' q) hy
    have he : (ε⁻¹*y)^q*y = (ε⁻¹)^q*y^(q+1) := by rw [mul_pow,pow_succ]; ring
    rw [he] at hh
    exact hh.trans (le_add_of_nonneg_left (by positivity))

theorem weighted_odd_score_young {S : Type*} [Fintype S]
    (p Y : S → ℝ) (hp : ∀ s, 0 ≤ p s) (h1 : ∑ s, p s = 1)
    (c z : ℝ) {ε : ℝ} (hε : 0 < ε) (q : ℕ) :
    (∑ s, p s*(Y s-c)^q)*z ≤
      ε*(∑ s, p s*|Y s-c|^(q+1))+(ε⁻¹)^q*|z|^(q+1) := by
  have hh (s : S) : (Y s-c)^q*z ≤ ε*|Y s-c|^(q+1)+(ε⁻¹)^q*|z|^(q+1) := by
    calc
      _ ≤ |(Y s-c)^q*z| := le_abs_self _
      _ = |Y s-c|^q*|z| := by rw [abs_mul,abs_pow]
      _ ≤ _ := polynomial_young_split (abs_nonneg _) (abs_nonneg _) hε q
  calc
    _ = ∑ s, p s*((Y s-c)^q*z) := by rw [Finset.sum_mul]; apply Finset.sum_congr rfl; intro s _; ring
    _ ≤ ∑ s, p s*(ε*|Y s-c|^(q+1)+(ε⁻¹)^q*|z|^(q+1)) :=
      Finset.sum_le_sum (fun s _ => mul_le_mul_of_nonneg_left (hh s) (hp s))
    _ = _ := by
      simp_rw [mul_add,Finset.sum_add_distrib,
        show ∀ s, p s*(ε*|Y s-c|^(q+1)) = ε*(p s*|Y s-c|^(q+1)) by intro; ring]
      rw [← Finset.mul_sum,← Finset.sum_mul,h1,one_mul]

theorem BddSmooth.natPow {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : E → ℝ} {r : ℕ} (hf : BddSmooth r f) (k : ℕ) : BddSmooth r (fun x => f x^k) :=
  hf.comp_contDiff (contDiff_id.pow k)

theorem BddSmooth.abs_natPow_zero {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : E → ℝ} (hf : BddSmooth 0 f) (k : ℕ) : BddSmooth 0 (fun x => |f x|^k) := by
  simpa only [Real.rpow_natCast] using hf.abs_rpow_zero (p := (k:ℝ)) (Nat.cast_nonneg k)

variable {ι S : Type*} [Fintype ι] [Fintype S] [Nonempty S]

noncomputable def hierarchyCenteredEvenMoment (w : S → ℝ)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) (Y : S → ℝ) (steps : List (GaussianStep ι))
    (k : ℕ) (x : ι → ℝ) : ℝ :=
  ∑ s, hierarchyAtom w φ steps s x*|Y s-gaussianHierarchyMean w φ Y steps x|^(2*k+2)

theorem hierarchyCenteredEvenMoment_smooth_zero {w : S → ℝ} (hw : ∀ s, 0 < w s)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) (Y : S → ℝ) (steps : List (GaussianStep ι))
    {a : ℝ} (ha : OrderedSteps a steps) (k : ℕ) :
    BddSmooth 0 (hierarchyCenteredEvenMoment w φ Y steps k) :=
  BddSmooth.sum Finset.univ fun s _ => (hierarchyAtom_smooth hw φ steps ha s 0).mul
    (((BddSmooth.const 0 (Y s)).sub (gaussianHierarchyMean_smooth hw φ Y steps ha 0)).abs_natPow_zero _)

 

theorem hierarchy_projection_one_step {n : ℕ}
    {w : S → ℝ} (hw : ∀ s, 0 < w s) (φ : S → (ι → ℝ) →L[ℝ] ℝ)
    (L : (Fin (n+1) → ℝ) →L[ℝ] (ι → ℝ)) (steps : List (GaussianStep ι))
    {a : ℝ} (ha : OrderedSteps a steps) (x : ι → ℝ) {m : ℝ} (hm : 0 ≤ m)
    (v : Fin (n+1) → ℝ) (c : ℝ) {ε : ℝ} (hε : 0 < ε) (k : ℕ) :
    let μ := tiltedLaw (Measure.pi fun _ : Fin (n+1) => gaussianReal 0 1) m
      (fun z => gaussianHierarchy w φ steps (x+L z))
    a*(∫ z, hierarchyCenteredEvenMoment w φ (fun s => φ s (L v)) steps k (x+L z) ∂μ) ≤
      (2:ℝ)^(2*k)*ε*(∫ z, gaussianHierarchyMean w φ
        (fun s => |φ s (L v)-c|^(2*k+2)) steps (x+L z) ∂μ) +
      (2:ℝ)^(2*k)*(ε⁻¹)^(2*k+1)*gaussianEvenConstant (k+1)*(∑ i, v i^2)^(k+1) := by
  dsimp only
  let F := fun z => gaussianHierarchy w φ steps (x+L z)
  let μ := tiltedLaw (Measure.pi fun _ : Fin (n+1) => gaussianReal 0 1) m F
  let Y := fun s => φ s (L v)
  let A := fun z => gaussianHierarchyMean w φ (fun s => (Y s-c)^(2*k+1)) steps (x+L z)
  let B := fun z => gaussianHierarchyMean w φ (fun s => |Y s-c|^(2*k+2)) steps (x+L z)
  let R := fun z => gaussianHierarchyResponse w φ (fun s => (Y s-c)^(2*k+1)) (L v) steps (x+L z)
  let E := fun z => hierarchyCenteredEvenMoment w φ Y steps k (x+L z)
  let Z := hierarchyAffineScore w φ L steps x m v
  obtain ⟨C,hF₀⟩ := gaussianHierarchy_lipschitz hw φ steps ha
  have hF : LipschitzWith _ F := hF₀.comp ((isometry_add_left x).lipschitzWith.comp L.lipschitzWith)
  have hi := (ExpNormBounded.exp_lipschitz hF m).integrable (fun _ => 1)
  have hA : ExpNormBounded A := ExpNormBounded.bddSmooth
    ((gaussianHierarchyMean_smooth hw φ _ steps ha 0).affine L x)
  have hB : ExpNormBounded B := ExpNormBounded.bddSmooth
    ((gaussianHierarchyMean_smooth hw φ _ steps ha 0).affine L x)
  have hR : ExpNormBounded R := ExpNormBounded.bddSmooth
    ((gaussianHierarchyResponse_smooth hw φ _ (L v) steps ha 0).affine L x)
  have hE : ExpNormBounded E := ExpNormBounded.bddSmooth
    ((hierarchyCenteredEvenMoment_smooth_zero hw φ Y steps ha k).affine L x)
  have hZ : ExpNormBounded Z := by
    rw [show Z = gaussianVectorScore m
      (fun i z => gaussianHierarchyMean w φ (fun s => φ s (L (Pi.single i 1))) steps (x+L z)) v from
      hierarchyAffineScore_eq hw φ L steps ha x m v]
    exact gaussianVectorScore_expBounded m
      (fun i => (gaussianHierarchyMean_smooth hw φ _ steps ha 0).affine L x) v
  have hz (z : Fin (n+1) → ℝ) : |Z z|^(2*k+2) = Z z^(2*(k+1)) := by
    rw [show 2*k+2 = 2*(k+1) by omega,pow_mul,pow_mul,sq_abs]
  have hZp : Integrable (fun z => Z z^(2*(k+1))) μ :=
    (hZ.pow _).integrable_tiltedLaw hF (fun _ => 1) m
  have hYoung : (∫ z, A z*Z z ∂μ) ≤
      ε*(∫ z, B z ∂μ) + (ε⁻¹)^(2*k+1)*(∫ z, Z z^(2*(k+1)) ∂μ) := by
    rw [← integral_const_mul,← integral_const_mul,← integral_add
      ((hB.integrable_tiltedLaw hF (fun _ => 1) m).const_mul ε)
      (hZp.const_mul _)]
    apply integral_mono ((hA.mul hZ).integrable_tiltedLaw hF (fun _ => 1) m)
      (((hB.integrable_tiltedLaw hF (fun _ => 1) m).const_mul ε).add (hZp.const_mul _))
    intro z
    have hh := weighted_odd_score_young (fun s => hierarchyAtom w φ steps s (x+L z)) Y
      (fun s => hierarchyAtom_nonneg hw φ steps ha s (x+L z))
      (hierarchyAtom_sum hw φ steps ha (x+L z)) c (Z z) hε (2*k+1)
    simpa only [A,B,Pi.add_apply,gaussianHierarchyMean_atoms hw φ steps ha,hz,
      show 2*k+1+1 = 2*k+2 by omega,mul_comm (hierarchyAtom w φ steps _ _)] using hh
  have hIBP : (∫ z, A z*Z z ∂μ) = ∫ z, R z ∂μ := by
    simp only [μ,integral_tiltedLaw hF.continuous.measurable hi]
    exact tiltedMean_hierarchyAffineScore hw φ L steps ha x m _ v
  have hcoer : a*(∫ z, E z ∂μ) ≤ (2:ℝ)^(2*k)*(∫ z, R z ∂μ) := by
    rw [← integral_const_mul,← integral_const_mul]
    exact integral_mono ((hE.integrable_tiltedLaw hF (fun _ => 1) m).const_mul a)
      ((hR.integrable_tiltedLaw hF (fun _ => 1) m).const_mul _)
      (fun z => gaussianHierarchyResponse_odd_coercivity hw φ (L v) c k steps ha (x+L z))
  have hbound : (∫ z, Z z^(2*(k+1)) ∂μ) ≤ gaussianEvenConstant (k+1)*(∑ i, v i^2)^(k+1) := by
    dsimp only [μ]
    rw [integral_tiltedLaw hF.continuous.measurable hi]
    exact hierarchyAffineScore_even_bound hw φ L steps ha x hm v (k+1)
  calc
    _ ≤ (2:ℝ)^(2*k)*(∫ z, R z ∂μ) := hcoer
    _ = (2:ℝ)^(2*k)*(∫ z, A z*Z z ∂μ) := by rw [hIBP]
    _ ≤ (2:ℝ)^(2*k)*(ε*(∫ z, B z ∂μ)+(ε⁻¹)^(2*k+1)*(∫ z, Z z^(2*(k+1)) ∂μ)) :=
      mul_le_mul_of_nonneg_left hYoung (by positivity)
    _ ≤ (2:ℝ)^(2*k)*(ε*(∫ z, B z ∂μ)+(ε⁻¹)^(2*k+1)*
        (gaussianEvenConstant (k+1)*(∑ i, v i^2)^(k+1))) := by
      gcongr
    _ = _ := by dsimp only [B,Y,μ,F]; ring

end SKFluctuations.Hierarchy

end

end OAI
