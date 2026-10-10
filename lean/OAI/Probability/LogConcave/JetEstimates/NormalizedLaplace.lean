import Mathlib
import OAI.Probability.LogConcave.JetEstimates.Bound

namespace OAI

section
section
noncomputable section
open MeasureTheory Filter
open scoped ENNReal NNReal Topology

section UpperProof
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal RealInnerProductSpace Topology

namespace LogConcaveSampling
namespace Appell
open MeasureTheory Filter
open scoped Topology RealInnerProductSpace

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
variable {ι : Type*} [DecidableEq ι]

lemma dir_laplace {μ : Measure E} (hμ : HasExpMoments μ)
    {h : E → ℝ} (hh : Continuous h) (hg : HasGrowth h) (v : E) :
    JetCalculus.dir v (laplace μ h) = laplace μ (fun x => inner ℝ v x*h x) := by
  funext θ
  rw [JetCalculus.dir,(hasFDerivAt_laplace hμ hh hg θ).fderiv]
  rw [laplace,ContinuousLinearMap.integral_apply
    (hμ.integrable_laplace (continuous_inserted hh).aestronglyMeasurable (growth_inserted hg) θ)]
  apply integral_congr_ae
  filter_upwards [] with x
  simp [inserted,real_inner_comm]

lemma jet_laplace {μ : Measure E} (hμ : HasExpMoments μ)
    {h : E → ℝ} (hh : Continuous h) (hg : HasGrowth h)
    (v : ι → E) (l : List ι) (hl : l.Nodup) :
    JetCalculus.jet v l (laplace μ h) =
      laplace μ (fun x => (∏ i ∈ l.toFinset, inner ℝ (v i) x)*h x) := by
  induction l with
  | nil => simp [JetCalculus.jet]
  | cons i l ih =>
    have hi : i ∉ l.toFinset := by simpa using (List.nodup_cons.mp hl).1
    simp only [JetCalculus.jet,ih (List.nodup_cons.mp hl).2]
    have hc : Continuous (fun x => (∏ i ∈ l.toFinset,inner ℝ (v i) x)*h x) :=
      (continuous_finsetProd _ (fun _ _ => continuous_const.inner continuous_id)).mul hh
    have hg' : HasGrowth (fun x => (∏ i ∈ l.toFinset,inner ℝ (v i) x)*h x) :=
      (HasGrowth.prod _ (fun j _ => HasGrowth.linear (innerSL ℝ (v j)))).mul hg
    rw [dir_laplace hμ hc hg']
    congr 1
    funext x
    rw [List.toFinset_cons,Finset.prod_insert hi]
    ring

omit [BorelSpace E] [SecondCountableTopology E] in
lemma laplace_zero {μ : Measure E} (h : E → ℝ) : laplace μ h 0=∫ x,h x ∂μ := by
  simp [laplace]

lemma jet_laplace_zero {μ : Measure E} (hμ : HasExpMoments μ)
    (v : ι → E) (l : List ι) (hl : l.Nodup) :
    JetCalculus.jet v l (laplace μ (fun _ => (1:ℝ))) 0 =
      moments μ (fun i x => inner ℝ (v i) x) l.toFinset := by
  rw [jet_laplace hμ continuous_const (HasGrowth.const _) v l hl,laplace_zero]
  simp [moments]

lemma filter_toFinset_of_subset (l : List ι) (s : Finset ι) (hs : s ⊆ l.toFinset) :
    (l.filter (fun i => i ∈ s)).toFinset=s := by
  ext i
  simp only [List.mem_toFinset,List.mem_filter,decide_eq_true_eq]
  exact ⟨fun h => h.2,fun h => ⟨List.mem_toFinset.mp (hs h),h⟩⟩

lemma filter_not_toFinset (l : List ι) (s : Finset ι) :
    (l.filter (fun i => i ∉ s)).toFinset=l.toFinset\s := by
  ext i
  simp

lemma jet_inverse_laplace_zero {μ : Measure E} [IsProbabilityMeasure μ] (hμ : HasExpMoments μ)
    (v : ι → E) (l : List ι) (hl : l.Nodup) :
    JetCalculus.jet v l (fun θ => (laplace μ (fun _ => (1:ℝ)) θ)⁻¹) 0 =
      inverseMoment (moments μ (fun i x => inner ℝ (v i) x)) l.toFinset := by
  let M := laplace μ (fun _ => (1:ℝ))
  have hMs : ContDiff ℝ (⊤ : ℕ∞) M := contDiff_laplace hμ continuous_const (HasGrowth.const _)
  have hMi : ContDiff ℝ (⊤ : ℕ∞) (fun θ => (M θ)⁻¹) :=
    hMs.inv (fun θ => (laplace_one_pos hμ θ).ne')
  have hM0 : M 0=1 := by simp [M,laplace]
  have hne : ∀ θ, M θ≠0 := fun θ => (laplace_one_pos hμ θ).ne'
  induction hn : l.length using Nat.strong_induction_on generalizing l with
  | h n ih =>
    by_cases hl0 : l=[]
    · subst l
      simp [JetCalculus.jet,show laplace μ (fun _ => (1:ℝ)) 0=1 from hM0]
    have hs0 : l.toFinset ≠ ∅ := by simpa using hl0
    have hprod : (fun θ => (M θ)⁻¹*M θ)=(fun _ => (1:ℝ)) := by
      funext θ; exact inv_mul_cancel₀ (hne θ)
    have hj := congrFun (JetCalculus.jet_mul hMi hMs v l hl) 0
    rw [hprod,JetCalculus.jet_const,ite_eq_right hl0] at hj
    have hp := Finset.mem_powerset.mpr (Finset.Subset.refl l.toFinset)
    rw [← Finset.sum_erase_add _ _ hp] at hj
    have hfull : l.filter (fun i => i ∈ l.toFinset)=l := by
      apply List.filter_eq_self.mpr
      intro i hi; simpa using hi
    have hempty : l.filter (fun i => i ∉ l.toFinset)=[] := by simp
    simp only [hfull,hempty,JetCalculus.jet,hM0,mul_one] at hj
    rw [inverseMoment_nonempty _ hs0]
    have he : (∑ s ∈ l.toFinset.powerset.erase l.toFinset,
        JetCalculus.jet v (l.filter (fun i => i ∈ s)) (fun θ => (M θ)⁻¹) 0 *
        JetCalculus.jet v (l.filter (fun i => i ∉ s)) M 0) =
      ∑ s ∈ l.toFinset.powerset.erase l.toFinset,
        moments μ (fun i x => inner ℝ (v i) x) (l.toFinset\s) *
          inverseMoment (moments μ (fun i x => inner ℝ (v i) x)) s := by
      apply Finset.sum_congr rfl
      intro s hs
      have hsub := Finset.mem_powerset.mp (Finset.mem_erase.mp hs).2
      have hlen : (l.filter (fun i => i ∈ s)).length < n := by
        have hh := Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr
          ⟨hsub,(Finset.mem_erase.mp hs).1⟩)
        rw [← filter_toFinset_of_subset l s hsub,
          List.toFinset_card_of_nodup (hl.filter _),List.toFinset_card_of_nodup hl,hn] at hh
        exact hh
      rw [ih _ hlen _ (hl.filter _) rfl,filter_toFinset_of_subset l s hsub,
        jet_laplace_zero hμ v _ (hl.filter _),filter_not_toFinset,mul_comm]
    change JetCalculus.jet v l (fun θ => (M θ)⁻¹) 0 = _
    rw [he] at hj
    linarith

end Appell
end LogConcaveSampling

namespace LogConcaveSampling
namespace JetCalculus
open scoped Topology

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] {ι κ : Type*}

lemma dir_comp_affine {f : F → ℝ} (hf : Differentiable ℝ f)
    (L : E →L[ℝ] F) (b : F) (v : E) :
    dir v (fun x => f (L x+b)) = fun x => dir (L v) f (L x+b) := by
  funext x
  have hd := (hf (L x+b)).hasFDerivAt.comp x (L.hasFDerivAt.add_const b)
  change (fderiv ℝ (f ∘ fun x => L x+b) x) v = _
  rw [hd.fderiv]
  rfl

lemma jet_comp_affine {f : F → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (L : E →L[ℝ] F) (b : F) (v : ι → E) (l : List ι) :
    jet v l (fun x => f (L x+b)) = fun x => jet (fun i => L (v i)) l f (L x+b) := by
  induction l with
  | nil => rfl
  | cons i l ih =>
    rw [jet,ih,dir_comp_affine ((smooth_jet hf _ l).differentiable (by simp))]
    rfl

lemma jet_map (v : κ → E) (e : ι → κ) (l : List ι) (f : E → ℝ) :
    jet v (l.map e) f = jet (v ∘ e) l f := by
  induction l with
  | nil => rfl
  | cons i l ih => simp only [List.map_cons,jet,ih,Function.comp_apply]

lemma dir_zero (f : E → ℝ) : dir 0 f=fun _ => 0 := by funext x; simp [dir]

lemma jet_zero (l : List ι) (f : E → ℝ) :
    jet (fun _ : ι => (0:E)) l f=if l=[] then f else fun _ => 0 := by
  cases l <;> simp [jet,dir_zero]

end JetCalculus
end LogConcaveSampling

namespace LogConcaveSampling
namespace Appell
open MeasureTheory Filter
open scoped Topology RealInnerProductSpace

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
variable {ι : Type*} [DecidableEq ι]

def normalizedLaplace (μ : Measure E) (h : E → ℝ) (θ : E) : ℝ :=
  (laplace μ (fun _ => (1:ℝ)) θ)⁻¹*laplace μ h θ

lemma smooth_normalizedLaplace {μ : Measure E} [IsProbabilityMeasure μ]
    (hμ : HasExpMoments μ) {h : E → ℝ} (hh : Continuous h) (hg : HasGrowth h) :
    ContDiff ℝ (⊤ : ℕ∞) (normalizedLaplace μ h) :=
  ((contDiff_laplace hμ continuous_const (HasGrowth.const _)).inv
    (fun θ => (laplace_one_pos hμ θ).ne')).mul (contDiff_laplace hμ hh hg)

omit [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] in
lemma growth_polynomial_inner (m : Finset ι → ℝ) (s : Finset ι) (v : ι → E) :
    HasGrowth (fun x => polynomial m s (fun i => inner ℝ (v i) x)) := by
  unfold polynomial
  apply HasGrowth.sum
  intro t ht
  exact (HasGrowth.const _).mul
    (HasGrowth.prod _ (fun i _ => HasGrowth.linear (innerSL ℝ (v i))))

omit [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] in
lemma continuous_polynomial_inner (m : Finset ι → ℝ) (s : Finset ι) (v : ι → E) :
    Continuous (fun x => polynomial m s (fun i => inner ℝ (v i) x)) :=
  (polynomial_contDiff m s (fun i => innerSL ℝ (v i))).continuous

lemma jet_shift_laplace {μ : Measure E} (hμ : HasExpMoments μ)
    {h : E → ℝ} (hh : Continuous h) (hg : HasGrowth h)
    (v : ι → E) (l : List ι) (hl : l.Nodup) (θ : E) :
    JetCalculus.jet v l (fun ω => laplace μ h (θ+ω)) 0 =
      laplace μ (fun x => (∏ i ∈ l.toFinset,inner ℝ (v i) x)*h x) θ := by
  rw [show (fun ω => laplace μ h (θ+ω))=
    (fun ω => laplace μ h ((ContinuousLinearMap.id ℝ E) ω+θ)) by funext ω; simp [add_comm],
    JetCalculus.jet_comp_affine (contDiff_laplace hμ hh hg)]
  simp only [ContinuousLinearMap.id_apply,zero_add]
  rw [jet_laplace hμ hh hg v l hl]

lemma jet_normalized_at_zero {μ : Measure E} [IsProbabilityMeasure μ]
    (hμ : HasExpMoments μ) {h : E → ℝ} (hh : Continuous h) (hg : HasGrowth h)
    (v : ι → E) (l : List ι) (hl : l.Nodup) (θ : E) :
    JetCalculus.jet v l (fun ω => (laplace μ (fun _ => (1:ℝ)) ω)⁻¹ *
      laplace μ h (θ+ω)) 0 =
    laplace μ (fun x => polynomial (moments μ (fun i x => inner ℝ (v i) x))
      l.toFinset (fun i => inner ℝ (v i) x)*h x) θ := by
  have hM := contDiff_laplace hμ continuous_const (HasGrowth.const (1:ℝ))
  have hMi : ContDiff ℝ (⊤ : ℕ∞) (fun θ => (laplace μ (fun _ => (1:ℝ)) θ)⁻¹) :=
    hM.inv (fun θ => (laplace_one_pos hμ θ).ne')
  have hc : ContDiff ℝ (⊤ : ℕ∞) (fun ω => laplace μ h (θ+ω)) :=
    (contDiff_laplace hμ hh hg).comp (contDiff_const.add contDiff_id)
  rw [JetCalculus.jet_mul hMi hc v l hl]
  conv_rhs => simp only [laplace,polynomial,Finset.sum_mul,Finset.mul_sum,smul_eq_mul]
  rw [integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro s hs
    rw [jet_inverse_laplace_zero hμ v _ (hl.filter _),
      filter_toFinset_of_subset l s (Finset.mem_powerset.mp hs),
      jet_shift_laplace hμ hh hg v _ (hl.filter _),filter_not_toFinset]
    rw [laplace,← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [] with x
    simp only [smul_eq_mul]
    ring
  · intro s hs
    have hpoly := (HasGrowth.const (inverseMoment (moments μ
      (fun i x => inner ℝ (v i) x)) s)).mul
      ((HasGrowth.prod (l.toFinset\s) (fun i _ => HasGrowth.linear (innerSL ℝ (v i)))).mul hg)
    have hct : Continuous (fun x => inverseMoment (moments μ
        (fun i x => inner ℝ (v i) x)) s * ((∏ i ∈ l.toFinset\s,inner ℝ (v i) x)*h x)) :=
      continuous_const.mul ((continuous_finsetProd _
        (fun _ _ => continuous_const.inner continuous_id)).mul hh)
    convert hμ.integrable_laplace hct.aestronglyMeasurable hpoly θ using 1
    funext x; simp only [smul_eq_mul]; ring

lemma jet_normalizedLaplace_zero {μ : Measure E} [IsProbabilityMeasure μ]
    (hμ : HasExpMoments μ) {h : E → ℝ} (hh : Continuous h) (hg : HasGrowth h)
    (v : ι → E) (l : List ι) (hl : l.Nodup) :
    JetCalculus.jet v l (normalizedLaplace μ h) 0 =
      ∫ x, polynomial (moments μ (fun i x => inner ℝ (v i) x))
        l.toFinset (fun i => inner ℝ (v i) x)*h x ∂μ := by
  change JetCalculus.jet v l (fun θ => (laplace μ (fun _ => (1:ℝ)) θ)⁻¹*laplace μ h θ) 0 = _
  simpa only [zero_add,laplace_zero] using
    jet_normalized_at_zero hμ hh hg v l hl 0

end Appell
end LogConcaveSampling

namespace LogConcaveSampling
namespace JetCalculus
open scoped Topology BigOperators

def logTrunc (n : ℕ) (t : ℝ) : ℝ :=
  ∑ m ∈ Finset.range n, ((-1:ℝ)^m/(m+1))*(t-1)^(m+1)

lemma smooth_logTrunc (n : ℕ) : ContDiff ℝ (⊤ : ℕ∞) (logTrunc n) := by
  apply ContDiff.sum
  intro m hm
  exact contDiff_const.mul ((contDiff_id.sub contDiff_const).pow _)

lemma hasDerivAt_logTrunc (n : ℕ) (t : ℝ) :
    HasDerivAt (logTrunc n) (∑ m ∈ Finset.range n, (1-t)^m) t := by
  have hd := HasDerivAt.sum (u := Finset.range n) (fun m _ =>
    ((((hasDerivAt_id t).sub_const 1).pow (m+1)).const_mul ((-1:ℝ)^m/(m+1))))
  convert! hd using 1
  · funext y; simp [logTrunc]
  · apply Finset.sum_congr rfl
    intro m hm
    have hm' : (m:ℝ)+1 ≠ 0 := by positivity
    simp only [Nat.cast_add,Nat.cast_one,Nat.add_sub_cancel,mul_one,id_eq]
    rw [show 1-t= -(t-1) by ring,neg_pow]
    field_simp

@[simp] lemma logTrunc_one (n : ℕ) : logTrunc n 1 = 0 := by simp [logTrunc]

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {ι : Type*} [DecidableEq ι]

lemma dir_log_remainder {G : E → ℝ} (hG : ContDiff ℝ (⊤ : ℕ∞) G)
    (hpos : ∀ x, 0 < G x) (n : ℕ) (v : E) :
    dir v (fun x => Real.log (G x)-logTrunc n (G x)) =
      fun x => (G x-1)^n*((-1:ℝ)^n*(G x)⁻¹*dir v G x) := by
  funext x
  have hd := ((hG.differentiable (by simp) x).hasFDerivAt.log (hpos x).ne').sub
    ((hasDerivAt_logTrunc n (G x)).comp_hasFDerivAt x
      (hG.differentiable (by simp) x).hasFDerivAt)
  change (fderiv ℝ ((fun x => Real.log (G x)) - logTrunc n ∘ G) x) v = _
  rw [hd.fderiv]
  simp only [sub_apply,smul_apply,smul_eq_mul]
  have hgeom := geom_sum_mul (1-G x) n
  have hpow : (1-G x)^n=(-1:ℝ)^n*(G x-1)^n := by
    rw [show 1-G x= -(G x-1) by ring,neg_pow]
  rw [hpow] at hgeom
  change (G x)⁻¹*dir v G x-(∑ m ∈ Finset.range n,(1-G x)^m)*dir v G x = _
  have hh : (G x)⁻¹-(∑ m ∈ Finset.range n,(1-G x)^m) =
      (G x-1)^n*((-1:ℝ)^n*(G x)⁻¹) := by
    apply (mul_left_cancel₀ (hpos x).ne')
    have hinv := mul_inv_cancel₀ (hpos x).ne'
    calc
      G x*((G x)⁻¹-∑ m ∈ Finset.range n,(1-G x)^m) =
          1-G x*(∑ m ∈ Finset.range n,(1-G x)^m) := by rw [mul_sub,hinv]
      _ = (-1:ℝ)^n*(G x-1)^n := by nlinarith only [hgeom]
      _ = (G x*(G x)⁻¹)*((-1:ℝ)^n*(G x-1)^n) := by rw [hinv,one_mul]
      _ = _ := by ring
  rw [show (G x)⁻¹*dir v G x-(∑ m ∈ Finset.range n,(1-G x)^m)*dir v G x =
    ((G x)⁻¹-(∑ m ∈ Finset.range n,(1-G x)^m))*dir v G x by ring,hh]
  ring

lemma jet_logTrunc {G : E → ℝ} (hG : ContDiff ℝ (⊤ : ℕ∞) G)
    (hpos : ∀ x, 0 < G x) (n : ℕ) (v : ι → E) (l : List ι)
    (hl : l.Nodup) {x : E} (hx : G x=1) (hlen : l.length ≤ n) :
    jet v l (fun x => Real.log (G x)) x = jet v l (fun x => logTrunc n (G x)) x := by
  have hs : ContDiff ℝ (⊤ : ℕ∞) (fun x => Real.log (G x)) := hG.log (fun x => (hpos x).ne')
  have ht : ContDiff ℝ (⊤ : ℕ∞) (fun x => logTrunc n (G x)) := (smooth_logTrunc n).comp hG
  suffices h : jet v l (fun x => Real.log (G x)-logTrunc n (G x)) x=0 by
    rw [jet_sub hs ht] at h
    exact sub_eq_zero.mp h
  induction l using List.reverseRecOn with
  | nil => simp [jet,hx]
  | append_singleton l i ih =>
    rw [jet_append]
    change jet v l (dir (v i) (fun x => Real.log (G x)-logTrunc n (G x))) x=0
    rw [dir_log_remainder hG hpos]
    apply jet_pow_mul_zero (hG.sub contDiff_const)
      ((contDiff_const.mul (hG.inv (fun x => (hpos x).ne'))).mul (smooth_dir hG _)) v n l
    · exact (List.nodup_append.mp hl).1
    · exact sub_eq_zero.mpr hx
    · simp only [List.length_append,List.length_singleton] at hlen
      omega

end JetCalculus
end LogConcaveSampling

namespace LogConcaveSampling
namespace JetCalculus
open scoped Topology

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] {ι κ : Type*}

def mixedJet (v : ι → E) (w : κ → F) (l : List ι) (k : List κ)
    (f : E × F → ℝ) : ℝ := jet v l (fun θ => jet w k (fun ω => f (θ,ω)) 0) 0

lemma jet_right_slice {f : E × F → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (w : κ → F) (k : List κ) (θ : E) (ω : F) :
    jet w k (fun ω => f (θ,ω)) ω=jet (fun i => ((0:E),w i)) k f (θ,ω) := by
  have hh := congrFun (jet_comp_affine hf
    ((0 : F →L[ℝ] E).prod (ContinuousLinearMap.id ℝ F)) (θ,0) w k) ω
  simpa using hh

lemma jet_left_slice {f : E × F → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (v : ι → E) (l : List ι) (θ : E) (ω : F) :
    jet v l (fun θ => f (θ,ω)) θ=jet (fun i => (v i,(0:F))) l f (θ,ω) := by
  have hh := congrFun (jet_comp_affine hf
    ((ContinuousLinearMap.id ℝ E).prod (0 : E →L[ℝ] F)) (0,ω) v l) θ
  simpa using hh

lemma mixedJet_eq_joint {f : E × F → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (v : ι → E) (w : κ → F) (l : List ι) (k : List κ) :
    mixedJet v w l k f=jet (Sum.elim (fun i => (v i,(0:F))) (fun j => ((0:E),w j)))
      (l.map Sum.inl++k.map Sum.inr) f 0 := by
  rw [jet_append,jet_map,jet_map]
  change mixedJet v w l k f=jet (fun i => (v i,(0:F))) l
    (jet (fun j => ((0:E),w j)) k f) (0,0)
  unfold mixedJet
  simp_rw [jet_right_slice hf]
  exact jet_left_slice (smooth_jet hf _ k) v l 0 0

lemma mixedJet_sub {f g : E × F → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (hg : ContDiff ℝ (⊤ : ℕ∞) g) (v : ι → E) (w : κ → F) (l : List ι) (k : List κ) :
    mixedJet v w l k (fun x => f x-g x)=mixedJet v w l k f-mixedJet v w l k g := by
  rw [mixedJet_eq_joint (hf.sub hg),jet_sub hf hg,
    mixedJet_eq_joint hf,mixedJet_eq_joint hg]

lemma mixedJet_sum {N : Type*} (s : Finset N) {f : N → E × F → ℝ}
    (hf : ∀ n ∈ s, ContDiff ℝ (⊤ : ℕ∞) (f n))
    (v : ι → E) (w : κ → F) (l : List ι) (k : List κ) :
    mixedJet v w l k (fun x => ∑ n ∈ s,f n x)=∑ n ∈ s,mixedJet v w l k (f n) := by
  rw [mixedJet_eq_joint (ContDiff.sum hf),jet_sum s hf]
  apply Finset.sum_congr rfl
  intro n hn
  exact (mixedJet_eq_joint (hf n hn) v w l k).symm

lemma mixedJet_const_mul {f : E × F → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (v : ι → E) (w : κ → F) (l : List ι) (k : List κ) (c : ℝ) :
    mixedJet v w l k (fun x => c*f x)=c*mixedJet v w l k f := by
  rw [mixedJet_eq_joint (contDiff_const.mul hf),jet_const_mul hf,mixedJet_eq_joint hf]

lemma mixedJet_const (v : ι → E) (w : κ → F) (l : List ι) (k : List κ) (c : ℝ) :
    mixedJet v w l k (fun _ => c)=if l=[] ∧ k=[] then c else 0 := by
  rw [mixedJet_eq_joint contDiff_const,jet_const]
  simp only [List.append_eq_nil_iff,List.map_eq_nil_iff]
  split_ifs <;> rfl

lemma nodup_sum_append {l : List ι} {k : List κ} (hl : l.Nodup) (hk : k.Nodup) :
    (l.map Sum.inl++k.map Sum.inr).Nodup := by
  rw [List.nodup_append]
  refine ⟨hl.map Sum.inl_injective,hk.map Sum.inr_injective,?_⟩
  intro x hx y hy hxy
  subst y
  obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hx
  obtain ⟨j,hj,hji⟩ := List.mem_map.mp hy
  cases hji

lemma mixedJet_logTrunc [DecidableEq ι] [DecidableEq κ]
    {G : E × F → ℝ} (hG : ContDiff ℝ (⊤ : ℕ∞) G) (hpos : ∀ x,0 < G x)
    (hG0 : G 0=1) (v : ι → E) (w : κ → F) (l : List ι) (k : List κ)
    (hl : l.Nodup) (hk : k.Nodup) :
    mixedJet v w l k (fun x => Real.log (G x)) =
      mixedJet v w l k (fun x => logTrunc (l.length+k.length) (G x)) := by
  have ht : ContDiff ℝ (⊤ : ℕ∞) (fun x => logTrunc (l.length+k.length) (G x)) :=
    (smooth_logTrunc _).comp hG
  rw [mixedJet_eq_joint (hG.log (fun x => (hpos x).ne')),mixedJet_eq_joint ht]
  apply jet_logTrunc hG hpos _ _ _ (nodup_sum_append hl hk) hG0
  simp

end JetCalculus
end LogConcaveSampling

namespace LogConcaveSampling
namespace Appell
open MeasureTheory Filter
open scoped Topology RealInnerProductSpace

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
variable {ι κ : Type*} [DecidableEq ι] [DecidableEq κ]

def crossMGF (μ : Measure E) (t : E × E) : ℝ :=
  (laplace μ (fun _ => (1:ℝ)) t.1)⁻¹ *
    ((laplace μ (fun _ => (1:ℝ)) t.2)⁻¹*laplace μ (fun _ => (1:ℝ)) (t.1+t.2))

lemma smooth_crossMGF {μ : Measure E} [IsProbabilityMeasure μ] (hμ : HasExpMoments μ) :
    ContDiff ℝ (⊤ : ℕ∞) (crossMGF μ) := by
  have hM := contDiff_laplace hμ continuous_const (HasGrowth.const (1:ℝ))
  have hi := hM.inv (fun θ => (laplace_one_pos hμ θ).ne')
  exact (hi.comp contDiff_fst).mul
    ((hi.comp contDiff_snd).mul (hM.comp (contDiff_fst.add contDiff_snd)))

omit [SecondCountableTopology E] in
lemma crossMGF_pos {μ : Measure E} [IsProbabilityMeasure μ] (hμ : HasExpMoments μ)
    (t : E × E) : 0 < crossMGF μ t := by
  exact mul_pos (inv_pos.mpr (laplace_one_pos hμ _))
    (mul_pos (inv_pos.mpr (laplace_one_pos hμ _)) (laplace_one_pos hμ _))

omit [BorelSpace E] [SecondCountableTopology E] in
@[simp] lemma crossMGF_zero {μ : Measure E} [IsProbabilityMeasure μ] : crossMGF μ 0=1 := by
  simp [crossMGF,laplace]

omit [SecondCountableTopology E] in
lemma crossMGF_left_zero {μ : Measure E} [IsProbabilityMeasure μ] (hμ : HasExpMoments μ)
    (t : E) : crossMGF μ (0,t)=1 := by
  have hM0 : laplace μ (fun _ => (1:ℝ)) 0=1 := by simp [laplace]
  simp only [crossMGF,hM0,inv_one,one_mul,zero_add]
  exact inv_mul_cancel₀ (laplace_one_pos hμ t).ne'

omit [SecondCountableTopology E] in
lemma crossMGF_right_zero {μ : Measure E} [IsProbabilityMeasure μ] (hμ : HasExpMoments μ)
    (t : E) : crossMGF μ (t,0)=1 := by
  have hM0 : laplace μ (fun _ => (1:ℝ)) 0=1 := by simp [laplace]
  simp only [crossMGF,hM0,inv_one,one_mul,add_zero]
  exact inv_mul_cancel₀ (laplace_one_pos hμ t).ne'

lemma mixedJet_crossMGF {μ : Measure E} [IsProbabilityMeasure μ] (hμ : HasExpMoments μ)
    (v : ι → E) (w : κ → E) (l : List ι) (k : List κ) (hl : l.Nodup) (hk : k.Nodup) :
    JetCalculus.mixedJet v w l k (crossMGF μ) =
      ∫ x, polynomial (moments μ (fun i x => inner ℝ (v i) x)) l.toFinset
        (fun i => inner ℝ (v i) x)*
        polynomial (moments μ (fun i x => inner ℝ (w i) x)) k.toFinset
          (fun i => inner ℝ (w i) x) ∂μ := by
  have hc (θ : E) : ContDiff ℝ (⊤ : ℕ∞) (fun ω =>
      (laplace μ (fun _ => (1:ℝ)) ω)⁻¹*laplace μ (fun _ => (1:ℝ)) (θ+ω)) :=
    ((contDiff_laplace hμ continuous_const (HasGrowth.const _)).inv
      (fun θ => (laplace_one_pos hμ θ).ne')).mul
      ((contDiff_laplace hμ continuous_const (HasGrowth.const _)).comp
        (contDiff_const.add contDiff_id))
  unfold JetCalculus.mixedJet crossMGF
  simp_rw [JetCalculus.jet_const_mul (hc _),
    jet_normalized_at_zero hμ continuous_const (HasGrowth.const (1:ℝ)) w k hk]
  simp only [mul_one]
  exact jet_normalizedLaplace_zero hμ (continuous_polynomial_inner _ _ w) (growth_polynomial_inner _ _ w) v l hl

omit [DecidableEq ι] [DecidableEq κ] in
omit [SecondCountableTopology E] in
lemma mixedJet_reduced_unmixed {μ : Measure E} [IsProbabilityMeasure μ] (hμ : HasExpMoments μ)
    (v : ι → E) (w : κ → E) (l : List ι) (k : List κ) (hempty : l=[] ∨ k=[]) :
    JetCalculus.mixedJet v w l k (fun x => crossMGF μ x-1)=0 := by
  rcases hempty with rfl | rfl
  · simp only [JetCalculus.mixedJet,JetCalculus.jet]
    simp_rw [crossMGF_left_zero hμ,sub_self]
    simp [JetCalculus.jet_const]
  · simp only [JetCalculus.mixedJet,JetCalculus.jet]
    simp_rw [crossMGF_right_zero hμ,sub_self]
    simp [JetCalculus.jet_const]

lemma mixedJet_reduced {μ : Measure E} [IsProbabilityMeasure μ] (hμ : HasExpMoments μ)
    (v : ι → E) (w : κ → E) (l : List ι) (k : List κ) (hl : l.Nodup) (hk : k.Nodup)
    (hn : ¬(l=[] ∧ k=[])) :
    JetCalculus.mixedJet v w l k (fun x => crossMGF μ x-1) =
      ∫ x, polynomial (moments μ (fun i x => inner ℝ (v i) x)) l.toFinset
        (fun i => inner ℝ (v i) x)*
        polynomial (moments μ (fun i x => inner ℝ (w i) x)) k.toFinset
          (fun i => inner ℝ (w i) x) ∂μ := by
  rw [JetCalculus.mixedJet_sub (smooth_crossMGF hμ) contDiff_const,
    JetCalculus.mixedJet_const,ite_eq_right hn,sub_zero,mixedJet_crossMGF hμ v w l k hl hk]

end Appell
end LogConcaveSampling

namespace LogConcaveSampling
namespace JetCalculus
open scoped Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {ι N : Type*} [DecidableEq ι] [Fintype N] [DecidableEq N]

def assignments (n₀ : N) : List ι → List (ι → N)
  | [] => [fun _ => n₀]
  | i::l => (assignments n₀ l).flatMap (fun p =>
      (Finset.univ.toList : List N).map (fun j => Function.update p i j))

omit [DecidableEq N] in
lemma length_assignments (n₀ : N) (l : List ι) :
    (assignments n₀ l).length = (Fintype.card N)^l.length := by
  induction l with
  | nil => simp [assignments]
  | cons i l ih =>
    simp only [assignments,List.length_flatMap,List.length_map,Finset.length_toList,
      Finset.card_univ,List.map_const',List.sum_replicate,smul_eq_mul,ih,List.length_cons,pow_succ]

omit [DecidableEq N] in
lemma assignments_default (n₀ : N) (l : List ι) {p : ι → N}
    (hp : p ∈ assignments n₀ l) {i : ι} (hi : i ∉ l) : p i=n₀ := by
  induction l generalizing p i with
  | nil => simpa [assignments] using congrFun (List.mem_singleton.mp hp) i
  | cons a l ih =>
    obtain ⟨q,hq,hp⟩ := List.mem_flatMap.mp hp
    obtain ⟨j,hj,rfl⟩ := List.mem_map.mp hp
    have hia : i ≠ a := fun h => hi (by simp [h])
    rw [Function.update_of_ne hia]
    exact ih hq (fun h => hi (List.mem_cons_of_mem _ h))

omit [DecidableEq N] in
lemma mem_assignments (n₀ : N) (l : List ι) (hl : l.Nodup) (p : ι → N)
    (hp : ∀ i, i ∉ l → p i=n₀) : p ∈ assignments n₀ l := by
  induction l generalizing p with
  | nil =>
    have : p=(fun _ => n₀) := funext (fun i => hp i (by simp))
    simp [assignments,this]
  | cons i l ih =>
    have hin := (List.nodup_cons.mp hl).1
    have hl' := (List.nodup_cons.mp hl).2
    apply List.mem_flatMap.mpr
    refine ⟨Function.update p i n₀,ih hl' (Function.update p i n₀) (fun j hj => ?_),?_⟩
    · by_cases hji : j=i
      · simp [hji]
      · simpa [Function.update_of_ne hji] using hp j (by simp [hji,hj])
    · apply List.mem_map.mpr
      refine ⟨p i,by simp,?_⟩
      ext j
      by_cases hji : j=i <;> simp [hji,Function.update_of_ne]

omit [Fintype N] in
lemma filter_update (l : List ι) (i : ι) (hi : i ∉ l) (p : ι → N) (j n : N) :
    l.filter (fun a => Function.update p i j a=n) = l.filter (fun a => p a=n) := by
  apply List.filter_congr
  intro a ha
  have hai : a ≠ i := fun h => hi (h ▸ ha)
  simp [Function.update_of_ne hai]

lemma differentiable_list_sum {K : Type*} (l : List K) {f : K → E → ℝ}
    (hf : ∀ i ∈ l, Differentiable ℝ (f i)) :
    Differentiable ℝ (fun x => (l.map (fun i => f i x)).sum) := by
  induction l with
  | nil => simpa only [List.map_nil,List.sum_nil] using (differentiable_const (0:ℝ) : Differentiable ℝ (fun _ : E => (0:ℝ)))
  | cons i l ih =>
    simpa only [List.map_cons,List.sum_cons] using
      (hf i (by simp)).fun_add (ih (fun j hj => hf j (by simp [hj])))

lemma dir_list_sum {K : Type*} (l : List K) {f : K → E → ℝ}
    (hf : ∀ i ∈ l, Differentiable ℝ (f i)) (v : E) :
    dir v (fun x => (l.map (fun i => f i x)).sum) =
      fun x => (l.map (fun i => dir v (f i) x)).sum := by
  induction l with
  | nil =>
    funext x
    change fderiv ℝ (fun _ : E => (0:ℝ)) x v = 0
    simp
  | cons i l ih =>
    simp only [List.map_cons,List.sum_cons]
    rw [dir_add (hf i (by simp))]
    · rw [ih (fun j hj => hf j (by simp [hj]))]
    · exact differentiable_list_sum l (fun j hj => hf j (by simp [hj]))

lemma smooth_list_sum {K : Type*} (l : List K) {f : K → E → ℝ}
    (hf : ∀ i ∈ l, ContDiff ℝ (⊤ : ℕ∞) (f i)) :
    ContDiff ℝ (⊤ : ℕ∞) (fun x => (l.map (fun i => f i x)).sum) := by
  induction l with
  | nil => simpa using (contDiff_const : ContDiff ℝ (⊤ : ℕ∞) (fun _ : E => (0:ℝ)))
  | cons i l ih =>
    simpa only [List.map_cons,List.sum_cons] using
      (hf i (by simp)).add (ih (fun j hj => hf j (by simp [hj])))

omit [DecidableEq ι] in
lemma jet_list_sum {K : Type*} (t : List K) {f : K → E → ℝ}
    (hf : ∀ i ∈ t, ContDiff ℝ (⊤ : ℕ∞) (f i)) (v : ι → E) (l : List ι) :
    jet v l (fun x => (t.map (fun i => f i x)).sum) =
      fun x => (t.map (fun i => jet v l (f i) x)).sum := by
  induction l with
  | nil => rfl
  | cons i l ih =>
    simp only [jet,ih]
    exact dir_list_sum t (fun j hj => (smooth_jet (hf j hj) v l).differentiable (by simp)) _

lemma list_sum_flatMap {K : Type*} (l : List K) (f : K → List ℝ) :
    (l.flatMap f).sum=(l.map (fun i => (f i).sum)).sum := by
  induction l with
  | nil => rfl
  | cons i l ih => simp [ih]

omit [DecidableEq N] in
lemma sum_eq_list (f : N → ℝ) :
    (∑ n, f n) = ((Finset.univ.toList : List N).map f).sum := by
  classical
  simp only [← List.sum_toFinset f (Finset.nodup_toList (Finset.univ : Finset N)),
    Finset.toList_toFinset]

lemma dir_prod {f : N → E → ℝ} (hf : ∀ n, Differentiable ℝ (f n)) (v : E) :
    dir v (fun x => ∏ n, f n x) = fun x =>
      ∑ j, ∏ n, (if n=j then dir v (f n) x else f n x) := by
  funext x
  rw [dir,(HasFDerivAt.finsetProd (fun n (_ : n ∈ (Finset.univ : Finset N)) =>
    (hf n x).hasFDerivAt)).fderiv]
  simp only [sum_apply,smul_apply,smul_eq_mul]
  apply Finset.sum_congr rfl
  intro j hj
  have hh : (fun n => if n=j then dir v (f n) x else f n x)=
      Function.update (fun n => f n x) j (dir v (f j) x) := by ext n; by_cases h : n=j <;> simp [h]
  rw [hh,Finset.prod_update_of_mem hj]
  simp only [Finset.sdiff_singleton_eq_erase,dir]
  ring

theorem jet_prod {f : N → E → ℝ} (hf : ∀ n, ContDiff ℝ (⊤ : ℕ∞) (f n))
    (n₀ : N) (v : ι → E) (l : List ι) (hl : l.Nodup) :
    jet v l (fun x => ∏ n, f n x) = fun x =>
      ((assignments n₀ l).map (fun p => ∏ n, jet v (l.filter (fun i => p i=n)) (f n) x)).sum := by
  induction l with
  | nil => simp [jet,assignments]
  | cons i l ih =>
    have hi := (List.nodup_cons.mp hl).1
    have hl' := (List.nodup_cons.mp hl).2
    rw [jet,ih hl',dir_list_sum _ (fun p hp =>
      (contDiff_prod (fun n _ => smooth_jet (hf n) v _)).differentiable (by simp))]
    funext x
    simp only [assignments,List.map_flatMap,list_sum_flatMap,List.map_map,Function.comp_def]
    apply congrArg List.sum
    apply List.map_congr_left
    intro p hp
    rw [dir_prod (fun n => (smooth_jet (hf n) v _).differentiable (by simp))]
    dsimp only
    rw [sum_eq_list]
    apply congrArg List.sum
    apply List.map_congr_left
    intro j hj
    apply Finset.prod_congr rfl
    intro n hn
    rw [List.filter_cons,filter_update l i hi]
    by_cases hnj : n=j
    · simp [hnj,jet]
    · simp [hnj,Ne.symm hnj]

end JetCalculus
end LogConcaveSampling

end UpperProof
end
end
end

end OAI
