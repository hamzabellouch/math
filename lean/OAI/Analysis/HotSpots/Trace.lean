import OAI.Analysis.HotSpots.Dirichlet

namespace OAI

section DouglasLipschitzBase
noncomputable section
section NodalSmoothingCombinedLayer

open Set Filter MeasureTheory Metric
open scoped Topology ContDiff
namespace StrictHotSpots.Nodal

lemma transition_deriv_zero {t : ℝ} (h : t ≤ 0 ∨ 1 ≤ t) :
    deriv Real.smoothTransition t = 0 := by
  rcases h with h | h
  · apply IsLocalMin.deriv_eq_zero
    exact Eventually.of_forall fun y => by
      rw [Real.smoothTransition.zero_of_nonpos h]
      exact Real.smoothTransition.nonneg y
  · apply IsLocalMax.deriv_eq_zero
    exact Eventually.of_forall fun y => by
      rw [Real.smoothTransition.one_of_one_le h]
      exact Real.smoothTransition.le_one y

def cutoff (n : ℕ) (t : ℝ) : ℝ := t * Real.smoothTransition (((n:ℝ)+1)*t-1)

lemma cutoff_contDiff (n : ℕ) : ContDiff ℝ ∞ (cutoff n) := by
  unfold cutoff
  exact contDiff_id.mul (Real.smoothTransition.contDiff.comp ((contDiff_const.mul contDiff_id).sub contDiff_const))

lemma cutoff_deriv (n : ℕ) (t : ℝ) : deriv (cutoff n) t =
    Real.smoothTransition (((n:ℝ)+1)*t-1) +
      (((n:ℝ)+1)*t) * deriv Real.smoothTransition (((n:ℝ)+1)*t-1) := by
  have hh := (hasDerivAt_id t).mul
    ((((Real.smoothTransition.contDiff : ContDiff ℝ ∞ _).differentiable (by simp)).differentiableAt.hasDerivAt).comp t
      (((hasDerivAt_id t).const_mul ((n:ℝ)+1)).sub_const 1))
  have he : (id * Real.smoothTransition ∘ (fun x : ℝ => ((n:ℝ)+1)*id x-1)) = cutoff n := rfl
  rw [he] at hh
  rw [hh.deriv]
  simp only [Function.comp_apply,id_eq,one_mul,mul_one]
  ring

lemma cutoff_zero (n : ℕ) {t : ℝ} (ht : t < 1/((n:ℝ)+1)) : cutoff n t = 0 := by
  unfold cutoff
  rw [Real.smoothTransition.zero_of_nonpos, mul_zero]
  have hn : 0 < (n:ℝ)+1 := by positivity
  have := (lt_div_iff₀ hn).mp ht
  nlinarith

lemma cutoff_norm_le (n : ℕ) (t : ℝ) : ‖cutoff n t‖ ≤ ‖t‖ := by
  change ‖t * Real.smoothTransition (((n:ℝ)+1)*t-1)‖ ≤ ‖t‖
  rw [norm_mul,Real.norm_of_nonneg (Real.smoothTransition.nonneg _)]
  exact mul_le_of_le_one_right (norm_nonneg t) (Real.smoothTransition.le_one _)

lemma cutoff_deriv_bound : ∃ C : ℝ, 1 ≤ C ∧ ∀ n t, ‖deriv (cutoff n) t‖ ≤ C := by
  obtain ⟨M,hM⟩ := isCompact_Icc.exists_bound_of_continuousOn
    ((Real.smoothTransition.contDiff.continuous_deriv (by simp : (1:ℕ∞ω) ≤ ∞)).continuousOn :
      ContinuousOn (deriv Real.smoothTransition) (Icc (0:ℝ) 1))
  have hM0 : 0 ≤ M := le_trans (norm_nonneg _) (hM 0 (by simp))
  refine ⟨1+2*M,by linarith,fun n t => ?_⟩
  rw [cutoff_deriv]
  have hτ : ‖Real.smoothTransition (((n:ℝ)+1)*t-1)‖ ≤ 1 := by
    rw [Real.norm_of_nonneg (Real.smoothTransition.nonneg _)]
    exact Real.smoothTransition.le_one _
  by_cases h : ((n:ℝ)+1)*t-1 ∈ Icc (0:ℝ) 1
  · have hnt : ‖((n:ℝ)+1)*t‖ ≤ 2 := by
      rw [Real.norm_eq_abs,abs_le]
      constructor <;> linarith [h.1,h.2]
    calc
      _ ≤ ‖Real.smoothTransition (((n:ℝ)+1)*t-1)‖ +
          ‖((n:ℝ)+1)*t * deriv Real.smoothTransition (((n:ℝ)+1)*t-1)‖ := norm_add_le _ _
      _ ≤ 1 + 2*M := by rw [norm_mul]; gcongr; exact hM _ h
  · have hd : deriv Real.smoothTransition (((n:ℝ)+1)*t-1) = 0 := by
      apply transition_deriv_zero
      simp only [mem_Icc,not_and_or,not_le] at h
      exact h.imp le_of_lt le_of_lt
    rw [hd,mul_zero,add_zero]
    linarith

lemma cutoff_eventually_eq {t : ℝ} (ht : 0 < t) :
    ∀ᶠ n : ℕ in atTop, cutoff n t = t ∧ deriv (cutoff n) t = 1 := by
  have hn : Tendsto (fun n : ℕ => ((n:ℝ)+1)*t-1) atTop atTop :=
    by
      simpa only [sub_eq_add_neg] using tendsto_atTop_add_const_right atTop (-1 : ℝ)
        ((tendsto_atTop_add_const_right atTop (1 : ℝ) tendsto_natCast_atTop_atTop).atTop_mul_const ht)
  filter_upwards [hn.eventually_ge_atTop 1] with n hn
  constructor
  · simp [cutoff,Real.smoothTransition.one_of_one_le hn]
  · rw [cutoff_deriv,Real.smoothTransition.one_of_one_le hn,
      transition_deriv_zero (Or.inr hn),mul_zero,add_zero]

end StrictHotSpots.Nodal
end NodalSmoothingCombinedLayer

section BoundarySignTestsCombinedLayer
open Set Filter MeasureTheory Metric
open scoped Topology ContDiff InnerProductSpace ENNReal
namespace StrictHotSpots.BoundarySign
variable {Ω : Set Plane} {u : Plane → ℝ}
def cut (Ω : Set Plane) (u : Plane → ℝ) (n : ℕ) : Plane → ℝ :=
  Ω.indicator (fun x => Nodal.cutoff n (u x))
def cutSupport (Ω : Set Plane) (u : Plane → ℝ) (n : ℕ) : Set Plane :=
  closure Ω ∩ u ⁻¹' Ici (1 / ((n:ℝ)+1))
lemma support_cut_subset (n : ℕ) : Function.support (cut Ω u n) ⊆ cutSupport Ω u n := by
  intro x hx
  by_cases hxΩ : x ∈ Ω
  · refine ⟨subset_closure hxΩ, ?_⟩
    by_contra h
    apply hx
    exact (indicator_of_mem hxΩ _).trans (Nodal.cutoff_zero n (lt_of_not_ge h))
  · exact False.elim (hx (indicator_of_notMem hxΩ _))
lemma cutSupport_closed (hu : ContinuousOn u (closure Ω)) (n : ℕ) :
    IsClosed (cutSupport Ω u n) :=
  hu.preimage_isClosed_of_isClosed isClosed_closure isClosed_Ici
lemma cutSupport_subset (ho : IsOpen Ω) (hb : ∀ x ∈ frontier Ω, u x ≤ 0) (n : ℕ) :
    cutSupport Ω u n ⊆ Ω := by
  intro x hx
  by_contra hn
  have hf : x ∈ frontier Ω := by
    rw [frontier,ho.interior_eq]
    exact ⟨hx.1,hn⟩
  have hp : 0 < 1 / ((n:ℝ)+1) := by positivity
  exact (not_le_of_gt hp) (hx.2.trans (hb x hf))
lemma cut_eq_zero_nhds (hu : ContinuousOn u (closure Ω)) (n : ℕ) {x : Plane}
    (hx : x ∉ cutSupport Ω u n) : cut Ω u n =ᶠ[𝓝 x] 0 := by
  filter_upwards [(cutSupport_closed hu n).isOpen_compl.mem_nhds hx] with y hy
  by_contra h
  exact hy (support_cut_subset n h)
lemma cut_eq_nhds (ho : IsOpen Ω) (n : ℕ) {x : Plane} (hx : x ∈ Ω) :
    cut Ω u n =ᶠ[𝓝 x] (fun y => Nodal.cutoff n (u y)) := by
  filter_upwards [ho.mem_nhds hx] with y hy
  exact indicator_of_mem hy _
lemma cut_contDiff (ho : IsOpen Ω) (hu : ContDiffOn ℝ ∞ u (closure Ω))
    (hb : ∀ x ∈ frontier Ω, u x ≤ 0) (n : ℕ) : ContDiff ℝ ∞ (cut Ω u n) := by
  rw [contDiff_iff_contDiffAt]
  intro x
  by_cases hx : x ∈ Ω
  · exact ((Nodal.cutoff_contDiff n).contDiffAt.comp x
      ((hu.mono subset_closure).contDiffAt (ho.mem_nhds hx))).congr_of_eventuallyEq
      (cut_eq_nhds ho n hx)
  · exact contDiffAt_const.congr_of_eventuallyEq
      (cut_eq_zero_nhds hu.continuousOn n (fun h => hx (cutSupport_subset ho hb n h)))
lemma cut_tsupport_subset (ho : IsOpen Ω) (hu : ContinuousOn u (closure Ω))
    (hb : ∀ x ∈ frontier Ω, u x ≤ 0) (n : ℕ) : tsupport (cut Ω u n) ⊆ Ω :=
  ((cutSupport_closed hu n).closure_subset_iff.mpr (support_cut_subset n)).trans
    (cutSupport_subset ho hb n)
lemma cut_hasCompactSupport (hu : ContinuousOn u (closure Ω))
    (hb : Bornology.IsBounded Ω) (n : ℕ) : HasCompactSupport (cut Ω u n) := by
  apply hb.isCompact_closure.of_isClosed_subset isClosed_closure
  exact ((cutSupport_closed hu n).closure_subset_iff.mpr (support_cut_subset n)).trans
    inter_subset_left

def test (ho : IsOpen Ω) (hu : ContDiffOn ℝ ∞ u (closure Ω))
    (hbound : Bornology.IsBounded Ω) (hb : ∀ x ∈ frontier Ω, u x ≤ 0) (n : ℕ) :
    smoothTestSpace Ω :=
  ⟨cut Ω u n, cut_contDiff ho hu hb n, cut_hasCompactSupport hu.continuousOn hbound n,
    cut_tsupport_subset ho hu.continuousOn hb n⟩
lemma cut_gradient (ho : IsOpen Ω) (hu : ContDiffOn ℝ ∞ u (closure Ω))
    (n : ℕ) {x : Plane} (hx : x ∈ Ω) :
    gradient (cut Ω u n) x = deriv (Nodal.cutoff n) (u x) • gradient u x := by
  apply (InnerProductSpace.toDual ℝ Plane).injective
  simp only [gradient,map_smul]
  rw [(cut_eq_nhds ho n hx).fderiv_eq]
  simp only [LinearIsometryEquiv.apply_symm_apply]
  exact (((Nodal.cutoff_contDiff n).differentiable (by simp)).differentiableAt.hasDerivAt.comp_hasFDerivAt x
    (((hu.mono subset_closure).contDiffAt (ho.mem_nhds hx)).differentiableAt (by simp)).hasFDerivAt).fderiv

lemma gap_test (ho : IsOpen Ω) (hu : InFirstNeumannEigenspace Ω u)
    (hbound : Bornology.IsBounded Ω) (hb : ∀ x ∈ frontier Ω, u x ≤ 0)
    {lam : ℝ} (hg : ∀ v : H10 ho, lam * ‖H10.value ho v‖^2 ≤ ‖H10.grad ho v‖^2)
    (n : ℕ) :
    lam * (∫ x in Ω, (Nodal.cutoff n (u x))^2) ≤
      ∫ x in Ω, (deriv (Nodal.cutoff n) (u x))^2 * ‖gradient u x‖^2 := by
  let f := test ho hu.1 hbound hb n
  have hh := hg (smoothTestToH10 ho f)
  change lam * ‖(HasH1Gradient.test ho f.property.1 f.property.2.1).1.toLp f.val‖^2 ≤
    ‖(HasH1Gradient.test ho f.property.1 f.property.2.1).2.1.toLp (gradient f.val)‖^2 at hh
  rw [← real_inner_self_eq_norm_sq, ← real_inner_self_eq_norm_sq,
    L2Inner.toLp_pair,L2Inner.toLp_pair] at hh
  have hval : (∫ x in Ω, inner ℝ (f.val x) (f.val x)) = ∫ x in Ω, (Nodal.cutoff n (u x))^2 := by
    apply setIntegral_congr_fun ho.measurableSet
    intro x hx
    simp only [f,test,cut,indicator_of_mem hx,RCLike.inner_apply,conj_trivial,pow_two]
  have hgrad : (∫ x in Ω, inner ℝ (gradient f.val x) (gradient f.val x)) =
      ∫ x in Ω, (deriv (Nodal.cutoff n) (u x))^2 * ‖gradient u x‖^2 := by
    apply setIntegral_congr_fun ho.measurableSet
    intro x hx
    dsimp only
    rw [real_inner_self_eq_norm_sq]
    change ‖gradient (cut Ω u n) x‖^2 = _
    rw [cut_gradient ho hu.1 n hx,norm_smul,mul_pow,Real.norm_eq_abs,sq_abs]
  rwa [hval,hgrad] at hh

lemma equation_test (ho : IsOpen Ω) (hu : InFirstNeumannEigenspace Ω u)
    (hbound : Bornology.IsBounded Ω) (hb : ∀ x ∈ frontier Ω, u x ≤ 0) (n : ℕ) :
    (∫ x in Ω, deriv (Nodal.cutoff n) (u x) * ‖gradient u x‖^2) =
      firstPositiveNeumannValue Ω * (∫ x in Ω, u x * Nodal.cutoff n (u x)) := by
  let f := test ho hu.1 hbound hb n
  have hh := hu.2.2.2 f.val (gradient f.val) (HasH1Gradient.test ho f.property.1 f.property.2.1)
  convert hh using 1
  · apply setIntegral_congr_fun ho.measurableSet
    intro x hx
    change _ = inner ℝ (gradient u x) (gradient (cut Ω u n) x)
    rw [cut_gradient ho hu.1 n hx,inner_smul_right,real_inner_self_eq_norm_sq]
  · congr 1
    apply setIntegral_congr_fun ho.measurableSet
    intro x hx
    simp only [f,test,cut,indicator_of_mem hx]
end StrictHotSpots.BoundarySign
end BoundarySignTestsCombinedLayer

section BoundarySignLimitsCombinedLayer
open Set Filter MeasureTheory
open scoped Topology ENNReal
namespace StrictHotSpots.Nodal
lemma cutoff_nonpos (n : ℕ) {t : ℝ} (h : t ≤ 0) : cutoff n t = 0 :=
  cutoff_zero n (lt_of_le_of_lt h (by positivity))
lemma cutoff_deriv_nonpos (n : ℕ) {t : ℝ} (h : t ≤ 0) : deriv (cutoff n) t = 0 := by
  have he : cutoff n =ᶠ[𝓝 t] (fun _ => (0:ℝ)) := by
    filter_upwards [gt_mem_nhds (show t < 1 / ((n:ℝ)+1) from lt_of_le_of_lt h (by positivity))] with y hy
    exact cutoff_zero n hy
  rw [he.deriv_eq]
  simp
lemma cutoff_tendsto (t : ℝ) : Tendsto (fun n => cutoff n t) atTop (𝓝 (if 0 < t then t else 0)) := by
  by_cases ht : 0 < t
  · rw [ite_eq_left ht]
    exact tendsto_const_nhds.congr' ((cutoff_eventually_eq ht).mono fun _ h => h.1.symm)
  · simp only [ite_eq_right ht,cutoff_nonpos _ (le_of_not_gt ht)]
    exact tendsto_const_nhds
lemma cutoff_deriv_tendsto (t : ℝ) :
    Tendsto (fun n => deriv (cutoff n) t) atTop (𝓝 (if 0 < t then (1:ℝ) else 0)) := by
  by_cases ht : 0 < t
  · rw [ite_eq_left ht]
    exact tendsto_const_nhds.congr' ((cutoff_eventually_eq ht).mono fun _ h => h.2.symm)
  · simp only [ite_eq_right ht,cutoff_deriv_nonpos _ (le_of_not_gt ht)]
    exact tendsto_const_nhds
variable {α : Type*} [MeasurableSpace α] {μ : Measure α} {u : α → ℝ}
lemma cutoff_square_integral (hu : MemLp u 2 μ) :
    Tendsto (fun n => ∫ x, (cutoff n (u x))^2 ∂μ) atTop
      (𝓝 (∫ x, if 0 < u x then (u x)^2 else 0 ∂μ)) := by
  apply tendsto_integral_of_dominated_convergence (fun x => (u x)^2)
  · intro n
    exact ((cutoff_contDiff n).continuous.comp_aestronglyMeasurable hu.aestronglyMeasurable).pow 2
  · exact hu.integrable_sq
  · intro n
    exact Eventually.of_forall fun x => by
      rw [Real.norm_of_nonneg (sq_nonneg _)]
      simpa only [Real.norm_eq_abs,sq_abs] using
        pow_le_pow_left₀ (norm_nonneg _) (cutoff_norm_le n (u x)) 2
  · exact Eventually.of_forall fun x => by
      simpa only [ite_pow,zero_pow (by decide : 2 ≠ 0)] using (cutoff_tendsto (u x)).pow 2
lemma cutoff_product_integral (hu : MemLp u 2 μ) :
    Tendsto (fun n => ∫ x, u x * cutoff n (u x) ∂μ) atTop
      (𝓝 (∫ x, if 0 < u x then (u x)^2 else 0 ∂μ)) := by
  apply tendsto_integral_of_dominated_convergence (fun x => (u x)^2)
  · intro n
    exact hu.aestronglyMeasurable.mul
      ((cutoff_contDiff n).continuous.comp_aestronglyMeasurable hu.aestronglyMeasurable)
  · exact hu.integrable_sq
  · intro n
    exact Eventually.of_forall fun x => by
      rw [norm_mul]
      calc
        ‖u x‖ * ‖cutoff n (u x)‖ ≤ ‖u x‖ * ‖u x‖ :=
          mul_le_mul_of_nonneg_left (cutoff_norm_le n _) (norm_nonneg _)
        _ = (u x)^2 := by rw [← pow_two,Real.norm_eq_abs,sq_abs]
  · exact Eventually.of_forall fun x => by
      simpa only [mul_ite,mul_zero,← pow_two] using
        (tendsto_const_nhds : Tendsto (fun _ : ℕ => u x) atTop (𝓝 (u x))).mul (cutoff_tendsto (u x))
lemma cutoff_deriv_integral (hu : AEStronglyMeasurable u μ) {g : α → ℝ}
    (hg : Integrable g μ) (hgn : ∀ x, 0 ≤ g x) :
    Tendsto (fun n => ∫ x, deriv (cutoff n) (u x) * g x ∂μ) atTop
      (𝓝 (∫ x, if 0 < u x then g x else 0 ∂μ)) := by
  obtain ⟨C,hC,hbd⟩ := cutoff_deriv_bound
  apply tendsto_integral_of_dominated_convergence (fun x => C * g x)
  · intro n
    exact (((cutoff_contDiff n).continuous_deriv (by simp)).comp_aestronglyMeasurable hu).mul
      hg.aestronglyMeasurable
  · exact hg.const_mul C
  · intro n
    exact Eventually.of_forall fun x => by
      rw [norm_mul,Real.norm_of_nonneg (hgn x)]
      exact mul_le_mul_of_nonneg_right (hbd n _) (hgn x)
  · exact Eventually.of_forall fun x => by
      simpa only [ite_mul,one_mul,zero_mul] using (cutoff_deriv_tendsto (u x)).mul tendsto_const_nhds
lemma cutoff_deriv_square_integral (hu : AEStronglyMeasurable u μ) {g : α → ℝ}
    (hg : Integrable g μ) (hgn : ∀ x, 0 ≤ g x) :
    Tendsto (fun n => ∫ x, (deriv (cutoff n) (u x))^2 * g x ∂μ) atTop
      (𝓝 (∫ x, if 0 < u x then g x else 0 ∂μ)) := by
  obtain ⟨C,hC,hbd⟩ := cutoff_deriv_bound
  apply tendsto_integral_of_dominated_convergence (fun x => C^2 * g x)
  · intro n
    exact ((((cutoff_contDiff n).continuous_deriv (by simp)).comp_aestronglyMeasurable hu).pow 2).mul
      hg.aestronglyMeasurable
  · exact hg.const_mul (C^2)
  · intro n
    exact Eventually.of_forall fun x => by
      rw [norm_mul,Real.norm_of_nonneg (hgn x),norm_pow]
      exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) (hbd n _) 2) (hgn x)
  · exact Eventually.of_forall fun x => by
      simpa only [ite_pow,one_pow,zero_pow (by decide : 2 ≠ 0),ite_mul,one_mul,zero_mul] using
        ((cutoff_deriv_tendsto (u x)).pow 2).mul tendsto_const_nhds
end StrictHotSpots.Nodal
end BoundarySignLimitsCombinedLayer

section NodalRestrictionWeightedCombinedLayer

open Set Filter MeasureTheory Metric
open scoped Topology ContDiff InnerProductSpace
namespace StrictHotSpots.Nodal

variable {Ω U : Set Plane} {u : Plane → ℝ}

lemma cutoff_indicator_zero_nhds (hΩ : IsOpen Ω) (hu : ContinuousOn u Ω)
    (hU : IsOpen U) (hf : ∀ x ∈ frontier U ∩ Ω, u x = 0)
    (n : ℕ) {x : Plane} (hx : x ∈ Ω) (hxU : x ∉ U) :
    U.indicator (fun y => cutoff n (u y)) =ᶠ[𝓝 x] 0 := by
  by_cases hxc : x ∈ closure U
  · have hux : u x = 0 := hf x ⟨⟨hxc,by simpa [hU.interior_eq] using hxU⟩,hx⟩
    have hε : u x < 1/((n:ℝ)+1) := by rw [hux]; positivity
    filter_upwards [((hu x hx).continuousAt (hΩ.mem_nhds hx)).eventually (gt_mem_nhds hε)] with y hy
    by_cases hyU : y ∈ U
    · simp only [Pi.zero_apply,indicator_of_mem hyU,cutoff_zero n hy]
    · simp only [Pi.zero_apply,indicator_of_notMem hyU]
  · filter_upwards [isClosed_closure.isOpen_compl.mem_nhds hxc] with y hy
    exact indicator_of_notMem (fun hyU => hy (subset_closure hyU)) _

lemma cutoff_indicator_contDiffOn (hΩ : IsOpen Ω) (hu : ContDiffOn ℝ ∞ u Ω)
    (hU : IsOpen U) (hf : ∀ x ∈ frontier U ∩ Ω, u x = 0) (n : ℕ) :
    ContDiffOn ℝ ∞ (U.indicator (fun x => cutoff n (u x))) Ω := by
  intro x hx
  apply ContDiffAt.contDiffWithinAt
  by_cases hxU : x ∈ U
  · apply ((cutoff_contDiff n).contDiffAt.comp x (hu.contDiffAt (hΩ.mem_nhds hx))).congr_of_eventuallyEq
    filter_upwards [hU.mem_nhds hxU] with y hy
    exact indicator_of_mem hy _
  · exact contDiffAt_const.congr_of_eventuallyEq (cutoff_indicator_zero_nhds hΩ hu.continuousOn hU hf n hx hxU)

lemma cutoff_indicator_fderiv (hΩ : IsOpen Ω) (hu : ContDiffOn ℝ ∞ u Ω)
    (hU : IsOpen U) (hf : ∀ x ∈ frontier U ∩ Ω, u x = 0) (n : ℕ)
    {x : Plane} (hx : x ∈ Ω) :
    fderiv ℝ (U.indicator (fun y => cutoff n (u y))) x =
      U.indicator (fun y => (deriv (cutoff n) (u y)) • fderiv ℝ u y) x := by
  by_cases hxU : x ∈ U
  · rw [indicator_of_mem hxU]
    have he : U.indicator (fun y => cutoff n (u y)) =ᶠ[𝓝 x] (fun y => cutoff n (u y)) := by
      filter_upwards [hU.mem_nhds hxU] with y hy
      exact indicator_of_mem hy _
    rw [he.fderiv_eq]
    exact (((cutoff_contDiff n).differentiable (by simp)).differentiableAt.hasDerivAt.comp_hasFDerivAt x
      ((hu.contDiffAt (hΩ.mem_nhds hx)).differentiableAt (by simp)).hasFDerivAt).fderiv
  · rw [indicator_of_notMem hxU,(cutoff_indicator_zero_nhds hΩ hu.continuousOn hU hf n hx hxU).fderiv_eq]
    exact (hasFDerivAt_const (𝕜 := ℝ) (0 : ℝ) x).fderiv

lemma cutoff_indicator_gradient (hΩ : IsOpen Ω) (hu : ContDiffOn ℝ ∞ u Ω)
    (hU : IsOpen U) (hf : ∀ x ∈ frontier U ∩ Ω, u x = 0) (n : ℕ)
    {x : Plane} (hx : x ∈ Ω) :
    gradient (U.indicator (fun y => cutoff n (u y))) x =
      U.indicator (fun y => (deriv (cutoff n) (u y)) • gradient u y) x := by
  apply (InnerProductSpace.toDual ℝ Plane).injective
  simp only [gradient]
  rw [cutoff_indicator_fderiv hΩ hu hU hf n hx]
  by_cases hxU : x ∈ U
  · simp only [indicator_of_mem hxU,map_smul]
  · simp only [indicator_of_notMem hxU,map_zero]

lemma cutoff_memLp (hU : IsOpen U) (hu : HasH1Gradient Ω u (gradient u)) (n : ℕ) :
    MemLp (U.indicator (fun x => cutoff n (u x))) 2 (volume.restrict Ω) := by
  apply hu.1.mono
    (((cutoff_contDiff n).continuous.comp_aestronglyMeasurable hu.1.aestronglyMeasurable).indicator hU.measurableSet)
  exact Eventually.of_forall fun x => by
    by_cases hx : x ∈ U
    · simpa only [indicator_of_mem hx] using cutoff_norm_le n (u x)
    · simp only [indicator_of_notMem hx,norm_zero]; exact norm_nonneg _

lemma cutoff_grad_memLp (hU : IsOpen U) (hu : HasH1Gradient Ω u (gradient u)) (n : ℕ) :
    MemLp (U.indicator (fun x => deriv (cutoff n) (u x) • gradient u x)) 2 (volume.restrict Ω) := by
  obtain ⟨C,hC,hbd⟩ := cutoff_deriv_bound
  apply (hu.2.1.norm.const_mul C).mono'
    ((((cutoff_contDiff n).continuous_deriv (by simp)).comp_aestronglyMeasurable
      hu.1.aestronglyMeasurable).smul hu.2.1.aestronglyMeasurable |>.indicator hU.measurableSet)
  exact Eventually.of_forall fun x => by
    by_cases hx : x ∈ U
    · rw [indicator_of_mem hx]
      change ‖deriv (cutoff n) (u x) • gradient u x‖ ≤ C * ‖gradient u x‖
      rw [norm_smul]
      exact mul_le_mul_of_nonneg_right (hbd n (u x)) (norm_nonneg (gradient u x))
    · rw [indicator_of_notMem hx,norm_zero]
      exact mul_nonneg (le_trans zero_le_one hC) (norm_nonneg _)

lemma cutoff_hasH1Gradient (hΩ : IsOpen Ω) (hu : ContDiffOn ℝ ∞ u Ω)
    (hH : HasH1Gradient Ω u (gradient u))
    (hU : IsOpen U) (hf : ∀ x ∈ frontier U ∩ Ω, u x = 0) (n : ℕ) :
    HasH1Gradient Ω (U.indicator (fun x => cutoff n (u x)))
      (U.indicator (fun x => deriv (cutoff n) (u x) • gradient u x)) := by
  have heq : gradient (U.indicator (fun x => cutoff n (u x))) =ᵐ[volume.restrict Ω]
      U.indicator (fun x => deriv (cutoff n) (u x) • gradient u x) :=
    (ae_restrict_iff' hΩ.measurableSet).mpr (Eventually.of_forall fun x hx =>
      cutoff_indicator_gradient hΩ hu hU hf n hx)
  have hg := (memLp_congr_ae heq).mpr (cutoff_grad_memLp hU hH n)
  have hh := HasH1Gradient.of_contDiffOn hΩ (cutoff_indicator_contDiffOn hΩ hu hU hf n)
    (cutoff_memLp hU hH n) hg
  refine ⟨hh.1,cutoff_grad_memLp hU hH n,?_⟩
  intro φ hφ hc hs e
  rw [hh.2.2 φ hφ hc hs e]
  congr 1
  apply integral_congr_ae
  filter_upwards [heq] with x hx
  rw [hx]



lemma hasH1Gradient_indicator (hΩ : IsOpen Ω) (hu : ContDiffOn ℝ ∞ u Ω)
    (hH : HasH1Gradient Ω u (gradient u)) (hU : IsOpen U)
    (hf : ∀ x ∈ frontier U ∩ Ω, u x = 0) (hpos : ∀ x ∈ U, 0 < u x) :
    HasH1Gradient Ω (U.indicator u) (U.indicator (gradient u)) := by
  refine ⟨MemLp.indicator hU.measurableSet hH.1,
    MemLp.indicator hU.measurableSet hH.2.1,?_⟩
  intro φ hφ hc hs e
  let F (n : ℕ) := U.indicator (fun x => cutoff n (u x))
  let G (n : ℕ) := U.indicator (fun x => deriv (cutoff n) (u x) • gradient u x)
  have hmF (n : ℕ) := cutoff_memLp hU hH n
  have hmG (n : ℕ) := cutoff_grad_memLp hU hH n
  have hlimF (x : Plane) : Tendsto (fun n => F n x) atTop (𝓝 (U.indicator u x)) := by
    by_cases hx : x ∈ U
    · apply tendsto_const_nhds.congr'
      filter_upwards [cutoff_eventually_eq (hpos x hx)] with n hn
      simp only [F,indicator_of_mem hx,hn.1]
    · simpa only [F,indicator_of_notMem hx] using (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0:ℝ)) atTop (𝓝 0))
  have hlimG (x : Plane) : Tendsto (fun n => G n x) atTop (𝓝 (U.indicator (gradient u) x)) := by
    by_cases hx : x ∈ U
    · apply tendsto_const_nhds.congr'
      filter_upwards [cutoff_eventually_eq (hpos x hx)] with n hn
      simp only [G,indicator_of_mem hx,hn.2,one_smul]
    · simpa only [G,indicator_of_notMem hx] using (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0:Plane)) atTop (𝓝 0))
  have hL := tendsto_integral_of_dominated_convergence (μ := volume.restrict Ω)
    (fun x => ‖u x‖ * ‖fderiv ℝ φ x e‖)
    (fun n => (hmF n).aestronglyMeasurable.mul (test_derivative_memLp hφ hc e).aestronglyMeasurable)
    (hH.1.norm.integrable_mul (test_derivative_memLp hφ hc e).norm)
    (fun n => Eventually.of_forall fun x => by
      simp only [Pi.mul_apply,norm_mul]
      apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
      by_cases hx : x ∈ U
      · simpa only [F,indicator_of_mem hx] using cutoff_norm_le n (u x)
      · simp only [indicator_of_notMem hx,norm_zero]; exact norm_nonneg _)
    (Eventually.of_forall fun x => (hlimF x).mul tendsto_const_nhds)
  obtain ⟨C,hC,hbd⟩ := cutoff_deriv_bound
  have hR := tendsto_integral_of_dominated_convergence (μ := volume.restrict Ω)
    (fun x => C * ‖gradient u x‖ * ‖e‖ * ‖φ x‖)
    (fun n => ((hmG n).aestronglyMeasurable.inner (aestronglyMeasurable_const (b := e))).mul
      (test_memLp hφ hc).aestronglyMeasurable)
    (((hH.2.1.norm.const_mul C).mul_const ‖e‖).integrable_mul (test_memLp hφ hc).norm)
    (fun n => Eventually.of_forall fun x => by
      simp only [Pi.mul_apply,norm_mul]
      apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
      apply le_trans (norm_inner_le_norm _ _) (mul_le_mul_of_nonneg_right ?_ (norm_nonneg e))
      by_cases hx : x ∈ U
      · simp only [indicator_of_mem hx,norm_smul]
        exact mul_le_mul_of_nonneg_right (hbd n (u x)) (norm_nonneg _)
      · simp only [indicator_of_notMem hx,norm_zero]
        exact mul_nonneg (le_trans zero_le_one hC) (norm_nonneg _))
    (Eventually.of_forall fun x => ((hlimG x).inner tendsto_const_nhds).mul tendsto_const_nhds)
  apply tendsto_nhds_unique hL
  convert hR.neg using 1
  ext n
  exact (cutoff_hasH1Gradient hΩ hu hH hU hf n).2.2 φ hφ hc hs e

lemma positive_set_open (hΩ : IsOpen Ω) (hu : ContinuousOn u Ω) :
    IsOpen (Ω ∩ {x | 0 < u x}) := by
  exact hu.isOpen_inter_preimage hΩ isOpen_Ioi

lemma positive_component_frontier_zero (hΩ : IsOpen Ω) (hu : ContinuousOn u Ω)
    (a : Plane) {x : Plane} (hx : x ∈ frontier (connectedComponentIn (Ω ∩ {x | 0 < u x}) a) ∩ Ω) : u x = 0 := by
  let P := Ω ∩ {x | 0 < u x}
  let U := connectedComponentIn P a
  have hP : IsOpen P := positive_set_open hΩ hu
  have hU : IsOpen U := hP.connectedComponentIn
  have hxc : x ∈ closure U := hx.1.1
  have hxU : x ∉ U := by
    have hh : x ∉ interior U := hx.1.2
    simpa only [hU.interior_eq] using hh
  have hux : ContinuousAt u x := (hu x hx.2).continuousAt (hΩ.mem_nhds hx.2)
  have hnonneg : 0 ≤ u x := by
    by_contra h
    have hneg : u x < 0 := lt_of_not_ge h
    have hn : {y | u y < 0} ∈ 𝓝 x := hux.eventually (gt_mem_nhds hneg)
    obtain ⟨ε,hε,he⟩ := Metric.mem_nhds_iff.mp hn
    obtain ⟨y,hy,hd⟩ := Metric.mem_closure_iff.mp hxc ε hε
    have hyneg : u y < 0 := he (by simpa [mem_ball,dist_comm] using hd)
    have hypos : 0 < u y := (connectedComponentIn_subset P a hy).2
    linarith
  apply le_antisymm _ hnonneg
  by_contra h
  have hpos : 0 < u x := lt_of_not_ge h
  obtain ⟨ε,hε,he⟩ := Metric.mem_nhds_iff.mp (hP.mem_nhds ⟨hx.2,hpos⟩)
  obtain ⟨y,hy,hd⟩ := Metric.mem_closure_iff.mp hxc ε hε
  have hyball : y ∈ ball x ε := by simpa [mem_ball,dist_comm] using hd
  have hbsub : ball x ε ⊆ connectedComponentIn P y :=
    (convex_ball x ε).isPreconnected.subset_connectedComponentIn hyball he
  rw [← connectedComponentIn_eq hy] at hbsub
  exact hxU (hbsub (mem_ball_self hε))

lemma positive_component_hasH1Gradient (hΩ : IsOpen Ω) (hu : ContDiffOn ℝ ∞ u Ω)
    (hH : HasH1Gradient Ω u (gradient u)) (a : Plane) :
    HasH1Gradient Ω ((connectedComponentIn (Ω ∩ {x | 0 < u x}) a).indicator u)
      ((connectedComponentIn (Ω ∩ {x | 0 < u x}) a).indicator (gradient u)) := by
  apply hasH1Gradient_indicator hΩ hu hH (positive_set_open hΩ hu.continuousOn).connectedComponentIn
  · exact fun x hx => positive_component_frontier_zero hΩ hu.continuousOn a hx
  · intro x hx
    exact (connectedComponentIn_subset _ a hx).2

end StrictHotSpots.Nodal
end NodalRestrictionWeightedCombinedLayer

section SmoothZeroTraceCombinedLayer
open Set Filter MeasureTheory Metric
open scoped Topology ContDiff InnerProductSpace
namespace StrictHotSpots

lemma positive_region_frontier_zero {Ω : Set Plane} {u : Plane → ℝ}
    (ho : IsOpen Ω) (hu : ContinuousOn u Ω) {x : Plane}
    (hx : x ∈ frontier (Ω ∩ {x | 0 < u x}) ∩ Ω) : u x = 0 := by
  have hc := hu.continuousAt (ho.mem_nhds hx.2)
  have hP := Nodal.positive_set_open ho hu
  have hn : x ∉ Ω ∩ {x | 0 < u x} := by simpa only [hP.interior_eq] using hx.1.2
  have hle : u x ≤ 0 := le_of_not_gt (fun hp => hn ⟨hx.2,hp⟩)
  apply le_antisymm hle
  by_contra hp
  have he : ∀ᶠ y in 𝓝 x, u y < 0 := hc.eventually (gt_mem_nhds (lt_of_not_ge hp))
  have hh := (mem_closure_iff_frequently.mp hx.1.1).and_eventually he
  obtain ⟨y,hy,huy⟩ := hh.exists
  exact (not_lt_of_gt hy.2) huy

lemma positive_part_gradient {Ω : Set Plane} {u : Plane → ℝ}
    (ho : IsOpen Ω) (hu : ContDiffOn ℝ ∞ u Ω)
    (hH : HasH1Gradient Ω u (gradient u)) :
    HasH1Gradient Ω ((Ω ∩ {x | 0 < u x}).indicator u)
      ((Ω ∩ {x | 0 < u x}).indicator (gradient u)) :=
  Nodal.hasH1Gradient_indicator ho hu hH (Nodal.positive_set_open ho hu.continuousOn)
    (fun _ hx => positive_region_frontier_zero ho hu.continuousOn hx) (fun _ hx => hx.2)

lemma positive_part_memH10 {Ω : Set Plane} {u : Plane → ℝ}
    (ho : IsOpen Ω) (hu : ContDiffOn ℝ ∞ u (closure Ω))
    (hH : HasH1Gradient Ω u (gradient u)) (hb : Bornology.IsBounded Ω)
    (hz : ∀ x ∈ frontier Ω, u x ≤ 0) :
    (positive_part_gradient ho (hu.mono subset_closure) hH).toH1 ∈ h10Submodule ho := by
  let P := Ω ∩ {x | 0 < u x}
  let hv := positive_part_gradient ho (hu.mono subset_closure) hH
  let f (n : ℕ) := BoundarySign.test ho hu hb hz n
  have hvlim : Tendsto (fun n => H1.value (smoothTestToH1 ho (f n))) atTop (𝓝 (H1.value hv.toH1)) := by
    apply L2VectorLimits.tendsto_toLp_of_dominated
      (fun n => (HasH1Gradient.test ho (f n).property.1 (f n).property.2.1).1) hv.1 hH.1.norm
    · exact Eventually.of_forall fun n => by
        filter_upwards [ae_restrict_mem ho.measurableSet] with x hx
        change ‖BoundarySign.cut Ω u n x‖ ≤ ‖u x‖
        simpa only [BoundarySign.cut,indicator_of_mem hx] using Nodal.cutoff_norm_le n (u x)
    · filter_upwards [ae_restrict_mem ho.measurableSet] with x hx
      change Tendsto (fun n => BoundarySign.cut Ω u n x) atTop (𝓝 (P.indicator u x))
      simp only [BoundarySign.cut,indicator_of_mem hx]
      simpa only [P,indicator,mem_inter_iff,mem_ofPred_eq,hx,true_and] using Nodal.cutoff_tendsto (u x)
  obtain ⟨C,hC,hbd⟩ := Nodal.cutoff_deriv_bound
  have hglim : Tendsto (fun n => H1.grad (smoothTestToH1 ho (f n))) atTop (𝓝 (H1.grad hv.toH1)) := by
    apply L2VectorLimits.tendsto_toLp_of_dominated
      (fun n => (HasH1Gradient.test ho (f n).property.1 (f n).property.2.1).2.1)
      hv.2.1 (hH.2.1.norm.const_mul C)
    · exact Eventually.of_forall fun n => by
        filter_upwards [ae_restrict_mem ho.measurableSet] with x hx
        change ‖gradient (BoundarySign.cut Ω u n) x‖ ≤ C*‖gradient u x‖
        rw [BoundarySign.cut_gradient ho hu n hx,norm_smul]
        exact mul_le_mul_of_nonneg_right (hbd n (u x)) (norm_nonneg _)
    · filter_upwards [ae_restrict_mem ho.measurableSet] with x hx
      change Tendsto (fun n => gradient (BoundarySign.cut Ω u n) x) atTop
        (𝓝 (P.indicator (gradient u) x))
      simp_rw [BoundarySign.cut_gradient ho hu _ hx]
      simpa only [P,indicator,mem_inter_iff,mem_ofPred_eq,hx,true_and,ite_smul,one_smul,zero_smul] using
        (Nodal.cutoff_deriv_tendsto (u x)).smul_const (gradient u x)
  change hv.toH1 ∈ closure ((smoothTestToH1 ho).range : Set (H1 Ω))
  exact mem_closure_of_tendsto (H1.tendsto_of_value_grad hvlim hglim)
    (Eventually.of_forall fun n => ⟨f n,rfl⟩)




theorem smooth_zero_trace_memH10 {Ω : Set Plane} {u : Plane → ℝ}
    (ho : IsOpen Ω) (hu : ContDiffOn ℝ ∞ u (closure Ω))
    (hH : HasH1Gradient Ω u (gradient u)) (hb : Bornology.IsBounded Ω)
    (hz : ∀ x ∈ frontier Ω, u x = 0) : hH.toH1 ∈ h10Submodule ho := by
  have hg : gradient (-u) = -gradient u := by
    funext x
    simp only [gradient,Pi.neg_apply,fderiv_neg,map_neg]
  have hn : HasH1Gradient Ω (-u) (gradient (-u)) := by
    simpa only [hg,neg_one_smul] using hH.smul (-1)
  let vp := positive_part_gradient ho (hu.mono subset_closure) hH
  let vn := positive_part_gradient ho (hu.neg.mono subset_closure) hn
  have hp := positive_part_memH10 ho hu hH hb (fun x hx => (hz x hx).le)
  have hq := positive_part_memH10 ho hu.neg hn hb (fun x hx => by simp only [hz x hx,neg_zero,le_refl])
  have he : hH.toH1 = vp.toH1-vn.toH1 := by
    apply H1.value_injective ho
    rw [map_sub,H1.value_toH1,H1.value_toH1,H1.value_toH1]
    apply Lp.ext
    filter_upwards [hH.1.coeFn_toLp,vp.1.coeFn_toLp,vn.1.coeFn_toLp,
      Lp.coeFn_sub (vp.1.toLp _) (vn.1.toLp _),ae_restrict_mem ho.measurableSet] with x hx hpx hnx hsub hxΩ
    rw [hsub,Pi.sub_apply,hx,hpx,hnx]
    change u x = (Ω ∩ {x | 0 < u x}).indicator u x -
      (Ω ∩ {x | 0 < (-u) x}).indicator (-u) x
    by_cases h : 0 < u x
    · have hn' : ¬0 < -u x := by linarith
      simp only [indicator,mem_inter_iff,hxΩ,mem_ofPred_eq,true_and,Pi.neg_apply,h,hn',ite_true,ite_false,sub_zero]
    · by_cases h' : u x < 0
      · have hn' : 0 < -u x := neg_pos.mpr h'
        simp only [indicator,mem_inter_iff,hxΩ,mem_ofPred_eq,true_and,Pi.neg_apply,h,hn',ite_true,ite_false,zero_sub,neg_neg]
      · have hx0 : u x = 0 := le_antisymm (le_of_not_gt h) (le_of_not_gt h')
        simp [indicator,hx0]
  rw [he]
  exact (h10Submodule ho).sub_mem hp hq
end StrictHotSpots
end SmoothZeroTraceCombinedLayer

section ContinuousZeroTraceCombinedLayer
open Set Filter MeasureTheory Metric
open scoped Topology ContDiff InnerProductSpace
namespace StrictHotSpots
namespace BoundarySign
variable {Ω : Set Plane} {u : Plane → ℝ}
lemma cut_contDiff_interior (ho : IsOpen Ω) (hu : ContDiffOn ℝ ∞ u Ω) (hc : ContinuousOn u (closure Ω))
    (hb : ∀ x ∈ frontier Ω, u x ≤ 0) (n : ℕ) : ContDiff ℝ ∞ (cut Ω u n) := by
  rw [contDiff_iff_contDiffAt]
  intro x
  by_cases hx : x ∈ Ω
  · exact ((Nodal.cutoff_contDiff n).contDiffAt.comp x
      (hu.contDiffAt (ho.mem_nhds hx))).congr_of_eventuallyEq
      (cut_eq_nhds ho n hx)
  · exact contDiffAt_const.congr_of_eventuallyEq
      (cut_eq_zero_nhds hc n (fun h => hx (cutSupport_subset ho hb n h)))
def test_interior (ho : IsOpen Ω) (hu : ContDiffOn ℝ ∞ u Ω)
    (hc : ContinuousOn u (closure Ω)) (hbound : Bornology.IsBounded Ω) (hb : ∀ x ∈ frontier Ω, u x ≤ 0) (n : ℕ) :
    smoothTestSpace Ω :=
  ⟨cut Ω u n, cut_contDiff_interior ho hu hc hb n, cut_hasCompactSupport hc hbound n,
    cut_tsupport_subset ho hc hb n⟩
lemma cut_gradient_interior (ho : IsOpen Ω) (hu : ContDiffOn ℝ ∞ u Ω)
    (n : ℕ) {x : Plane} (hx : x ∈ Ω) :
    gradient (cut Ω u n) x = deriv (Nodal.cutoff n) (u x) • gradient u x := by
  apply (InnerProductSpace.toDual ℝ Plane).injective
  simp only [gradient,map_smul]
  rw [(cut_eq_nhds ho n hx).fderiv_eq]
  simp only [LinearIsometryEquiv.apply_symm_apply]
  exact (((Nodal.cutoff_contDiff n).differentiable (by simp)).differentiableAt.hasDerivAt.comp_hasFDerivAt x
    ((hu.contDiffAt (ho.mem_nhds hx)).differentiableAt (by simp)).hasFDerivAt).fderiv

end BoundarySign
lemma positive_part_memH10_interior {Ω : Set Plane} {u : Plane → ℝ}
    (ho : IsOpen Ω) (hu : ContDiffOn ℝ ∞ u Ω) (hc : ContinuousOn u (closure Ω))
    (hH : HasH1Gradient Ω u (gradient u)) (hb : Bornology.IsBounded Ω)
    (hz : ∀ x ∈ frontier Ω, u x ≤ 0) :
    (positive_part_gradient ho hu hH).toH1 ∈ h10Submodule ho := by
  let P := Ω ∩ {x | 0 < u x}
  let hv := positive_part_gradient ho hu hH
  let f (n : ℕ) := BoundarySign.test_interior ho hu hc hb hz n
  have hvlim : Tendsto (fun n => H1.value (smoothTestToH1 ho (f n))) atTop (𝓝 (H1.value hv.toH1)) := by
    apply L2VectorLimits.tendsto_toLp_of_dominated
      (fun n => (HasH1Gradient.test ho (f n).property.1 (f n).property.2.1).1) hv.1 hH.1.norm
    · exact Eventually.of_forall fun n => by
        filter_upwards [ae_restrict_mem ho.measurableSet] with x hx
        change ‖BoundarySign.cut Ω u n x‖ ≤ ‖u x‖
        simpa only [BoundarySign.cut,indicator_of_mem hx] using Nodal.cutoff_norm_le n (u x)
    · filter_upwards [ae_restrict_mem ho.measurableSet] with x hx
      change Tendsto (fun n => BoundarySign.cut Ω u n x) atTop (𝓝 (P.indicator u x))
      simp only [BoundarySign.cut,indicator_of_mem hx]
      simpa only [P,indicator,mem_inter_iff,mem_ofPred_eq,hx,true_and] using Nodal.cutoff_tendsto (u x)
  obtain ⟨C,hC,hbd⟩ := Nodal.cutoff_deriv_bound
  have hglim : Tendsto (fun n => H1.grad (smoothTestToH1 ho (f n))) atTop (𝓝 (H1.grad hv.toH1)) := by
    apply L2VectorLimits.tendsto_toLp_of_dominated
      (fun n => (HasH1Gradient.test ho (f n).property.1 (f n).property.2.1).2.1)
      hv.2.1 (hH.2.1.norm.const_mul C)
    · exact Eventually.of_forall fun n => by
        filter_upwards [ae_restrict_mem ho.measurableSet] with x hx
        change ‖gradient (BoundarySign.cut Ω u n) x‖ ≤ C*‖gradient u x‖
        rw [BoundarySign.cut_gradient_interior ho hu n hx,norm_smul]
        exact mul_le_mul_of_nonneg_right (hbd n (u x)) (norm_nonneg _)
    · filter_upwards [ae_restrict_mem ho.measurableSet] with x hx
      change Tendsto (fun n => gradient (BoundarySign.cut Ω u n) x) atTop
        (𝓝 (P.indicator (gradient u) x))
      simp_rw [BoundarySign.cut_gradient_interior ho hu _ hx]
      simpa only [P,indicator,mem_inter_iff,mem_ofPred_eq,hx,true_and,ite_smul,one_smul,zero_smul] using
        (Nodal.cutoff_deriv_tendsto (u x)).smul_const (gradient u x)
  change hv.toH1 ∈ closure ((smoothTestToH1 ho).range : Set (H1 Ω))
  exact mem_closure_of_tendsto (H1.tendsto_of_value_grad hvlim hglim)
    (Eventually.of_forall fun n => ⟨f n,rfl⟩)

theorem interior_smooth_zero_trace_memH10 {Ω : Set Plane} {u : Plane → ℝ}
    (ho : IsOpen Ω) (hu : ContDiffOn ℝ ∞ u Ω) (hc : ContinuousOn u (closure Ω))
    (hH : HasH1Gradient Ω u (gradient u)) (hb : Bornology.IsBounded Ω)
    (hz : ∀ x ∈ frontier Ω, u x = 0) : hH.toH1 ∈ h10Submodule ho := by
  have hg : gradient (-u) = -gradient u := by
    funext x
    simp only [gradient,Pi.neg_apply,fderiv_neg,map_neg]
  have hn : HasH1Gradient Ω (-u) (gradient (-u)) := by
    simpa only [hg,neg_one_smul] using hH.smul (-1)
  let vp := positive_part_gradient ho hu hH
  let vn := positive_part_gradient ho hu.neg hn
  have hp := positive_part_memH10_interior ho hu hc hH hb (fun x hx => (hz x hx).le)
  have hq := positive_part_memH10_interior ho hu.neg hc.neg hn hb (fun x hx => by simp only [hz x hx,neg_zero,le_refl])
  have he : hH.toH1 = vp.toH1-vn.toH1 := by
    apply H1.value_injective ho
    rw [map_sub,H1.value_toH1,H1.value_toH1,H1.value_toH1]
    apply Lp.ext
    filter_upwards [hH.1.coeFn_toLp,vp.1.coeFn_toLp,vn.1.coeFn_toLp,
      Lp.coeFn_sub (vp.1.toLp _) (vn.1.toLp _),ae_restrict_mem ho.measurableSet] with x hx hpx hnx hsub hxΩ
    rw [hsub,Pi.sub_apply,hx,hpx,hnx]
    change u x = (Ω ∩ {x | 0 < u x}).indicator u x -
      (Ω ∩ {x | 0 < (-u) x}).indicator (-u) x
    by_cases h : 0 < u x
    · have hn' : ¬0 < -u x := by linarith
      simp only [indicator,mem_inter_iff,hxΩ,mem_ofPred_eq,true_and,Pi.neg_apply,h,hn',ite_true,ite_false,sub_zero]
    · by_cases h' : u x < 0
      · have hn' : 0 < -u x := neg_pos.mpr h'
        simp only [indicator,mem_inter_iff,hxΩ,mem_ofPred_eq,true_and,Pi.neg_apply,h,hn',ite_true,ite_false,zero_sub,neg_neg]
      · have hx0 : u x = 0 := le_antisymm (le_of_not_gt h) (le_of_not_gt h')
        simp [indicator,hx0]
  rw [he]
  exact (h10Submodule ho).sub_mem hp hq
end StrictHotSpots
end ContinuousZeroTraceCombinedLayer


end

end DouglasLipschitzBase

end OAI
