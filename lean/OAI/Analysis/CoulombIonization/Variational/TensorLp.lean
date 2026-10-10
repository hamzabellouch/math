import Mathlib
import OAI.Analysis.CoulombIonization.Variational.SpinJoinEquiv
import OAI.Analysis.CoulombIonization.FormDomain.SobolevVector

namespace OAI

noncomputable section

namespace CoulombAtom

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
open MeasureTheory Filter
open scoped Topology BigOperators ContDiff InnerProductSpace Convolution
open Filter
open scoped Topology InnerProductSpace
open MeasureTheory Complex Filter
open scoped Topology InnerProductSpace
open MeasureTheory Complex Filter
open scoped Topology InnerProductSpace ContDiff
open MeasureTheory Filter
open scoped Topology BigOperators ContDiff InnerProductSpace Convolution
open MeasureTheory Filter
open scoped Topology BigOperators ContDiff InnerProductSpace
open MeasureTheory Filter
open scoped Topology BigOperators ContDiff InnerProductSpace ENNReal
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open Set Filter Topology InnerProductSpace Laplacian
open MeasureTheory Filter
open scoped Topology
open MeasureTheory Filter
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter
open scoped Topology BigOperators InnerProductSpace
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter
open scoped Topology BigOperators Pointwise
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric Topology InnerProductSpace Laplacian
open scoped Convolution
open scoped RealInnerProductSpace
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric Topology InnerProductSpace Laplacian
open MeasureTheory Filter Set Metric Topology InnerProductSpace Laplacian
open MeasureTheory Filter Set Metric Topology
open MeasureTheory Set Filter Metric Topology InnerProductSpace Laplacian
open MeasureTheory Set Filter Metric Topology InnerProductSpace Laplacian
open MeasureTheory Filter Set Metric Topology
open MeasureTheory Filter Set Metric Topology
open MeasureTheory Filter Set Metric Topology InnerProductSpace Laplacian
open Filter Set Metric Topology InnerProductSpace Laplacian
open MeasureTheory Filter Set Metric Topology
open MeasureTheory Filter Set Metric Topology
open MeasureTheory Filter Set Metric Topology
open MeasureTheory Filter Set Metric Topology
open Filter
open scoped Topology
open MeasureTheory Filter Set Metric Topology
open MeasureTheory Filter Set Metric Topology
open MeasureTheory Complex Filter
open scoped Topology InnerProductSpace ContDiff BigOperators
open MeasureTheory Filter Set
open scoped Topology BigOperators
open MeasureTheory Filter
open scoped Topology BigOperators InnerProductSpace
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open scoped BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff

section TensorLp
variable {E F : Type*} [MeasureSpace E] [MeasureSpace F]
  [SFinite (volume : Measure E)] [SFinite (volume : Measure F)]

omit [SFinite (volume : Measure E)] [SFinite (volume : Measure F)] in
lemma memLp_tensor_of_aemeasurable
    (hkernel : AEMeasurable
      (fun point : E => Measure.map (Prod.mk point) (volume : Measure F))
      (volume : Measure E))
    {f : E → ℂ} {g : F → ℂ} (hf : MemLp f 2) (hg : MemLp g 2) :
    MemLp (fun point : E × F => f point.1 * g point.2) 2 := by
  have hfst : Measure.QuasiMeasurePreserving (Prod.fst : E × F → E) volume volume := by
    refine ⟨measurable_fst, Measure.AbsolutelyContinuous.mk fun subset hsubset hzero => ?_⟩
    rw [Measure.map_apply measurable_fst hsubset, Measure.volume_eq_prod, Measure.prod,
      Measure.bind_apply (measurable_fst hsubset) hkernel]
    apply lintegral_eq_zero_of_ae_eq_zero
    filter_upwards [measure_eq_zero_iff_ae_notMem.mp hzero] with point hpoint
    rw [Measure.map_apply measurable_prodMk_left (measurable_fst hsubset)]
    have hempty : Prod.mk point ⁻¹' (Prod.fst ⁻¹' subset) = (∅ : Set F) := by
      ext other
      simp [hpoint]
    rw [hempty, measure_empty]
    rfl
  have hsnd : Measure.QuasiMeasurePreserving (Prod.snd : E × F → F) volume volume := by
    refine ⟨measurable_snd, Measure.AbsolutelyContinuous.mk fun subset hsubset hzero => ?_⟩
    rw [Measure.map_apply measurable_snd hsubset, Measure.volume_eq_prod, Measure.prod,
      Measure.bind_apply (measurable_snd hsubset) hkernel]
    apply lintegral_eq_zero_of_ae_eq_zero
    exact Filter.Eventually.of_forall fun point => by
      change (Measure.map (Prod.mk point) volume) (Prod.snd ⁻¹' subset) = 0
      rw [Measure.map_apply measurable_prodMk_left (measurable_snd hsubset)]
      exact hzero
  have hm : AEStronglyMeasurable (fun point : E × F => f point.1 * g point.2) :=
    (hf.aestronglyMeasurable.comp_quasiMeasurePreserving hfst).mul
      (hg.aestronglyMeasurable.comp_quasiMeasurePreserving hsnd)
  apply (eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top
    (p := 2) (by norm_num) (by simp) hm).mpr
  have hfinite_f : (∫⁻ point, ‖f point‖ₑ ^ (2 : ℕ)) < (∞ : ℝ≥0∞) := by
    simpa using lintegral_rpow_enorm_lt_top_of_eLpNorm_lt_top
      (p := 2) (by norm_num) (by simp) hf
  have hfinite_g : (∫⁻ point, ‖g point‖ₑ ^ (2 : ℕ)) < (∞ : ℝ≥0∞) := by
    simpa using lintegral_rpow_enorm_lt_top_of_eLpNorm_lt_top
      (p := 2) (by norm_num) (by simp) hg
  simp only [ENNReal.toReal_ofNat, ENNReal.rpow_two]
  calc
    (∫⁻ point : E × F, ‖f point.1 * g point.2‖ₑ ^ (2 : ℕ))
        ≤ ∫⁻ point : E, ∫⁻ other : F, ‖f point‖ₑ ^ (2 : ℕ) * ‖g other‖ₑ ^ (2 : ℕ) := by
      rw [Measure.volume_eq_prod, Measure.prod]
      refine (Measure.lintegral_bind_le _ _ hkernel).trans ?_
      apply lintegral_mono
      intro point
      simpa only [enorm_mul, mul_pow] using
        lintegral_map_le (fun pair : E × F => ‖f pair.1 * g pair.2‖ₑ ^ (2 : ℕ))
          measurable_prodMk_left.aemeasurable
    _ = (∫⁻ point, ‖f point‖ₑ ^ (2 : ℕ)) * ∫⁻ other, ‖g other‖ₑ ^ (2 : ℕ) :=
      lintegral_lintegral_mul (hf.aemeasurable.enorm.pow_const 2)
        (hg.aemeasurable.enorm.pow_const 2)
    _ < (∞ : ℝ≥0∞) := ENNReal.mul_lt_top hfinite_f hfinite_g

omit [SFinite (volume : Measure E)] in
lemma memLp_tensor_of_sfinite_right {f : E → ℂ} {g : F → ℂ}
    (hf : MemLp f 2) (hg : MemLp g 2) :
    MemLp (fun point : E × F => f point.1 * g point.2) 2 :=
  memLp_tensor_of_aemeasurable Measurable.map_prodMk_left.aemeasurable hf hg

lemma not_aemeasurable_count_restrict_prodMk {subset : Set ℝ}
    (hsubset : ¬ MeasurableSet subset) :
    ¬ AEMeasurable
      (fun point : ℝ => Measure.map (Prod.mk point)
        ((Measure.count : Measure ℝ).restrict subset)) Measure.count := by
  classical
  intro hkernel
  have hdiag := (Measure.measurable_coe (measurableSet_diagonal (α := ℝ))).comp_aemeasurable
    hkernel
  have hmeas : Measurable (fun point : ℝ =>
      (Measure.map (Prod.mk point) ((Measure.count : Measure ℝ).restrict subset))
        (Set.diagonal ℝ)) := by
    convert hdiag.measurable_mk using 1
    funext point
    exact Measure.ae_count_iff.mp hdiag.ae_eq_mk point
  have heval (point : ℝ) :
      (Measure.map (Prod.mk point) ((Measure.count : Measure ℝ).restrict subset))
        (Set.diagonal ℝ) = if point ∈ subset then 1 else 0 := by
    rw [Measure.map_apply measurable_prodMk_left measurableSet_diagonal]
    have hpreimage : Prod.mk point ⁻¹' Set.diagonal ℝ = {point} := by
      ext other
      simp [Set.diagonal, eq_comm]
    rw [hpreimage, Measure.restrict_apply (measurableSet_singleton point)]
    by_cases hpoint : point ∈ subset
    · rw [Set.singleton_inter_of_mem hpoint, Measure.count_singleton, ite_eq_left hpoint]
    · rw [Set.singleton_inter_of_notMem hpoint, measure_empty, ite_eq_right hpoint]
  apply hsubset
  have hnonzero := (measurableSet_eq_fun hmeas
    (measurable_const : Measurable (fun _ : ℝ => (0 : ℝ≥0∞)))).compl
  convert hnonzero using 1
  ext point
  simp [heval]

lemma not_memLp_tensor_count_restrict_of_choice {subset : Set ℝ}
    (hsubset : ¬ MeasurableSet subset)
    (hchoice : (Classical.ofNonempty : Measure (ℝ × ℝ)) =
      (∞ : ℝ≥0∞) • Measure.dirac (0, 0)) :
    ∃ f g : ℝ → ℂ, MemLp f 2 Measure.count ∧
      MemLp g 2 ((Measure.count : Measure ℝ).restrict subset) ∧
      ¬ MemLp (fun point : ℝ × ℝ => f point.1 * g point.2) 2
        ((Measure.count : Measure ℝ).prod (Measure.count.restrict subset)) := by
  classical
  let factor : ℝ → ℂ := ({0} : Set ℝ).indicator fun _ => 1
  have hfactor : MemLp factor 2 Measure.count :=
    memLp_indicator_const 2 (measurableSet_singleton 0) 1 (Or.inr (by simp))
  have hprod : (Measure.count : Measure ℝ).prod (Measure.count.restrict subset) =
      (∞ : ℝ≥0∞) • Measure.dirac (0, 0) := by
    rw [Measure.prod, Measure.bind,
      Measure.map_of_not_aemeasurable_of_ne_zero
        (not_aemeasurable_count_restrict_prodMk hsubset) Measure.count_ne_zero'',
      Measure.join_dirac, hchoice]
  refine ⟨factor, factor, hfactor, MemLp.mono_measure Measure.restrict_le_self hfactor, ?_⟩
  rw [hprod]
  have hnorm : eLpNorm (fun point : ℝ × ℝ => factor point.1 * factor point.2) 2
      ((∞ : ℝ≥0∞) • Measure.dirac (0, 0)) = (∞ : ℝ≥0∞) := by
    rw [eLpNorm_smul_measure_of_ne_zero ENNReal.top_ne_zero,
      eLpNorm_dirac _ _ (by norm_num)]
    norm_num [factor, ENNReal.top_rpow_of_pos]
  intro htensor
  exact htensor.eLpNorm_ne_top hnorm

omit [SFinite (volume : Measure E)] [SFinite (volume : Measure F)] in
lemma volume_prod_eq_choice_of_not_aemeasurable
    (hkernel : ¬ AEMeasurable
      (fun point : E => Measure.map (Prod.mk point) (volume : Measure F))
      (volume : Measure E)) :
    (volume : Measure (E × F)) = Classical.ofNonempty := by
  have hvolume : (volume : Measure E) ≠ 0 := by
    intro hzero
    apply hkernel
    rw [hzero]
    exact aemeasurable_zero_measure
  rw [Measure.volume_eq_prod, Measure.prod, Measure.bind,
    Measure.map_of_not_aemeasurable_of_ne_zero hkernel hvolume, Measure.join_dirac]

omit [SFinite (volume : Measure E)] [SFinite (volume : Measure F)] in
lemma memLp_tensor_iff_choice {f : E → ℂ} {g : F → ℂ}
    (hf : MemLp f 2) (hg : MemLp g 2) :
    MemLp (fun point : E × F => f point.1 * g point.2) 2 ↔
      (¬ AEMeasurable
        (fun point : E => Measure.map (Prod.mk point) (volume : Measure F))
        (volume : Measure E) →
        MemLp (fun point : E × F => f point.1 * g point.2) 2
          (Classical.ofNonempty : Measure (E × F))) := by
  constructor
  · intro htensor hkernel
    rwa [volume_prod_eq_choice_of_not_aemeasurable hkernel] at htensor
  · intro hchoice
    by_cases hkernel : AEMeasurable
        (fun point : E => Measure.map (Prod.mk point) (volume : Measure F))
        (volume : Measure E)
    · exact memLp_tensor_of_aemeasurable hkernel hf hg
    · rw [volume_prod_eq_choice_of_not_aemeasurable hkernel]
      exact hchoice hkernel

omit [SFinite (volume : Measure E)] in
/-- Right s-finiteness makes the product kernel measurable, so L² factors have an L² tensor.
Without an a.e. measurable kernel, Mathlib's product uses an arbitrary chosen measure, whose
integrability is characterized by `memLp_tensor_iff_choice`, not guaranteed by the factors.
The finite-dimensional Haar hypotheses in the applications imply right s-finiteness. -/
lemma memLp_tensor {f : E → ℂ} {g : F → ℂ} (hf : MemLp f 2) (hg : MemLp g 2) :
    MemLp (fun point : E × F => f point.1 * g point.2) 2 :=
  memLp_tensor_of_sfinite_right hf hg

lemma integral_tensor_sq (f : E → ℂ) (g : F → ℂ) :
    (∫ p : E × F, ‖f p.1*g p.2‖^2) = (∫ x, ‖f x‖^2)*(∫ y, ‖g y‖^2) := by
  simp only [norm_mul, mul_pow]
  rw [Measure.volume_eq_prod]
  exact integral_prod_mul (fun x => ‖f x‖^2) (fun y => ‖g y‖^2)

end TensorLp
section

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasureSpace E] [BorelSpace E]
  [(volume : Measure E).IsAddHaarMeasure]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [FiniteDimensional ℝ F] [MeasureSpace F] [BorelSpace F]
  [(volume : Measure F).IsAddHaarMeasure]

omit [FiniteDimensional ℝ E] [MeasureSpace E] [BorelSpace E]
  [(volume : Measure E).IsAddHaarMeasure] [FiniteDimensional ℝ F]
  [MeasureSpace F] [BorelSpace F] [(volume : Measure F).IsAddHaarMeasure] in
lemma lineDeriv_slice_left {φ : E × F → ℝ} (hφ : ContDiff ℝ ∞ φ)
    (x : E) (y : F) (v : E) :
    lineDeriv ℝ (fun z => φ (z,y)) x v = lineDeriv ℝ φ (x,y) (v,0) := by
  have hh := (hφ.differentiable (by simp) (x,y)).hasFDerivAt.comp x
    ((hasFDerivAt_id (𝕜 := ℝ) x).prodMk (hasFDerivAt_const (𝕜 := ℝ) y x))
  have hd := (hh.hasLineDerivAt v).lineDeriv
  rw [(hφ.differentiable (by simp) (x,y)).lineDeriv_eq_fderiv]
  simpa only [Function.comp_def, id_eq, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.prod_apply, ContinuousLinearMap.id_apply,
    zero_apply] using hd

lemma IsWeakDerivative.tensor_left {v : E} {f df : E → ℂ} {g : F → ℂ}
    (hwd : IsWeakDerivative v f df) (hf : MemLp f 2) (hdf : MemLp df 2)
    (hg : MemLp g 2) :
    IsWeakDerivative (v,0) (fun p : E × F => f p.1*g p.2)
      (fun p => df p.1*g p.2) := by
  intro φ hφ hcφ
  have hi1 := (memLp_tensor hf hg).integrable_mul
    (test_deriv_memLp hφ hcφ (v,0))
  have hi2 := (memLp_tensor hdf hg).integrable_mul (test_memLp hφ hcφ)
  have hp1 := integral_prod_symm _ hi1
  have hp2 := integral_prod_symm _ hi2
  simp only [Pi.mul_apply] at hp1 hp2
  rw [Measure.volume_eq_prod E F, hp1, hp2, ← integral_neg]
  apply integral_congr_ae
  exact Eventually.of_forall fun y => by
    have ht : ContDiff ℝ ∞ (fun x => φ (x,y)) := hφ.comp (contDiff_id.prodMk contDiff_const)
    have hct : HasCompactSupport (fun x => φ (x,y)) := by
      apply HasCompactSupport.of_support_subset_isCompact (hcφ.image continuous_fst)
      intro x hx
      exact ⟨(x,y), subset_tsupport φ hx, rfl⟩
    have hh := hwd (fun x => φ (x,y)) ht hct
    simp_rw [lineDeriv_slice_left hφ] at hh
    simpa only [mul_right_comm (f _) (g y), mul_right_comm (df _) (g y),
      integral_mul_const, neg_mul] using congrArg (fun c => c*g y) hh

lemma IsWeakDerivative.tensor_right {v : F} {g dg : F → ℂ} {f : E → ℂ}
    (hwd : IsWeakDerivative v g dg) (hg : MemLp g 2) (hdg : MemLp dg 2)
    (hf : MemLp f 2) :
    IsWeakDerivative (0,v) (fun p : E × F => f p.1*g p.2)
      (fun p => f p.1*dg p.2) := by
  have hh := (hwd.tensor_left hg hdg hf).pullback
    (ContinuousLinearEquiv.prodComm ℝ E F)
      (by change MeasurePreserving Prod.swap (volume.prod volume) (volume.prod volume)
          exact Measure.measurePreserving_swap) (w := (0,v)) rfl
  change IsWeakDerivative (0,v) (fun p : E × F => g p.2*f p.1)
    (fun p => dg p.2*f p.1) at hh
  simpa only [mul_comm] using hh

end

open MeasureTheory Filter
open scoped Topology ContDiff BigOperators


def leftList {α : Type*} {N M : ℕ} (x : Fin (N+M) → α) : Fin N → α :=
  fun i => x (finSumFinEquiv (Sum.inl i))
def rightList {α : Type*} {N M : ℕ} (x : Fin (N+M) → α) : Fin M → α :=
  fun i => x (finSumFinEquiv (Sum.inr i))

@[simp] lemma leftList_join {α : Type*} {N M : ℕ} (x : Fin N → α) (y : Fin M → α) :
    leftList (joinLists x y) = x := by ext i; exact joinLists_left x y i
@[simp] lemma rightList_join {α : Type*} {N M : ℕ} (x : Fin N → α) (y : Fin M → α) :
    rightList (joinLists x y) = y := by ext i; exact joinLists_right x y i
@[simp] lemma join_list_parts {α : Type*} {N M : ℕ} (x : Fin (N+M) → α) :
    joinLists (leftList x) (rightList x) = x := by
  ext i
  obtain ⟨j,rfl⟩ := finSumFinEquiv.surjective i
  cases j with
  | inl j => exact joinLists_left (leftList x) (rightList x) j
  | inr j => exact joinLists_right (leftList x) (rightList x) j

lemma configurationJoin_symm_apply {N M : ℕ} (x : Configuration (N+M)) :
    (configurationJoin N M).symm x = (leftList x,rightList x) := by
  apply (configurationJoin N M).injective
  rw [ContinuousLinearEquiv.apply_symm_apply,configurationJoin_apply,join_list_parts]

lemma configurationJoin_symm_preserving (N M : ℕ) :
    MeasurePreserving (configurationJoin N M).symm :=
  MeasurePreserving.symm (configurationJoin N M).toHomeomorph.toMeasurableEquiv
    (configurationJoin_preserving N M)

lemma configurationJoin_direction_right {N M : ℕ} (i : Fin M) (a : Fin 3) :
    configurationJoin N M (0,direction i a) = direction (finSumFinEquiv (Sum.inr i)) a := by
  rw [configurationJoin_apply]
  funext j
  obtain ⟨j,rfl⟩ := finSumFinEquiv.surjective j
  cases j with
  | inl j =>
    rw [joinLists_left]
    have hn : finSumFinEquiv (Sum.inl j) ≠ finSumFinEquiv (Sum.inr i) :=
      fun h => Sum.inl_ne_inr (finSumFinEquiv.injective h)
    simp only [direction, Pi.single_apply, ite_eq_right hn, Pi.zero_apply]
  | inr j => rw [joinLists_right]; simp [direction, Pi.single_apply]

def tensorForm {N M : ℕ} (ψ : FormVector N) (φ : FormVector M) : FormVector (N+M) where
  value s x := ψ.value (leftList s) (leftList x) * φ.value (rightList s) (rightList x)
  gradient s i a x := Sum.elim
    (fun j => ψ.gradient (leftList s) j a (leftList x) * φ.value (rightList s) (rightList x))
    (fun j => ψ.value (leftList s) (leftList x) * φ.gradient (rightList s) j a (rightList x))
    (finSumFinEquiv.symm i)

@[simp] lemma tensorForm_value_join {N M : ℕ} (ψ : FormVector N) (φ : FormVector M)
    (s : Spins N) (t : Spins M) (x : Configuration N) (y : Configuration M) :
    (tensorForm ψ φ).value (joinLists s t) (joinLists x y) = ψ.value s x*φ.value t y := by
  simp only [tensorForm,leftList_join,rightList_join]

@[simp] lemma tensorForm_gradient_left {N M : ℕ} (ψ : FormVector N) (φ : FormVector M)
    (s : Spins N) (t : Spins M) (x : Configuration N) (y : Configuration M)
    (i : Fin N) (a : Fin 3) :
    (tensorForm ψ φ).gradient (joinLists s t) (finSumFinEquiv (Sum.inl i)) a (joinLists x y) =
      ψ.gradient s i a x*φ.value t y := by
  simp only [tensorForm,leftList_join,rightList_join,Equiv.symm_apply_apply,Sum.elim_inl]

@[simp] lemma tensorForm_gradient_right {N M : ℕ} (ψ : FormVector N) (φ : FormVector M)
    (s : Spins N) (t : Spins M) (x : Configuration N) (y : Configuration M)
    (i : Fin M) (a : Fin 3) :
    (tensorForm ψ φ).gradient (joinLists s t) (finSumFinEquiv (Sum.inr i)) a (joinLists x y) =
      ψ.value s x*φ.gradient t i a y := by
  simp only [tensorForm,leftList_join,rightList_join,Equiv.symm_apply_apply,Sum.elim_inr]

lemma SobolevVector.tensor {N M : ℕ} {ψ : FormVector N} {φ : FormVector M}
    (hψ : SobolevVector ψ) (hφ : SobolevVector φ) : SobolevVector (tensorForm ψ φ) := by
  refine ⟨fun s => ?_, fun s i a => ?_, fun s i a => ?_⟩
  · simpa only [Function.comp_def,configurationJoin_symm_apply,tensorForm] using
      (memLp_tensor (hψ.1 (leftList s)) (hφ.1 (rightList s))).comp_measurePreserving
        (configurationJoin_symm_preserving N M)
  · obtain ⟨i,rfl⟩ := finSumFinEquiv.surjective i
    cases i with
    | inl i =>
      simpa only [Function.comp_def,configurationJoin_symm_apply,tensorForm,
        Equiv.symm_apply_apply,Sum.elim_inl] using
        (memLp_tensor
          (hψ.2.1 (leftList s) i a) (hφ.1 (rightList s))).comp_measurePreserving
          (configurationJoin_symm_preserving N M)
    | inr i =>
      simpa only [Function.comp_def,configurationJoin_symm_apply,tensorForm,
        Equiv.symm_apply_apply,Sum.elim_inr] using
        (memLp_tensor
          (hψ.1 (leftList s)) (hφ.2.1 (rightList s) i a)).comp_measurePreserving
          (configurationJoin_symm_preserving N M)
  · obtain ⟨i,rfl⟩ := finSumFinEquiv.surjective i
    cases i with
    | inl i =>
      have hv : (configurationJoin N M).symm (direction (finSumFinEquiv (Sum.inl i)) a) =
          (direction i a,0) := by rw [← configurationJoin_direction,ContinuousLinearEquiv.symm_apply_apply]
      simpa only [Function.comp_def,configurationJoin_symm_apply,tensorForm,
        Equiv.symm_apply_apply,Sum.elim_inl] using
        ((hψ.2.2 (leftList s) i a).tensor_left (hψ.1 _) (hψ.2.1 _ i a) (hφ.1 _)).pullback
          (configurationJoin N M).symm (configurationJoin_symm_preserving N M) hv
    | inr i =>
      have hv : (configurationJoin N M).symm (direction (finSumFinEquiv (Sum.inr i)) a) =
          (0,direction i a) := by rw [← configurationJoin_direction_right,ContinuousLinearEquiv.symm_apply_apply]
      simpa only [Function.comp_def,configurationJoin_symm_apply,tensorForm,
        Equiv.symm_apply_apply,Sum.elim_inr] using
        ((hφ.2.2 (rightList s) i a).tensor_right (hφ.1 _) (hφ.2.1 _ i a) (hψ.1 _)).pullback
          (configurationJoin N M).symm (configurationJoin_symm_preserving N M) hv

lemma formMass_tensor {N M : ℕ} (ψ : FormVector N) (φ : FormVector M) :
    formMass (tensorForm ψ φ) = formMass ψ*formMass φ := by
  unfold formMass
  rw [← sum_spin_join]
  have hi (s : Spins N) (t : Spins M) :
      (∫ z, ‖(tensorForm ψ φ).value (joinLists s t) z‖^2) =
        (∫ x, ‖ψ.value s x‖^2)*(∫ y, ‖φ.value t y‖^2) := by
    rw [← (configurationJoin_preserving N M).integral_comp
      (configurationJoin N M).toHomeomorph.measurableEmbedding
      (fun z => ‖(tensorForm ψ φ).value (joinLists s t) z‖^2)]
    simp only [configurationJoin_apply_prod,tensorForm_value_join]
    exact integral_tensor_sq _ _
  simp_rw [hi,← Finset.sum_mul,← Finset.mul_sum]


open MeasureTheory Filter
open scoped Topology ContDiff BigOperators

end CoulombAtom

end

end OAI
