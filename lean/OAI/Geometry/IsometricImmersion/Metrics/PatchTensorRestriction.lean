import OAI.Geometry.IsometricImmersion.Assembly.EnumeratedPatchTensors
import OAI.Geometry.IsometricImmersion.Obstructions.PatchAdmissibility

namespace OAI

noncomputable section
open Set Filter Function
open scoped ContDiff Topology BigOperators Matrix Matrix.Norms.Elementwise

namespace SmoothLocal.Geometry
open SmoothLocal.Perturbation

def assembledPatchTensor (eta : PatchAddress → SymmetricPerturbation) : MetricField :=
  tensorPatchSum (enumeratedPatchTensor eta)

def assembledPatchMetric (g : MetricField) (eta : PatchAddress → SymmetricPerturbation) : MetricField :=
  g + assembledPatchTensor eta

def localPatchMetric (g : MetricField) (eta : PatchAddress → SymmetricPerturbation)
    (a : PatchAddress) : MetricField :=
  affinePullbackMetric g (patchAddressCenter a) (patchAddressMatrix a) + perturbationTensor (eta a)

theorem assembledPatchTensor_eq_single (eta : PatchAddress → SymmetricPerturbation)
    (a : PatchAddress) {p : Coord} (hp : p ∈ patchAddressCarrier a) :
    assembledPatchTensor eta p = patchAddressTensor eta a p := by
  have hh := tensorPatchSum_eq_single_on_disjoint_carrier
    (enumeratedPatchTensor eta) enumeratedPatchCarrier
    (enumeratedPatchTensor_tsupport_subset eta) enumeratedPatchCarriers_pairwise_disjoint
    (patchTensorIndex a) (by simpa only [enumeratedPatchCarrier_index] using hp)
  simpa only [assembledPatchTensor,enumeratedPatchTensor_index] using hh

theorem assembledPatchTensor_zero_off_carriers (eta : PatchAddress → SymmetricPerturbation)
    {p : Coord} (hp : ∀ a : PatchAddress, p ∉ patchAddressCarrier a) : assembledPatchTensor eta p = 0 := by
  apply tensorPatchSum_zero_off_carriers (enumeratedPatchTensor eta) enumeratedPatchCarrier
    (enumeratedPatchTensor_tsupport_subset eta)
  intro j
  cases h : patchTensorAddress j with
  | none => simp [enumeratedPatchCarrier,h]
  | some a => simpa only [enumeratedPatchCarrier,h] using hp a

theorem assembledPatchMetric_pullback_eq_on_closedPatchBox
    (g : MetricField) (eta : PatchAddress → SymmetricPerturbation) (a : PatchAddress)
    {q : Coord} (hq : q ∈ closedPatchBox) :
    affinePullbackMetric (assembledPatchMetric g eta) (patchAddressCenter a) (patchAddressMatrix a) q =
      localPatchMetric g eta a q := by
  have hp : affineCoordinates (patchAddressCenter a) (patchAddressMatrix a) q ∈ patchAddressCarrier a :=
    ⟨q,hq,rfl⟩
  calc
    _ = affinePullbackMetric (g + patchAddressTensor eta a)
        (patchAddressCenter a) (patchAddressMatrix a) q := by
      unfold affinePullbackMetric assembledPatchMetric
      simp only [Pi.add_apply,assembledPatchTensor_eq_single eta a hp]
    _ = _ := congrFun (affinePullback_add_pushforward g (perturbationTensor (eta a))
      (patchAddressCenter a) (patchAddressMatrix a) (patchAddressMatrix_isUnit a)) q

theorem assembledPatchMetric_pullback_eventuallyEq
    (g : MetricField) (eta : PatchAddress → SymmetricPerturbation) (a : PatchAddress)
    {q : Coord} (hq : ‖q‖ < 4) :
    affinePullbackMetric (assembledPatchMetric g eta) (patchAddressCenter a) (patchAddressMatrix a)
      =ᶠ[𝓝 q] localPatchMetric g eta a := by
  have hball : q ∈ Metric.ball (0 : Coord) 4 := by
    simpa only [Metric.mem_ball,dist_zero_right] using hq
  filter_upwards [Metric.isOpen_ball.mem_nhds hball] with p hp
  apply assembledPatchMetric_pullback_eq_on_closedPatchBox g eta a
  apply (mem_closedPatchBox_iff_norm_le p).mpr
  exact (by simpa only [Metric.mem_ball,dist_zero_right] using hp : ‖p‖ < 4).le

theorem assembledPatchTensor_contDiff {epsilon : ℝ} (he : 0 < epsilon)
    (eta : PatchAddress → SymmetricPerturbation)
    (hsmall : ∀ a, eta a ∈ patchTensorBudgetNeighborhood epsilon a) :
    ContDiff ℝ ∞ (assembledPatchTensor eta) :=
  tensorPatchSum_contDiff _ epsilon (enumeratedPatchTensor_contDiff eta)
    (enumeratedPatchTensor_hasCompactSupport eta) (enumeratedPatchTensor_diagonal_bound he eta hsmall)

theorem assembledPatchTensor_summable {epsilon : ℝ} (he : 0 < epsilon)
    (eta : PatchAddress → SymmetricPerturbation)
    (hsmall : ∀ a, eta a ∈ patchTensorBudgetNeighborhood epsilon a) (p : Coord) :
    Summable (fun j => enumeratedPatchTensor eta j p) :=
  tensorPatchSum_summable _ epsilon (enumeratedPatchTensor_diagonal_bound he eta hsmall) p

theorem assembledPatchTensor_all_jets_zero_at_origin {epsilon : ℝ} (he : 0 < epsilon)
    (eta : PatchAddress → SymmetricPerturbation)
    (hsmall : ∀ a, eta a ∈ patchTensorBudgetNeighborhood epsilon a) (k : ℕ) :
    iteratedFDeriv ℝ k (assembledPatchTensor eta) (0 : Coord) = 0 := by
  apply tensorPatchSum_jets_zero_off_each_support _ epsilon (enumeratedPatchTensor_contDiff eta)
    (enumeratedPatchTensor_hasCompactSupport eta) (enumeratedPatchTensor_diagonal_bound he eta hsmall)
  intro j hj
  exact zero_not_mem_enumeratedPatchCarrier j (enumeratedPatchTensor_tsupport_subset eta j hj)

theorem assembledPatchTensor_all_jets_zero_on_disk {epsilon : ℝ} (he : 0 < epsilon)
    (eta : PatchAddress → SymmetricPerturbation)
    (hsmall : ∀ a, eta a ∈ patchTensorBudgetNeighborhood epsilon a)
    (n : ℕ) {p : Coord} (hp : p ∈ accumulatingDisk n) (k : ℕ) :
    iteratedFDeriv ℝ k (assembledPatchTensor eta) p = 0 := by
  apply tensorPatchSum_jets_zero_off_each_support _ epsilon (enumeratedPatchTensor_contDiff eta)
    (enumeratedPatchTensor_hasCompactSupport eta) (enumeratedPatchTensor_diagonal_bound he eta hsmall)
  intro j hj
  exact Set.disjoint_left.mp (enumeratedPatchCarrier_disjoint_disk j n)
    (enumeratedPatchTensor_tsupport_subset eta j hj) hp

theorem assembledPatchTensor_jets_eq_single_on_carrier {epsilon : ℝ} (he : 0 < epsilon)
    (eta : PatchAddress → SymmetricPerturbation)
    (hsmall : ∀ a, eta a ∈ patchTensorBudgetNeighborhood epsilon a)
    (a : PatchAddress) {p : Coord} (hp : p ∈ patchAddressCarrier a) (k : ℕ) :
    iteratedFDeriv ℝ k (assembledPatchTensor eta) p = iteratedFDeriv ℝ k (patchAddressTensor eta a) p := by
  have hi : p ∈ enumeratedPatchCarrier (patchTensorIndex a) := by
    simpa only [enumeratedPatchCarrier_index] using hp
  have hjets := tensorPatchSum_jets_eq_single _ epsilon (enumeratedPatchTensor_contDiff eta)
    (enumeratedPatchTensor_hasCompactSupport eta) (enumeratedPatchTensor_diagonal_bound he eta hsmall)
    (patchTensorIndex a) (p := p)
    (fun j hj hmem => Set.disjoint_left.mp (enumeratedPatchCarriers_pairwise_disjoint hj)
      (enumeratedPatchTensor_tsupport_subset eta j hmem) hi) k
  simpa only [assembledPatchTensor,enumeratedPatchTensor_index] using hjets

theorem assembledPatchMetric_posDef
    {g : MetricField} {U : Set Coord} (hg : ∀ p ∈ U, (g p).PosDef)
    (eta : PatchAddress → SymmetricPerturbation)
    (hlocal : ∀ a, ∀ p ∈ U ∩ patchAddressCarrier a, ((g + patchAddressTensor eta a) p).PosDef) :
    ∀ p ∈ U, (assembledPatchMetric g eta p).PosDef := by
  intro p hp
  by_cases hex : ∃ a, p ∈ patchAddressCarrier a
  · obtain ⟨a,ha⟩ := hex
    change (g p + assembledPatchTensor eta p).PosDef
    rw [assembledPatchTensor_eq_single eta a ha]
    exact hlocal a p ⟨hp,ha⟩
  · have hout : ∀ a, p ∉ patchAddressCarrier a := fun a ha => hex ⟨a,ha⟩
    change (g p + assembledPatchTensor eta p).PosDef
    rw [assembledPatchTensor_zero_off_carriers eta hout,add_zero]
    exact hg p hp

theorem assembledPatchMetric_smoothPositive {epsilon : ℝ} (he : 0 < epsilon)
    {g : MetricField} {U : Set Coord} (hg : SmoothPositiveOn g U)
    (eta : PatchAddress → SymmetricPerturbation)
    (hsmall : ∀ a, eta a ∈ patchTensorBudgetNeighborhood epsilon a)
    (hlocal : ∀ a, ∀ p ∈ U ∩ patchAddressCarrier a, ((g + patchAddressTensor eta a) p).PosDef) :
    SmoothPositiveOn (assembledPatchMetric g eta) U :=
  smoothPositive_metric_add_of_tensor_contDiff hg (assembledPatchTensor_contDiff he eta hsmall)
    (assembledPatchMetric_posDef hg.2 eta hlocal)

theorem assembledPatchMetric_curvature_on_disk {epsilon : ℝ} (he : 0 < epsilon)
    {g : MetricField} {U : Set Coord} (hg : SmoothPositiveOn g U) (hU : IsOpen U)
    (eta : PatchAddress → SymmetricPerturbation)
    (hsmall : ∀ a, eta a ∈ patchTensorBudgetNeighborhood epsilon a)
    (hlocal : ∀ a, ∀ p ∈ U ∩ patchAddressCarrier a, ((g + patchAddressTensor eta a) p).PosDef)
    (n : ℕ) {p : Coord} (hp : p ∈ accumulatingDisk n) (hpU : p ∈ U) :
    gaussianCurvature (assembledPatchMetric g eta) p = gaussianCurvature g p :=
  gaussianCurvature_add_eq_of_zero_tensor_jets hg hU hpU
    (assembledPatchTensor_contDiff he eta hsmall) (assembledPatchMetric_posDef hg.2 eta hlocal)
    (assembledPatchTensor_all_jets_zero_on_disk he eta hsmall n hp)

end SmoothLocal.Geometry

end

end OAI
