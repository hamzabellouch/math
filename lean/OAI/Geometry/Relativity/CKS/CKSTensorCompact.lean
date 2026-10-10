import OAI.Geometry.Relativity.CKS.MixedMassCompact
import OAI.Geometry.Relativity.CKS.CKSTensorJet

namespace OAI

noncomputable section
namespace CKSMixedGeometry
noncomputable section
open CKSCalculus Set Filter
open CKSAngularGeometry (determinant)
open scoped Topology ContDiff NNReal Matrix.Norms.Elementwise

lemma tensorRegion_open : IsOpen tensorRegion := by
  have h := massDenominator_continuousOn.isOpen_inter_preimage massMetricRegion_open (isOpen_Ioi (a := (0:ℝ)))
  exact h.preimage tensorBase_smooth.continuous

lemma tensorRegion_zero {j : TensorInput}
    (hj : determinant (fun i k => (j.1.1 0 i k).1.1) ≠ 0) : (0,j) ∈ tensorRegion := by
  constructor
  · simpa only [coefficientMetric_zero] using hj
  · simp [tensorDen,constantJet]

lemma tensor_family_bound {K : Set TensorInput} (hK : IsCompact K)
    (hreg : ∀ j ∈ K, determinant (fun i k => (j.1.1 0 i k).1.1) ≠ 0) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ C : ℝ, 0 ≤ C ∧ ∀ z : ScalarThreeJet,
      ∀ j ∈ K, ‖z‖ ≤ δ → ‖tensorCoefficients (z,j)‖ ≤ C := by
  let : FiniteDimensional ℝ ScalarThreeJet := inferInstance
  let : FiniteDimensional ℝ MatrixThreeJet := inferInstance
  let : FiniteDimensional ℝ MatrixScalarJet := inferInstance
  let : FiniteDimensional ℝ (Fin 3 → MatrixThreeJet) := inferInstance
  let : FiniteDimensional ℝ (Fin 3 → MatrixScalarJet) := inferInstance
  let : FiniteDimensional ℝ (A → ScalarThreeJet) := inferInstance
  let : FiniteDimensional ℝ (A → ScalarJet) := inferInstance
  let : FiniteDimensional ℝ MassInput := inferInstance
  let : FiniteDimensional ℝ TensorInput := inferInstance
  let : ProperSpace TensorParameter := FiniteDimensional.proper ℝ TensorParameter
  let K₀ : Set TensorParameter := (fun j : TensorInput => ((0:ScalarThreeJet),j)) '' K
  have hK₀ : IsCompact K₀ := hK.image (by fun_prop)
  have hs : K₀ ⊆ tensorRegion := by
    rintro p ⟨j,hj,rfl⟩
    exact tensorRegion_zero (hreg j hj)
  obtain ⟨δ,hδ,hδs⟩ := hK₀.exists_cthickening_subset_open tensorRegion_open hs
  obtain ⟨C,hC⟩ := (hK₀.cthickening (r := δ)).exists_bound_of_continuousOn
    (fun p hp => (tensorCoefficients_smooth (hδs hp)).continuousAt.continuousWithinAt)
  refine ⟨δ,hδ,max C 0,le_max_right _ _,?_⟩
  intro z j hj hz
  apply (hC (z,j) ?_).trans (le_max_left _ _)
  apply Metric.mem_cthickening_of_dist_le (z,j) (0,j) δ K₀ ⟨j,hj,rfl⟩
  simpa only [Prod.dist_eq,dist_zero_right,dist_self,max_eq_left (norm_nonneg z)] using hz

def boundedTensorFamily (K : Set MatrixThreeJet) (B : ℝ) : Set TensorInput :=
  boundedMassFamily K B ×ˢ (Metric.closedBall (0:ScalarJet) B ×ˢ Metric.closedBall (0:A → ScalarJet) B)

lemma boundedTensorFamily_compact {K : Set MatrixThreeJet} (hK : IsCompact K) (B : ℝ) :
    IsCompact (boundedTensorFamily K B) := by
  let : ProperSpace ScalarJet := FiniteDimensional.proper ℝ ScalarJet
  let : ProperSpace (A → ScalarJet) := FiniteDimensional.proper ℝ (A → ScalarJet)
  exact (boundedMassFamily_compact hK B).prod ((isCompact_closedBall _ B).prod (isCompact_closedBall _ B))

theorem cks_tensor_coefficients_bounded {K : Set MatrixThreeJet} (hK : IsCompact K)
    (hreg : ∀ q ∈ K, determinant (fun i k => (q i k).1.1) ≠ 0) (B : ℝ) :
    ∃ R₀ : ℝ, 1 ≤ R₀ ∧ ∃ C : ℝ, 0 ≤ C ∧ ∀ r : ℝ,
      ∀ z : ScalarThreeJet, ∀ j : TensorInput, R₀ ≤ r → ‖z‖ ≤ 1/r →
      j.1.1 0 ∈ K → ‖j.1‖ ≤ B → ‖j.2.1‖ ≤ B → ‖j.2.2‖ ≤ B →
      ‖tensorCoefficients (z,j)‖ ≤ C := by
  obtain ⟨δ,hδ,C,hC,hh⟩ := tensor_family_bound (boundedTensorFamily_compact hK B)
    (fun j hj => hreg _ hj.1.1)
  refine ⟨max 1 (1/δ),le_max_left _ _,C,hC,?_⟩
  intro r z j hr hz hq hj hkr hkb
  have hr0 : 0 < r := lt_of_lt_of_le zero_lt_one ((le_max_left _ _).trans hr)
  have hd : 1/r ≤ δ := by
    apply (div_le_iff₀ hr0).mpr
    simpa only [mul_comm] using ((div_le_iff₀ hδ).mp ((le_max_right _ _).trans hr))
  apply hh z j
  · exact ⟨boundedMassFamily_mem hq hj,by simpa only [Metric.mem_closedBall,dist_zero_right] using hkr,
      by simpa only [Metric.mem_closedBall,dist_zero_right] using hkb⟩
  · exact hz.trans hd

end
end CKSMixedGeometry

end

end OAI
