import OAI.Geometry.Relativity.CKS.MixedMassUniform

namespace OAI

noncomputable section
namespace CKSMixedGeometry
noncomputable section
open CKSCalculus Set Filter
open CKSAngularGeometry (determinant)
open scoped Topology ContDiff NNReal Matrix.Norms.Elementwise

def boundedMassFamily (K : Set MatrixThreeJet) (B : ℝ) : Set MassInput :=
  {j | j.1 0 ∈ K} ∩ Metric.closedBall 0 B

lemma boundedMassFamily_compact {K : Set MatrixThreeJet} (hK : IsCompact K) (B : ℝ) :
    IsCompact (boundedMassFamily K B) := by
  let : FiniteDimensional ℝ ScalarThreeJet := inferInstance
  let : FiniteDimensional ℝ MatrixThreeJet := inferInstance
  let : FiniteDimensional ℝ MatrixScalarJet := inferInstance
  let : FiniteDimensional ℝ (Fin 3 → MatrixThreeJet) := inferInstance
  let : FiniteDimensional ℝ (Fin 3 → MatrixScalarJet) := inferInstance
  let : FiniteDimensional ℝ (A → ScalarThreeJet) := inferInstance
  let : FiniteDimensional ℝ (A → ScalarJet) := inferInstance
  let : FiniteDimensional ℝ MassInput := inferInstance
  let : ProperSpace MassInput := FiniteDimensional.proper ℝ MassInput
  exact (isCompact_closedBall (0:MassInput) B).inter_left (hK.isClosed.preimage (by fun_prop))

lemma boundedMassFamily_mem {K : Set MatrixThreeJet} {B : ℝ} {j : MassInput}
    (hj : j.1 0 ∈ K) (hB : ‖j‖ ≤ B) : j ∈ boundedMassFamily K B :=
  ⟨hj,by simpa only [Metric.mem_closedBall,dist_zero_right] using hB⟩

attribute [local irreducible] cksMassJet leadingMassJet

theorem cks_mass_uniform_bounded {K : Set MatrixThreeJet} (hK : IsCompact K)
    (hreg : ∀ q ∈ K, determinant (fun i k => (q i k).1.1) ≠ 0) (B : ℝ) :
    ∃ R₀ : ℝ, 1 ≤ R₀ ∧ ∃ C : ℝ, 0 ≤ C ∧ ∀ r : ℝ, ∀ z : ScalarThreeJet, ∀ j : MassInput,
      R₀ ≤ r → ‖z‖ ≤ 1/r → j.1 0 ∈ K → ‖j‖ ≤ B →
      ‖cksMassJet z j-leadingMassJet j‖ ≤ C/r := by
  obtain ⟨δ,hδ,C,hC,hh⟩ := cks_mass_uniform (boundedMassFamily_compact hK B)
    (fun j hj => hreg _ hj.1)
  refine ⟨max 1 (1/δ),le_max_left _ _,C,hC,?_⟩
  intro r z j hr hz hj hB
  have hr1 : 1 ≤ r := (le_max_left _ _).trans hr
  have hr0 : 0 < r := lt_of_lt_of_le zero_lt_one hr1
  have hd : 1/r ≤ δ := by
    apply (div_le_iff₀ hr0).mpr
    simpa only [mul_comm] using ((div_le_iff₀ hδ).mp ((le_max_right _ _).trans hr))
  exact (hh z j (boundedMassFamily_mem hj hB) (hz.trans hd)).trans
    (by simpa only [mul_one_div] using mul_le_mul_of_nonneg_left hz hC)

end
end CKSMixedGeometry

end

end OAI
