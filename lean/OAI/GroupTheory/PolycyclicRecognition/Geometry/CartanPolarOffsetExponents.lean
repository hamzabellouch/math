import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanTransformedPolarTemplates

namespace OAI

/-! # Exact cancellation of the polar source and target exponents -/

noncomputable section
namespace PolycyclicRecognition.CartanWordModel

open Module LieAlgebra Set
open scoped BigOperators

variable {L W : Type*} [LieRing L] [LieAlgebra ℝ L] [FiniteDimensional ℝ L]
  {H : LieSubalgebra ℝ L} [H.IsCartanSubalgebra] (M : CartanWordModel H)
  {a : ℕ} (T : TriangularAdjoint L a)
  (hunimod : ∀ x : L, LinearMap.trace ℝ L (ad ℝ L x) = 0)
  [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
  (eW : HeightSpace T.character ≃ₗ[ℝ] W)

theorem sum_polar_ideal_cost_smul (K : ProperCone ℝ (StrongDual ℝ W))
    (β : M.ConeIdealBases (heightConePreimage T eW K)) {c : ℝ} (hc : 0 ≤ c) :
    (∑ j, M.coneIdealWordCost (heightConePreimage T eW K)
      ((M.supportIn T hunimod eW).weightSupport
        ((fun x : W => c • x) '' conePolarTemplate K)) (β.val j)) =
      c * ∑ j, M.coneIdealWordCost (heightConePreimage T eW K)
        (M.polarProbeWidths T hunimod eW K) (β.val j) := by
  have he : (M.supportIn T hunimod eW).weightSupport
      ((fun x : W => c • x) '' conePolarTemplate K) =
      fun i => c * M.polarProbeWidths T hunimod eW K i := by
    funext i
    exact M.weightSupport_polar_smul T hunimod eW K hc i
  rw [he]
  simp only [M.coneIdealWordCost_smul, Finset.mul_sum]

/-- The common source maximizing basis computes every polar radius. -/
theorem polar_templateSupport_eq (K : ProperCone ℝ (StrongDual ℝ W))
    (bN : Basis (Fin (finrank ℝ (cartanRootIdeal H))) ℝ (cartanRootIdeal H))
    (bI : Basis (Fin (finrank ℝ (M.coneWordIdeal (heightConePreimage T eW K))))
      ℝ (M.coneWordIdeal (heightConePreimage T eW K)))
    (β : M.ConeIdealBases (heightConePreimage T eW K))
    (hβ : M.IsMaximizingConeIdealBasis (heightConePreimage T eW K) bI
      (M.polarProbeWidths T hunimod eW K) β) {c : ℝ} (hc : 0 ≤ c) :
    (M.supportIn T hunimod eW).templateSupport
      ((fun x : W => c • x) '' conePolarTemplate K) =
      c * ∑ j, M.coneIdealWordCost (heightConePreimage T eW K)
        (M.polarProbeWidths T hunimod eW K) (β.val j) := by
  obtain ⟨_, _, _, hs, hz⟩ := M.polar_probe_template_properties T hunimod eW K hc
  have he : (M.supportIn T hunimod eW).weightSupport
      ((fun x : W => c • x) '' conePolarTemplate K) =
      fun i => c * M.polarProbeWidths T hunimod eW K i := by
    funext i
    exact M.weightSupport_polar_smul T hunimod eW K hc i
  have hβc : M.IsMaximizingConeIdealBasis (heightConePreimage T eW K) bI
      ((M.supportIn T hunimod eW).weightSupport
        ((fun x : W => c • x) '' conePolarTemplate K)) β := by
    rw [he]
    exact M.maximizing_coneIdealBasis_smul _ bI _ β hβ hc
  rw [← M.sum_coneIdealCost_eq_templateSupport T hunimod eW _ bN bI _ hs hz β hβc]
  exact M.sum_polar_ideal_cost_smul T hunimod eW K β hc

/-- Source radius `2ε/3`, target radius `ε/3`, and the actual tiling rate
have exactly matching exponents. The target cone and its dimension may differ. -/
theorem polar_offset_exponent_balance (K : ProperCone ℝ (StrongDual ℝ W))
    (A : templateSymmetryGroup (M.supportIn T hunimod eW))
    (bN : Basis (Fin (finrank ℝ (cartanRootIdeal H))) ℝ (cartanRootIdeal H))
    (bI : Basis (Fin (finrank ℝ (M.coneWordIdeal (heightConePreimage T eW K))))
      ℝ (M.coneWordIdeal (heightConePreimage T eW K)))
    (β : M.ConeIdealBases (heightConePreimage T eW K))
    (hβ : M.IsMaximizingConeIdealBasis (heightConePreimage T eW K) bI
      (M.polarProbeWidths T hunimod eW K) β)
    (bI' : Basis (Fin (finrank ℝ
      (M.coneWordIdeal (heightConePreimage T eW (transformedPolarCone K A.val)))))
      ℝ (M.coneWordIdeal (heightConePreimage T eW (transformedPolarCone K A.val))))
    (β' : M.ConeIdealBases (heightConePreimage T eW (transformedPolarCone K A.val)))
    {ε : ℝ} (hε : 0 < ε)
    (hβ' : M.IsMaximizingConeIdealBasis
      (heightConePreimage T eW (transformedPolarCone K A.val)) bI'
      ((M.supportIn T hunimod eW).weightSupport
        (A.val '' ((fun x : W => (ε / 3) • x) '' conePolarTemplate K))) β') :
    (M.supportIn T hunimod eW).templateSupport
      ((fun x : W => (2 * ε / 3) • x) '' conePolarTemplate K) -
      (∑ j, M.coneIdealWordCost
        (heightConePreimage T eW (transformedPolarCone K A.val))
        ((M.supportIn T hunimod eW).weightSupport
          (A.val '' ((fun x : W => (ε / 3) • x) '' conePolarTemplate K))) (β'.val j)) =
      (ε / 3) * ∑ j, M.coneIdealWordCost (heightConePreimage T eW K)
        (M.polarProbeWidths T hunimod eW K) (β.val j) := by
  rw [M.transformed_polar_ideal_exponent T hunimod eW K A bN bI' (by positivity) β' hβ',
    M.polar_templateSupport_eq T hunimod eW K bN bI β hβ (by positivity),
    M.polar_templateSupport_eq T hunimod eW K bN bI β hβ (by positivity)]
  ring

end PolycyclicRecognition.CartanWordModel

end

end OAI
