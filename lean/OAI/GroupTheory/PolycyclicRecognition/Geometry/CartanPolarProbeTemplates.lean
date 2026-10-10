import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanBoxExponents
import OAI.GroupTheory.PolycyclicRecognition.Algebra.ConePolarTemplate
import OAI.GroupTheory.PolycyclicRecognition.Analysis.ConeIdealBoxCalculus

namespace OAI

/-! # Actual polar-template widths for the three probe boxes -/

noncomputable section
namespace PolycyclicRecognition.CartanWordModel

open Module LieAlgebra Set

variable {L W : Type*} [LieRing L] [LieAlgebra ℝ L] [FiniteDimensional ℝ L]
  {H : LieSubalgebra ℝ L} [H.IsCartanSubalgebra] (M : CartanWordModel H)
  {a : ℕ} (T : TriangularAdjoint L a)
  (hunimod : ∀ x : L, LinearMap.trace ℝ L (ad ℝ L x) = 0)
  [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
  (eW : HeightSpace T.character ≃ₗ[ℝ] W)

/-- Pull a cone of height functionals back to the actual Cartan weights. -/
def heightConePreimage (K : ProperCone ℝ (StrongDual ℝ W)) : Set (H →ₗ[ℝ] ℝ) :=
  {χ | ((χ.comp (cartanHeightSection T H)).comp eW.symm.toLinearMap).toContinuousLinearMap ∈ K}

def polarProbeWidths (K : ProperCone ℝ (StrongDual ℝ W)) : Fin M.letterCount → ℝ :=
  fun i => conePolarWidth K ((M.supportIn T hunimod eW).weight i).toContinuousLinearMap

theorem weight_mem_heightConePreimage_iff (K : ProperCone ℝ (StrongDual ℝ W))
    (i : Fin M.letterCount) :
    (M.weight i : H →ₗ[ℝ] ℝ) ∈ heightConePreimage T eW K ↔
      ((M.supportIn T hunimod eW).weight i).toContinuousLinearMap ∈ K := Iff.rfl

/-- The support exponents of the normalized probe templates are exactly
the polar widths multiplied by their radii. -/
theorem weightSupport_polar_smul (K : ProperCone ℝ (StrongDual ℝ W))
    {c : ℝ} (hc : 0 ≤ c) (i : Fin M.letterCount) :
    (M.supportIn T hunimod eW).weightSupport
      ((fun x : W => c • x) '' conePolarTemplate K) i =
      c * conePolarWidth K ((M.supportIn T hunimod eW).weight i).toContinuousLinearMap :=
  conePolarWidth_smul K ((M.supportIn T hunimod eW).weight i).toContinuousLinearMap hc

theorem polar_width_nonneg (K : ProperCone ℝ (StrongDual ℝ W))
    (i : Fin M.letterCount) :
    0 ≤ conePolarWidth K ((M.supportIn T hunimod eW).weight i).toContinuousLinearMap :=
  conePolarWidth_nonneg K _

theorem polar_width_zero (K : ProperCone ℝ (StrongDual ℝ W))
    (i : Fin M.letterCount) (hi : (M.weight i : H →ₗ[ℝ] ℝ) ∈ heightConePreimage T eW K) :
    conePolarWidth K ((M.supportIn T hunimod eW).weight i).toContinuousLinearMap = 0 :=
  conePolarWidth_eq_zero K ((M.weight_mem_heightConePreimage_iff T hunimod eW K i).mp hi)

theorem polar_width_pos (K : ProperCone ℝ (StrongDual ℝ W))
    (i : Fin M.letterCount) (hi : (M.weight i : H →ₗ[ℝ] ℝ) ∉ heightConePreimage T eW K) :
    0 < conePolarWidth K ((M.supportIn T hunimod eW).weight i).toContinuousLinearMap :=
  conePolarWidth_pos K (fun h => hi ((M.weight_mem_heightConePreimage_iff T hunimod eW K i).mpr h))

/-- The normalized source templates satisfy every compactness, convexity
and zero-width condition required by the actual three-chain construction. -/
theorem polar_probe_template_properties (K : ProperCone ℝ (StrongDual ℝ W))
    {c : ℝ} (hc : 0 ≤ c) :
    let E := (fun x : W => c • x) '' conePolarTemplate K
    IsCompact E ∧ Convex ℝ E ∧ (0 : W) ∈ E ∧
      (∀ i, 0 ≤ (M.supportIn T hunimod eW).weightSupport E i) ∧
      ∀ i, (M.weight i : H →ₗ[ℝ] ℝ) ∈ heightConePreimage T eW K →
        (M.supportIn T hunimod eW).weightSupport E i = 0 := by
  dsimp only
  refine ⟨(isCompact_conePolarTemplate K).image (continuous_const.smul continuous_id),
    ?_, ⟨0, zero_mem_conePolarTemplate K, smul_zero c⟩, ?_, ?_⟩
  · rintro _ ⟨u, hu, rfl⟩ _ ⟨v, hv, rfl⟩ a b ha hb hab
    refine ⟨a • u + b • v, convex_conePolarTemplate K hu hv ha hb hab, ?_⟩
    simp only [smul_add, smul_smul, mul_comm c]
  · intro i
    rw [M.weightSupport_polar_smul T hunimod eW K hc]
    exact mul_nonneg hc (M.polar_width_nonneg T hunimod eW K i)
  · intro i hi
    rw [M.weightSupport_polar_smul T hunimod eW K hc,
      M.polar_width_zero T hunimod eW K i hi, mul_zero]

/-- One actual mixed-word basis maximizes every nonnegative multiple of
the polar template, including all three radii in the strict-width tiling. -/
theorem exists_polar_probe_basis (K : ProperCone ℝ (StrongDual ℝ W))
    (bI : Basis (Fin (finrank ℝ (M.coneWordIdeal (heightConePreimage T eW K))))
      ℝ (M.coneWordIdeal (heightConePreimage T eW K))) :
    ∃ β : M.ConeIdealBases (heightConePreimage T eW K),
      M.IsMaximizingConeIdealBasis (heightConePreimage T eW K) bI
        (fun i => conePolarWidth K
          ((M.supportIn T hunimod eW).weight i).toContinuousLinearMap) β ∧
      ∀ c : ℝ, 0 ≤ c → M.IsMaximizingConeIdealBasis (heightConePreimage T eW K) bI
        ((M.supportIn T hunimod eW).weightSupport
          ((fun x : W => c • x) '' conePolarTemplate K)) β := by
  obtain ⟨β, hβ⟩ := M.exists_maximizing_coneIdealBasis (heightConePreimage T eW K) bI
    (fun i => conePolarWidth K ((M.supportIn T hunimod eW).weight i).toContinuousLinearMap)
  refine ⟨β, hβ, ?_⟩
  intro c hc
  have he : (M.supportIn T hunimod eW).weightSupport
      ((fun x : W => c • x) '' conePolarTemplate K) =
      fun i => c * conePolarWidth K ((M.supportIn T hunimod eW).weight i).toContinuousLinearMap := by
    funext i
    exact M.weightSupport_polar_smul T hunimod eW K hc i
  rw [he]
  exact M.maximizing_coneIdealBasis_smul (heightConePreimage T eW K) bI _ β hβ hc

end PolycyclicRecognition.CartanWordModel

end

end OAI
