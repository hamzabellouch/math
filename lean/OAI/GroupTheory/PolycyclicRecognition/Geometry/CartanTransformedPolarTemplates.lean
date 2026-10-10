import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanPolarProbeTemplates
import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanConeIdealExponent

namespace OAI

/-! # The actual target templates in the offset comparison

The target cone is the inverse image under precomposition by the affine
label. Its vanishing widths and positive ideal widths are consequences of
the source polar template, without requiring the label to preserve a ball.
-/

noncomputable section
namespace PolycyclicRecognition

open Set

variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
  [FiniteDimensional ℝ W]

/-- The target functionals whose pullbacks lie in the source cone. -/
def transformedPolarCone (K : ProperCone ℝ (StrongDual ℝ W)) (A : W ≃ₗ[ℝ] W) :
    ProperCone ℝ (StrongDual ℝ W) :=
  K.comap ((ContinuousLinearMap.compL ℝ W W ℝ).flip
    A.toLinearMap.toContinuousLinearMap)

theorem mem_transformedPolarCone (K : ProperCone ℝ (StrongDual ℝ W))
    (A : W ≃ₗ[ℝ] W) (β : StrongDual ℝ W) :
    β ∈ transformedPolarCone K A ↔ β.comp A.toLinearMap.toContinuousLinearMap ∈ K :=
  Iff.rfl

/-- The exact support width of a transformed and dilated polar template. -/
theorem transformedPolar_width (K : ProperCone ℝ (StrongDual ℝ W))
    (A : W ≃ₗ[ℝ] W) (β : StrongDual ℝ W) {c : ℝ} (hc : 0 ≤ c) :
    sSup (β '' (A '' ((fun x : W => c • x) '' conePolarTemplate K))) =
      c * conePolarWidth K (β.comp A.toLinearMap.toContinuousLinearMap) := by
  rw [image_image]
  exact conePolarWidth_smul K (β.comp A.toLinearMap.toContinuousLinearMap) hc

end PolycyclicRecognition

namespace PolycyclicRecognition.CartanWordModel

open Module LieAlgebra Set
open scoped BigOperators

variable {L W : Type*} [LieRing L] [LieAlgebra ℝ L] [FiniteDimensional ℝ L]
  {H : LieSubalgebra ℝ L} [H.IsCartanSubalgebra] (M : CartanWordModel H)
  {a : ℕ} (T : TriangularAdjoint L a)
  (hunimod : ∀ x : L, LinearMap.trace ℝ L (ad ℝ L x) = 0)
  [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
  (eW : HeightSpace T.character ≃ₗ[ℝ] W)

theorem weightSupport_transformed_polar (K : ProperCone ℝ (StrongDual ℝ W))
    (A : W ≃ₗ[ℝ] W) {c : ℝ} (hc : 0 ≤ c) (i : Fin M.letterCount) :
    (M.supportIn T hunimod eW).weightSupport
      (A '' ((fun x : W => c • x) '' conePolarTemplate K)) i =
      c * conePolarWidth K
        (((M.supportIn T hunimod eW).weight i).toContinuousLinearMap.comp
          A.toLinearMap.toContinuousLinearMap) :=
  transformedPolar_width K A
    ((M.supportIn T hunimod eW).weight i).toContinuousLinearMap hc

/-- Both target path templates have zero quotient widths and strictly
positive widths outside the pulled-back cone. -/
theorem transformed_polar_width_properties (K : ProperCone ℝ (StrongDual ℝ W))
    (A : W ≃ₗ[ℝ] W) {c : ℝ} (hc : 0 < c) :
    let E := A '' ((fun x : W => c • x) '' conePolarTemplate K)
    let C := heightConePreimage T eW (transformedPolarCone K A)
    IsCompact E ∧ Convex ℝ E ∧ (0 : W) ∈ E ∧
      (∀ i, 0 ≤ (M.supportIn T hunimod eW).weightSupport E i) ∧
      (∀ i, (M.weight i : H →ₗ[ℝ] ℝ) ∈ C →
        (M.supportIn T hunimod eW).weightSupport E i = 0) ∧
      (∀ i, (M.weight i : H →ₗ[ℝ] ℝ) ∉ C →
        0 < (M.supportIn T hunimod eW).weightSupport E i) := by
  dsimp only
  obtain ⟨hcompact, hconv, hzero, _, _⟩ :=
    M.polar_probe_template_properties T hunimod eW K hc.le
  refine ⟨hcompact.image A.continuous_of_finiteDimensional,
    hconv.linear_image A.toLinearMap, ⟨0, hzero, A.map_zero⟩, ?_, ?_, ?_⟩
  · intro i
    rw [M.weightSupport_transformed_polar T hunimod eW K A hc.le i]
    exact mul_nonneg hc.le (conePolarWidth_nonneg K _)
  · intro i hi
    have hi' := (M.weight_mem_heightConePreimage_iff T hunimod eW
      (transformedPolarCone K A) i).mp hi
    change (((M.supportIn T hunimod eW).weight i).toContinuousLinearMap.comp
      A.toLinearMap.toContinuousLinearMap) ∈ K at hi'
    rw [M.weightSupport_transformed_polar T hunimod eW K A hc.le i,
      conePolarWidth_eq_zero K hi', mul_zero]
  · intro i hi
    have hi' : (((M.supportIn T hunimod eW).weight i).toContinuousLinearMap.comp
        A.toLinearMap.toContinuousLinearMap) ∉ K := by
      intro h
      exact hi ((M.weight_mem_heightConePreimage_iff T hunimod eW
        (transformedPolarCone K A) i).mpr h)
    rw [M.weightSupport_transformed_polar T hunimod eW K A hc.le i]
    exact mul_pos hc (conePolarWidth_pos K hi')

/-- One target ideal basis maximizes every radius used by the path comparison. -/
theorem exists_transformed_polar_probe_basis (K : ProperCone ℝ (StrongDual ℝ W))
    (A : W ≃ₗ[ℝ] W)
    (bI : Basis (Fin (finrank ℝ
      (M.coneWordIdeal (heightConePreimage T eW (transformedPolarCone K A)))) )
      ℝ (M.coneWordIdeal (heightConePreimage T eW (transformedPolarCone K A)))) :
    ∃ β : M.ConeIdealBases (heightConePreimage T eW (transformedPolarCone K A)),
      ∀ c : ℝ, 0 ≤ c →
        M.IsMaximizingConeIdealBasis (heightConePreimage T eW (transformedPolarCone K A)) bI
          ((M.supportIn T hunimod eW).weightSupport
            (A '' ((fun x : W => c • x) '' conePolarTemplate K))) β := by
  let C := heightConePreimage (H := H) T eW (transformedPolarCone K A)
  let s := fun i => conePolarWidth K
    (((M.supportIn T hunimod eW).weight i).toContinuousLinearMap.comp
      A.toLinearMap.toContinuousLinearMap)
  obtain ⟨β, hβ⟩ := M.exists_maximizing_coneIdealBasis C bI s
  refine ⟨β, ?_⟩
  intro c hc
  have he : (M.supportIn T hunimod eW).weightSupport
      (A '' ((fun x : W => c • x) '' conePolarTemplate K)) = fun i => c * s i := by
    funext i
    exact M.weightSupport_transformed_polar T hunimod eW K A hc i
  rw [he]
  exact M.maximizing_coneIdealBasis_smul C bI s β hβ hc

/-- The target ideal volume exponent equals the original polar-template
exponent under an actual template-symmetry label. -/
theorem transformed_polar_ideal_exponent (K : ProperCone ℝ (StrongDual ℝ W))
    (A : templateSymmetryGroup (M.supportIn T hunimod eW))
    (bN : Basis (Fin (finrank ℝ (cartanRootIdeal H))) ℝ (cartanRootIdeal H))
    (bI : Basis (Fin (finrank ℝ
      (M.coneWordIdeal (heightConePreimage T eW (transformedPolarCone K A.val)))))
      ℝ (M.coneWordIdeal (heightConePreimage T eW (transformedPolarCone K A.val))))
    {c : ℝ} (hc : 0 < c)
    (β : M.ConeIdealBases (heightConePreimage T eW (transformedPolarCone K A.val)))
    (hβ : M.IsMaximizingConeIdealBasis
      (heightConePreimage T eW (transformedPolarCone K A.val)) bI
      ((M.supportIn T hunimod eW).weightSupport
        (A.val '' ((fun x : W => c • x) '' conePolarTemplate K))) β) :
    (∑ j, M.coneIdealWordCost
      (heightConePreimage T eW (transformedPolarCone K A.val))
      ((M.supportIn T hunimod eW).weightSupport
        (A.val '' ((fun x : W => c • x) '' conePolarTemplate K))) (β.val j)) =
      (M.supportIn T hunimod eW).templateSupport
        ((fun x : W => c • x) '' conePolarTemplate K) := by
  obtain ⟨hcompact, hconv, hzero, _, _⟩ :=
    M.polar_probe_template_properties T hunimod eW K hc.le
  obtain ⟨_, _, _, hs, hz, _⟩ :=
    M.transformed_polar_width_properties T hunimod eW K A.val hc
  exact M.sum_coneIdealCost_image_templateSymmetry T hunimod eW _ bN bI _
    hcompact ⟨0, hzero⟩ hconv A hs hz β hβ

end PolycyclicRecognition.CartanWordModel

end

end OAI
