import OAI.GroupTheory.PolycyclicRecognition.Algebra.RayIdealTemplates
import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanBoxDilation
import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanAdjointAction

namespace OAI

/-!+# Fixed ideal displacements along a Cartan ray

The residual adjoint part costs a polynomial, which is absorbed by the
strict mixed-word widths. Exact weight dilation translates the template.
This gives small coordinates for the actual conjugated displacement in
the template translated to contain zero, as required by Cartan paths.
-/

noncomputable section
namespace PolycyclicRecognition.CartanWordModel

open Module LieAlgebra LieModule Filter Set
open scoped BigOperators Topology

variable {L W : Type*} [LieRing L] [LieAlgebra ℝ L] [FiniteDimensional ℝ L]
  {H : LieSubalgebra ℝ L} [H.IsCartanSubalgebra] (M : CartanWordModel H)
  {a : ℕ} (T : TriangularAdjoint L a)
  (hunimod : ∀ x : L, LinearMap.trace ℝ L (ad ℝ L x) = 0)
  [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
  (eW : HeightSpace T.character ≃ₗ[ℝ] W)

/-- Polynomial residual distortion is absorbed for a fixed ideal vector. -/
theorem fixed_ideal_residual_box_norm_tendsto_zero
    (C : Set (H →ₗ[ℝ] ℝ)) (E : Set W) (hE : IsCompact E) (hne : E.Nonempty)
    (hpos : ∀ w : M.coneMixedWords C, 0 < M.boxCost T hunimod eW E w.val)
    (b₀ : Basis (Fin (finrank ℝ (cartanRootIdeal H))) ℝ (cartanRootIdeal H))
    (β : ℕ → M.Bases)
    (hβ : ∀ n, IsMaximizingColumnBasis (wordListCoordinates M.letter M.wordList b₀)
      (M.boxCost T hunimod eW E) (β n).val)
    (h : H) (x : M.coneWordIdeal C) :
    Tendsto (fun n : ℕ =>
      ‖(M.boxBasis T hunimod eW E (β n) n).equivFun
        (cartanIdealResidualAutomorphism T H (-(n : ℝ) • h) x)‖)
      atTop (𝓝 0) := by
  obtain ⟨A, p, hA, hb⟩ := M.exists_residual_box_bound T hunimod eW b₀
  let B := ‖(Module.finBasis ℝ H).equivFun h‖
  have hB : 0 ≤ B := norm_nonneg _
  have hlim := M.fixed_ideal_polynomial_box_norm_tendsto_zero T hunimod eW
    C E hpos b₀ β hβ x (A * (1 + B) ^ p) (by positivity) p
  apply squeeze_zero (fun n => norm_nonneg _) _ hlim
  intro n
  have hnorm : ‖(Module.finBasis ℝ H).equivFun (-(n : ℝ) • h)‖ = (n : ℝ) * B := by
    rw [map_smul, norm_smul, Real.norm_eq_abs, abs_neg,
      abs_of_nonneg (Nat.cast_nonneg n)]
  have hh := hb hE hne (β n) (hβ n) n (Nat.cast_nonneg n) (-(n : ℝ) • h) x
  rw [hnorm] at hh
  apply hh.trans
  have hbase : 1 + (n : ℝ) * B ≤ (1 + B) * (1 + n) := by nlinarith
  calc
    A * (1 + (n : ℝ) * B) ^ p * _ ≤
        A * ((1 + B) * (1 + n)) ^ p * _ := by gcongr
    _ = _ := by rw [mul_pow]; ring

/-- The full adjoint action on a fixed ideal vector has vanishing
coordinates in the translated template. The bases are the same actual
word bases, whose maximizing property is translation invariant. -/
theorem fixed_ideal_adjoint_shifted_box_norm_tendsto_zero
    (C : Set (H →ₗ[ℝ] ℝ)) (E : Set W) (hE : IsCompact E) (hne : E.Nonempty)
    (hpos : ∀ w : M.coneMixedWords C, 0 < M.boxCost T hunimod eW E w.val)
    (b₀ : Basis (Fin (finrank ℝ (cartanRootIdeal H))) ℝ (cartanRootIdeal H))
    (β : ℕ → M.Bases)
    (hβ : ∀ n, IsMaximizingColumnBasis (wordListCoordinates M.letter M.wordList b₀)
      (M.boxCost T hunimod eW E) (β n).val)
    (v₀ : W) (x : M.coneWordIdeal C) :
    Tendsto (fun n : ℕ =>
      ‖(M.boxBasis T hunimod eW ((fun v => v - v₀) '' E) (β n) n).equivFun
        (cartanIdealAdjointAutomorphism T H
          (-(n : ℝ) • cartanHeightSection T H (eW.symm v₀)) x)‖)
      atTop (𝓝 0) := by
  have hlim := M.fixed_ideal_residual_box_norm_tendsto_zero T hunimod eW
    C E hE hne hpos b₀ β hβ (cartanHeightSection T H (eW.symm v₀)) x
  apply hlim.congr
  intro n
  have hb := M.idealWeightDilation_boxBasis T hunimod eW hE hne (-v₀) (β n) n
  have hdir : (n : ℝ) • cartanHeightSection T H (eW.symm (-v₀)) =
      -(n : ℝ) • cartanHeightSection T H (eW.symm v₀) := by
    rw [map_neg, map_neg, smul_neg, neg_smul]
  rw [hdir] at hb
  have hset : ((fun v => v + -v₀) '' E) = ((fun v => v - v₀) '' E) := by
    simp only [sub_eq_add_neg]
  rw [hset] at hb
  rw [← hb]
  let D := cartanIdealWeightDilation T H
    (-(n : ℝ) • cartanHeightSection T H (eW.symm v₀))
  let y := cartanIdealResidualAutomorphism T H
    (-(n : ℝ) • cartanHeightSection T H (eW.symm v₀)) x
  change ‖(M.boxBasis T hunimod eW E (β n) n).equivFun y‖ =
    ‖(M.boxBasis T hunimod eW E (β n) n).equivFun (D.symm (D y))‖
  rw [D.symm_apply_apply]

end PolycyclicRecognition.CartanWordModel

end

end OAI
