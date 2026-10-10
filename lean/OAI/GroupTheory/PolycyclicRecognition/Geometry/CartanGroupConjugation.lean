import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanConjugationBounds

namespace OAI

/-! # Group-box bounds for Cartan actions

The finite Dynkin identity integrates the residual Lie automorphism. Its
polynomial box bound and exact weight dilation yield a shifted-box bound.
-/

noncomputable section

namespace PolycyclicRecognition.CartanWordModel

open Module LieModule LieAlgebra
open scoped Manifold

variable {L : Type*} [LieRing L] [LieAlgebra ℝ L] [FiniteDimensional ℝ L]
  {H : LieSubalgebra ℝ L} [H.IsCartanSubalgebra] (M : CartanWordModel H)
  {n : ℕ} (T : TriangularAdjoint L n)
  {EN N : Type*} [NormedAddCommGroup EN] [NormedSpace ℝ EN]
  [FiniteDimensional ℝ EN] [TopologicalSpace N] [ChartedSpace EN N] [Group N]
  [LieGroup (𝓘(ℝ, EN)) ⊤ N] [T2Space N]
  (eN : cartanRootIdeal H ≃ₗ⁅ℝ⁆ GroupLieAlgebra (𝓘(ℝ, EN)) N)
  (Exp : GroupLieAlgebra (𝓘(ℝ, EN)) N → N) (hExp : IsGroupExponential Exp)
  (hbij : Function.Bijective Exp) (dynkin : NilpotentDynkinExpansionInput EN N)

/-- The actual group automorphism induced by the Cartan residual derivation. -/
def residualGroupAutomorphism (h : H) : N ≃* N :=
  integrateNilpotentLieEquiv eN Exp hbij dynkin hExp M.bound_zero
    (cartanIdealResidualAutomorphism T H h)

variable (hunimod : ∀ x : L, LinearMap.trace ℝ L (ad ℝ L x) = 0)
  {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
  (eW : HeightSpace T.character ≃ₗ[ℝ] W)

/-- Residual group actions have a polynomial coordinate bound uniform over
all templates, maximizing bases and scales. -/
theorem exists_residual_groupBox_bound
    (b₀ : Basis (Fin (finrank ℝ (cartanRootIdeal H))) ℝ (cartanRootIdeal H)) :
    ∃ (A : ℝ) (p : ℕ), 0 ≤ A ∧ ∀ {E : Set W}, IsCompact E → E.Nonempty →
      ∀ β : M.Bases,
      IsMaximizingColumnBasis (wordListCoordinates M.letter M.wordList b₀)
        (M.boxCost T hunimod eW E) β.val →
      ∀ r : ℝ, 0 ≤ r → ∀ (h : H) (R : ℝ),
      M.residualGroupAutomorphism T eN Exp hExp hbij dynkin h ''
        M.groupBox T hunimod eW (Exp ∘ eN) E β r R ⊆
        M.groupBox T hunimod eW (Exp ∘ eN) E β r
          (A * (1 + ‖(Module.finBasis ℝ H).equivFun h‖) ^ p * R) := by
  obtain ⟨A, p, hA, hb⟩ := M.exists_residual_box_bound T hunimod eW b₀
  refine ⟨A, p, hA, ?_⟩
  intro E hE hne β hβ r hr h R
  exact image_exponentialCoordinateBox_subset (M.boxBasis T hunimod eW E β r)
    (Exp ∘ eN) (cartanIdealResidualAutomorphism T H h).toLinearEquiv.toLinearMap
    (M.residualGroupAutomorphism T eN Exp hExp hbij dynkin h)
    (integrateNilpotentLieEquiv_apply_exp eN Exp hbij dynkin hExp M.bound_zero
      (cartanIdealResidualAutomorphism T H h))
    (mul_nonneg hA (pow_nonneg (by positivity) _)) (hb hE hne β hβ r hr h) R

/-- Adding the exact scalar action shifts the template, while the residual
action costs only a polynomial factor in the Cartan parameter. -/
theorem exists_shifted_groupBox_bound
    (b₀ : Basis (Fin (finrank ℝ (cartanRootIdeal H))) ℝ (cartanRootIdeal H)) :
    ∃ (A : ℝ) (p : ℕ), 0 ≤ A ∧ ∀ {E : Set W}, IsCompact E → E.Nonempty →
      ∀ β : M.Bases,
      IsMaximizingColumnBasis (wordListCoordinates M.letter M.wordList b₀)
        (M.boxCost T hunimod eW E) β.val →
      ∀ r : ℝ, 0 ≤ r → ∀ (h : H) (w : W) (R : ℝ) (g : N),
      g ∈ M.groupBox T hunimod eW (Exp ∘ eN) E β r R →
      M.groupWeightDilation T eW eN Exp hExp hbij dynkin w r
        (M.residualGroupAutomorphism T eN Exp hExp hbij dynkin h g) ∈
        M.groupBox T hunimod eW (Exp ∘ eN) ((fun x => x + w) '' E) β r
          (A * (1 + ‖(Module.finBasis ℝ H).equivFun h‖) ^ p * R) := by
  obtain ⟨A, p, hA, hb⟩ := M.exists_residual_groupBox_bound T eN Exp hExp hbij dynkin hunimod eW b₀
  refine ⟨A, p, hA, ?_⟩
  intro E hE hne β hβ r hr h w R g hg
  have hx := hb hE hne β hβ r hr h R ⟨g, hg, rfl⟩
  have hy : M.groupWeightDilation T eW eN Exp hExp hbij dynkin w r
      (M.residualGroupAutomorphism T eN Exp hExp hbij dynkin h g) ∈
      M.groupWeightDilation T eW eN Exp hExp hbij dynkin w r ''
        M.groupBox T hunimod eW (Exp ∘ eN) E β r
          (A * (1 + ‖(Module.finBasis ℝ H).equivFun h‖) ^ p * R) := ⟨_, hx, rfl⟩
  rwa [M.groupWeightDilation_box T hunimod eW eN Exp hExp hbij dynkin hE hne] at hy

end PolycyclicRecognition.CartanWordModel

end

end OAI
