import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanAdjointAction

namespace OAI

/-! # Actual Cartan conjugation and shifted boxes

The full Lie action integrates to the nilpotent group. A faithful compatible
representation identifies this automorphism with ambient conjugation. The
resulting box estimate retains the polynomial residual factor and the exact
canonical-height translation.
-/

noncomputable section

namespace PolycyclicRecognition.CartanWordModel

open Module LieAlgebra LieModule
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

/-- Integration of the complete adjoint action, including its residual part. -/
def adjointGroupAutomorphism (h : H) : N ≃* N :=
  integrateNilpotentLieEquiv eN Exp hbij dynkin hExp M.bound_zero
    (cartanIdealAdjointAutomorphism T H h)

section Representation

variable {A G : Type*} [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A] [Group G]

attribute [local instance 100] LieRing.ofAssociativeRing

/-- Compatibility of exponentials in a faithful representation identifies
the constructed automorphism with actual ambient conjugation. -/
theorem adjointGroupAutomorphism_eq_conjugation
    (j : L →ₗ⁅ℝ⁆ A) (ρ : G →* Aˣ) (hρ : Function.Injective ρ)
    (ι : N →* G) (d : H → G)
    (hN : ∀ x : cartanRootIdeal H, ρ (ι (Exp (eN x))) = algebraExpUnit (j x))
    (hd : ∀ h, ρ (d h) = algebraExpUnit (j h)) (h : H) (g : N) :
    ι (M.adjointGroupAutomorphism T eN Exp hExp hbij dynkin h g) =
      d h * ι g * (d h)⁻¹ := by
  obtain ⟨x, rfl⟩ := (hbij.comp eN.bijective).surjective g
  apply hρ
  change ρ (ι (integrateNilpotentLieEquiv eN Exp hbij dynkin hExp M.bound_zero
    (cartanIdealAdjointAutomorphism T H h) (Exp (eN x)))) = _
  rw [integrateNilpotentLieEquiv_apply_exp, hN, map_mul, map_mul, map_inv, hd]
  change algebraExpUnit (j (cartanIdealAdjointAutomorphism T H h x : L)) =
    algebraExpUnit (j h) * ρ (ι (Exp (eN x))) * (algebraExpUnit (j h))⁻¹
  rw [hN]
  rw [represented_adjoint_ideal T H j h x]
  exact algebraExpUnit_conj (algebraExpUnit (j h)) (j x)

end Representation

variable (hunimod : ∀ x : L, LinearMap.trace ℝ L (ad ℝ L x) = 0)
  {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
  (eW : HeightSpace T.character ≃ₗ[ℝ] W)

omit hunimod [FiniteDimensional ℝ W] in
/-- Canonical height determines the scalar factor of the actual action. -/
theorem adjointGroupAutomorphism_factor (h : H) (w : W) (r : ℝ)
    (hh : eW (heightProjection T.character (h : L)) = r • w) (g : N) :
    M.adjointGroupAutomorphism T eN Exp hExp hbij dynkin h g =
      M.groupWeightDilation T eW eN Exp hExp hbij dynkin w r
        (M.residualGroupAutomorphism T eN Exp hExp hbij dynkin h g) := by
  have he : cartanIdealWeightDilation T H h =
      cartanIdealWeightDilation T H (r • cartanHeightSection T H (eW.symm w)) := by
    apply cartanIdealWeightDilation_eq_of_height_eq T H
    apply eW.injective
    change eW (heightProjection T.character (h : L)) =
      eW (heightProjection T.character (r • (cartanHeightSection T H (eW.symm w) : L)))
    rw [map_smul, cartanHeightSection_height, map_smul, eW.apply_symm_apply, hh]
  obtain ⟨x, rfl⟩ := (hbij.comp eN.bijective).surjective g
  change integrateNilpotentLieEquiv eN Exp hbij dynkin hExp M.bound_zero
      (cartanIdealAdjointAutomorphism T H h) (Exp (eN x)) =
    integrateNilpotentLieEquiv eN Exp hbij dynkin hExp M.bound_zero
      (cartanIdealWeightDilation T H (r • cartanHeightSection T H (eW.symm w)))
      (integrateNilpotentLieEquiv eN Exp hbij dynkin hExp M.bound_zero
        (cartanIdealResidualAutomorphism T H h) (Exp (eN x)))
  simp only [integrateNilpotentLieEquiv_apply_exp]
  change Exp (eN (cartanIdealWeightDilation T H h
      (cartanIdealResidualAutomorphism T H h x))) = _
  rw [he]

/-- The actual adjoint action translates the template by canonical height,
with a polynomial loss in the Cartan logarithm only. -/
theorem exists_adjoint_groupBox_bound
    (b₀ : Basis (Fin (finrank ℝ (cartanRootIdeal H))) ℝ (cartanRootIdeal H)) :
    ∃ (A : ℝ) (p : ℕ), 0 ≤ A ∧ ∀ {E : Set W}, IsCompact E → E.Nonempty →
      ∀ β : M.Bases,
      IsMaximizingColumnBasis (wordListCoordinates M.letter M.wordList b₀)
        (M.boxCost T hunimod eW E) β.val →
      ∀ r : ℝ, 0 ≤ r → ∀ (h : H) (w : W),
      eW (heightProjection T.character (h : L)) = r • w →
      ∀ (R : ℝ) (g : N), g ∈ M.groupBox T hunimod eW (Exp ∘ eN) E β r R →
      M.adjointGroupAutomorphism T eN Exp hExp hbij dynkin h g ∈
        M.groupBox T hunimod eW (Exp ∘ eN) ((fun x => x + w) '' E) β r
          (A * (1 + ‖(Module.finBasis ℝ H).equivFun h‖) ^ p * R) := by
  obtain ⟨A, p, hA, hb⟩ :=
    M.exists_shifted_groupBox_bound T eN Exp hExp hbij dynkin hunimod eW b₀
  refine ⟨A, p, hA, ?_⟩
  intro E hE hne β hβ r hr h w hh R g hg
  rw [M.adjointGroupAutomorphism_factor T eN Exp hExp hbij dynkin eW h w r hh]
  exact hb hE hne β hβ r hr h w R g hg

end PolycyclicRecognition.CartanWordModel

end

end OAI
