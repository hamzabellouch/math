import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanControlledAction

namespace OAI

/-! # Polynomial bounds for products of controlled Cartan increments

Each increment begins in a fixed nilpotent coordinate box. Its Cartan height
lies in a scaled template, and its Cartan logarithm has a polynomial bound.
The resulting product remains in the template box with polynomial radius.
All constants are uniform over templates, maximizing bases and scales.
-/

noncomputable section

namespace PolycyclicRecognition.CartanWordModel

open Module LieAlgebra LieModule
open scoped Manifold

variable {L : Type*} [LieRing L] [LieAlgebra ℝ L] [FiniteDimensional ℝ L]
  {H : LieSubalgebra ℝ L} [H.IsCartanSubalgebra] (M : CartanWordModel H)
  {n : ℕ} (T : TriangularAdjoint L n)
  (hunimod : ∀ x : L, LinearMap.trace ℝ L (ad ℝ L x) = 0)
  {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
  (eW : HeightSpace T.character ≃ₗ[ℝ] W)
  {EN N : Type*} [NormedAddCommGroup EN] [NormedSpace ℝ EN]
  [FiniteDimensional ℝ EN] [TopologicalSpace N] [ChartedSpace EN N] [Group N]
  [LieGroup (𝓘(ℝ, EN)) ⊤ N] [T2Space N]
  (eN : cartanRootIdeal H ≃ₗ⁅ℝ⁆ GroupLieAlgebra (𝓘(ℝ, EN)) N)
  (Exp : GroupLieAlgebra (𝓘(ℝ, EN)) N → N) (hExp : IsGroupExponential Exp)
  (hbij : Function.Bijective Exp) (dynkin : NilpotentDynkinExpansionInput EN N)

/-- A controlled Cartan action takes an unscaled box into the template box. -/
theorem exists_controlled_adjoint_group_bound
    (b₀ : Basis (Fin (finrank ℝ (cartanRootIdeal H))) ℝ (cartanRootIdeal H)) :
    ∃ (A : ℝ) (p : ℕ), 0 ≤ A ∧ ∀ {E : Set W}, IsCompact E → E.Nonempty →
      ∀ β : M.Bases,
      IsMaximizingColumnBasis (wordListCoordinates M.letter M.wordList b₀)
        (M.boxCost T hunimod eW E) β.val →
      ∀ (γ : M.Bases) (r : ℝ), 0 ≤ r → ∀ (h : H) (w : W), w ∈ E →
      eW (heightProjection T.character (h : L)) = r • w → ∀ (R : ℝ) (g : N),
      g ∈ exponentialCoordinateBox (Exp ∘ eN)
        (WordBasisSelections.basis M.letter M.wordList γ) R →
      M.adjointGroupAutomorphism T eN Exp hExp hbij dynkin h g ∈
        M.groupBox T hunimod eW (Exp ∘ eN) E β r
          (A * (1 + ‖(Module.finBasis ℝ H).equivFun h‖) ^ p * R) := by
  obtain ⟨A, p, hA, hb⟩ := M.exists_controlled_adjoint_bound T hunimod eW b₀
  refine ⟨A, p, hA, ?_⟩
  intro E hE hne β hβ γ r hr h w hw hh R g hg
  obtain ⟨x, rfl, hx⟩ := hg
  refine ⟨cartanIdealAdjointAutomorphism T H h x, ?_, ?_⟩
  · exact (integrateNilpotentLieEquiv_apply_exp eN Exp hbij dynkin hExp M.bound_zero
      (cartanIdealAdjointAutomorphism T H h) x).symm
  · exact (hb hE hne β hβ γ r hr h w hw hh x).trans
      (mul_le_mul_of_nonneg_left hx (mul_nonneg hA (pow_nonneg (by positivity) _)))

/-- Polynomial Cartan logarithms give a polynomial radius for the full
product, even when the height template and scale vary. -/
theorem exists_controlled_product_bound
    (b₀ : Basis (Fin (finrank ℝ (cartanRootIdeal H))) ℝ (cartanRootIdeal H))
    {B R : ℝ} (hB : 0 ≤ B) (hR : 0 ≤ R) (k : ℕ) :
    ∃ (C : ℝ) (q : ℕ), 0 ≤ C ∧ ∀ {E : Set W}, IsCompact E → E.Nonempty →
      ∀ β : M.Bases,
      IsMaximizingColumnBasis (wordListCoordinates M.letter M.wordList b₀)
        (M.boxCost T hunimod eW E) β.val →
      ∀ (γ : M.Bases) (r : ℝ), 0 ≤ r → ∀ (m : ℕ) (h : Fin m → H) (w : Fin m → W),
      (∀ i, w i ∈ E) →
      (∀ i, eW (heightProjection T.character (h i : L)) = r • w i) →
      (∀ i, ‖(Module.finBasis ℝ H).equivFun (h i)‖ ≤ B * (1 + (m : ℝ)) ^ k) →
      ∀ g : Fin m → N,
      (∀ i, g i ∈ exponentialCoordinateBox (Exp ∘ eN)
        (WordBasisSelections.basis M.letter M.wordList γ) R) →
      (List.ofFn (fun i => M.adjointGroupAutomorphism T eN Exp hExp hbij dynkin (h i) (g i))).prod ∈
        M.groupBox T hunimod eW (Exp ∘ eN) E β r (C * (1 + (m : ℝ)) ^ q) := by
  obtain ⟨A, p, hA, hact⟩ :=
    M.exists_controlled_adjoint_group_bound T hunimod eW eN Exp hExp hbij dynkin b₀
  obtain ⟨C, hC, hprod⟩ := M.exists_groupBox_product_bound T hunimod eW eN Exp hExp dynkin b₀
  let D := A * (1 + B) ^ p * R
  have hD : 0 ≤ D := by dsimp [D]; positivity
  refine ⟨C * (1 + D) ^ M.bound, M.bound + (k * p) * M.bound, by positivity, ?_⟩
  intro E hE hne β hβ γ r hr m h w hw hh hlog g hg
  let s : ℝ := 1 + (m : ℝ)
  have hs : 1 ≤ s := le_add_of_nonneg_right (Nat.cast_nonneg _)
  have hsp : 1 ≤ s ^ k := one_le_pow₀ hs
  have hinc (i : Fin m) : M.adjointGroupAutomorphism T eN Exp hExp hbij dynkin (h i) (g i) ∈
      M.groupBox T hunimod eW (Exp ∘ eN) E β r (D * s ^ (k * p)) := by
    obtain ⟨x, hx, hbound⟩ := hact hE hne β hβ γ r hr (h i) (w i) (hw i) (hh i) R (g i) (hg i)
    refine ⟨x, hx, hbound.trans ?_⟩
    have hi : 1 + ‖(Module.finBasis ℝ H).equivFun (h i)‖ ≤ (1 + B) * s ^ k := by
      have hi := hlog i
      change ‖(Module.finBasis ℝ H).equivFun (h i)‖ ≤ B * s ^ k at hi
      nlinarith
    calc
      _ ≤ A * ((1 + B) * s ^ k) ^ p * R := by gcongr
      _ = _ := by rw [mul_pow, ← pow_mul]; ring
  obtain ⟨x, hx, hbound⟩ := hprod E β hβ r hr m (D * s ^ (k * p))
    (mul_nonneg hD (pow_nonneg (by linarith) _))
    (fun i => M.adjointGroupAutomorphism T eN Exp hExp hbij dynkin (h i) (g i)) hinc
  refine ⟨x, hx, hbound.trans ?_⟩
  have hsp' : 1 ≤ s ^ (k * p) := one_le_pow₀ hs
  have hsum : 1 + D * s ^ (k * p) ≤ (1 + D) * s ^ (k * p) := by nlinarith
  calc
    _ ≤ C * s ^ M.bound * ((1 + D) * s ^ (k * p)) ^ M.bound := by gcongr
    _ = _ := by rw [mul_pow, ← pow_mul, pow_add]; ring

end PolycyclicRecognition.CartanWordModel

end

end OAI
