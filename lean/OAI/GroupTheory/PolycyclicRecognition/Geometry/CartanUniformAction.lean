import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanActionCoefficients
import OAI.GroupTheory.PolycyclicRecognition.Algebra.PolynomialEnvelopes

namespace OAI

/-! # Common word envelopes for polynomially bounded Cartan samples -/

noncomputable section

namespace PolycyclicRecognition.CartanWordModel

open Module LieAlgebra LieModule Filter
open scoped BigOperators Topology

variable {L W Z : Type*} [LieRing L] [LieAlgebra ℝ L] [FiniteDimensional ℝ L]
  {H : LieSubalgebra ℝ L} [H.IsCartanSubalgebra] (M : CartanWordModel H)
  {n : ℕ} (T : TriangularAdjoint L n)
  (hunimod : ∀ x : L, LinearMap.trace ℝ L (ad ℝ L x) = 0)
  [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
  (eW : HeightSpace T.character ≃ₗ[ℝ] W)

/-- Polynomial control of the sampled Cartan logarithms makes the word
coefficient error subexponential, uniformly over all chart positions. -/
theorem exists_uniform_adjoint_word_envelope
    (b₀ : Basis (Fin (finrank ℝ (cartanRootIdeal H))) ℝ (cartanRootIdeal H))
    {E : Set W} (hE : IsCompact E) (hne : E.Nonempty) {t : ℝ} (ht : 0 ≤ t)
    (β γ : M.Bases)
    (hβ : IsMaximizingColumnBasis (wordListCoordinates M.letter M.wordList b₀)
      (M.boxCost T hunimod eW E) β.val)
    (h : ℝ → Z → H) (w : ℝ → Z → W)
    (hw : ∀ r, 1 ≤ r → ∀ z, w r z ∈ (fun x => t • x) '' E)
    (hh : ∀ r, 1 ≤ r → ∀ z,
      eW (heightProjection T.character (h r z : L)) = r • w r z)
    {B : ℝ} (hB : 0 ≤ B) (q : ℕ)
    (hlog : ∀ r, 1 ≤ r → ∀ z,
      ‖(Module.finBasis ℝ H).equivFun (h r z)‖ ≤ B * (1 + r) ^ q)
    (v : cartanRootIdeal H) :
    ∃ (ε : ℝ → ℝ) (a : ℝ → Z → M.wordList → ℝ),
      (∀ r, 0 ≤ ε r) ∧ Tendsto ε atTop (𝓝 0) ∧
      ∀ r, 1 ≤ r → ∀ z,
        (∀ u, |a r z u| ≤ Real.exp (r * (t * M.boxCost T hunimod eW E u + ε r))) ∧
        ∑ u, a r z u • evalBracketWord M.letter u =
          cartanIdealAdjointAutomorphism T H (h r z) v := by
  classical
  obtain ⟨A, p, hA, hcoeff⟩ := M.exists_adjoint_word_coefficient_bound T hunimod eW b₀
  let V := ‖(WordBasisSelections.basis M.letter M.wordList γ).equivFun v‖
  let D := A * (1 + B) ^ p * V
  have hD : 0 ≤ D := by dsimp [D, V]; positivity
  obtain ⟨ε, hεpos, hε, henv⟩ := exists_polynomial_exp_envelope hD (q * p)
  have hex (r : ℝ) (hr : 1 ≤ r) (z : Z) : ∃ a : M.wordList → ℝ,
      (∀ u, |a u| ≤ Real.exp (r * (t * M.boxCost T hunimod eW E u + ε r))) ∧
      ∑ u, a u • evalBracketWord M.letter u =
        cartanIdealAdjointAutomorphism T H (h r z) v := by
    obtain ⟨a, ha, he⟩ := hcoeff hE hne ht β hβ γ r (by linarith)
      (h r z) (w r z) (hw r hr z) (hh r hr z) v
    refine ⟨a, fun u => (ha u).trans ?_, he⟩
    have hpow : 1 + ‖(Module.finBasis ℝ H).equivFun (h r z)‖ ≤
        (1 + B) * (1 + r) ^ q := by
      have hp1 : 1 ≤ (1 + r) ^ q := one_le_pow₀ (by linarith)
      have hn := hlog r hr z
      nlinarith
    have hpoly : A * (1 + ‖(Module.finBasis ℝ H).equivFun (h r z)‖) ^ p * V ≤
        D * (1 + r) ^ (q * p) := by
      calc
        _ ≤ A * ((1 + B) * (1 + r) ^ q) ^ p * V := by gcongr
        _ = _ := by rw [mul_pow, ← pow_mul]; ring
    calc
      _ ≤ (D * (1 + r) ^ (q * p)) *
          Real.exp (r * (t * M.boxCost T hunimod eW E u)) :=
        mul_le_mul_of_nonneg_right hpoly (Real.exp_pos _).le
      _ ≤ Real.exp (r * ε r) * Real.exp (r * (t * M.boxCost T hunimod eW E u)) :=
        mul_le_mul_of_nonneg_right (henv r hr) (Real.exp_pos _).le
      _ = _ := by rw [← Real.exp_add]; congr 1; ring
  let a : ℝ → Z → M.wordList → ℝ := fun r z =>
    if hr : 1 ≤ r then Classical.choose (hex r hr z) else 0
  refine ⟨ε, a, hεpos, hε, ?_⟩
  intro r hr z
  simpa only [a, dite_eq_left hr] using Classical.choose_spec (hex r hr z)

end PolycyclicRecognition.CartanWordModel

end

end OAI
