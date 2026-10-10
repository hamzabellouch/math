import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanBoxScaling
import OAI.GroupTheory.PolycyclicRecognition.Analysis.BoxWordExpansion

namespace OAI

/-! # Word coefficients of the actual Cartan action inside a template -/

noncomputable section

namespace PolycyclicRecognition.CartanWordModel

open Module LieAlgebra LieModule
open scoped BigOperators

variable {L W : Type*} [LieRing L] [LieAlgebra ℝ L] [FiniteDimensional ℝ L]
  {H : LieSubalgebra ℝ L} [H.IsCartanSubalgebra] (M : CartanWordModel H)
  {n : ℕ} (T : TriangularAdjoint L n)
  (hunimod : ∀ x : L, LinearMap.trace ℝ L (ad ℝ L x) = 0)
  [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
  (eW : HeightSpace T.character ≃ₗ[ℝ] W)

/-- Containment of the Cartan height in a homothetic template gives an
actual word expansion of the conjugated logarithm. Its only loss is a
fixed polynomial in the Cartan logarithm, with the template exponent
retained for each individual word. -/
theorem exists_adjoint_word_coefficient_bound
    (b₀ : Basis (Fin (finrank ℝ (cartanRootIdeal H))) ℝ (cartanRootIdeal H)) :
    ∃ (A : ℝ) (p : ℕ), 0 ≤ A ∧ ∀ {E : Set W}, IsCompact E → E.Nonempty →
      ∀ {t : ℝ}, 0 ≤ t → ∀ (β : M.Bases),
      IsMaximizingColumnBasis (wordListCoordinates M.letter M.wordList b₀)
        (M.boxCost T hunimod eW E) β.val →
      ∀ (γ : M.Bases) (r : ℝ), 0 ≤ r → ∀ (h : H) (w : W),
      w ∈ (fun x => t • x) '' E →
      eW (heightProjection T.character (h : L)) = r • w →
      ∀ v : cartanRootIdeal H, ∃ a : M.wordList → ℝ,
        (∀ u, |a u| ≤ A * (1 + ‖(Module.finBasis ℝ H).equivFun h‖) ^ p *
          ‖(WordBasisSelections.basis M.letter M.wordList γ).equivFun v‖ *
            Real.exp (r * (t * M.boxCost T hunimod eW E u))) ∧
        ∑ u, a u • evalBracketWord M.letter u = cartanIdealAdjointAutomorphism T H h v := by
  obtain ⟨A, p, hA, hb⟩ := M.exists_controlled_adjoint_bound T hunimod eW b₀
  refine ⟨(finrank ℝ (cartanRootIdeal H) : ℝ) * A, p, by positivity, ?_⟩
  intro E hE hne t ht β hβ γ r hr h w hw hh v
  have hc : IsCompact ((fun x : W => t • x) '' E) :=
    hE.image (continuous_const.smul continuous_id : Continuous (fun x : W => t • x))
  have hnorm := hb hc (hne.image _) β
    (M.maximizing_box_basis_smul T hunimod eW b₀ hE hne ht β hβ)
    γ r hr h w hw hh v
  obtain ⟨a, ha, he⟩ := exists_word_expansion_of_rescaled_norm_le
    M.letter M.wordList β (M.boxCost T hunimod eW ((fun x => t • x) '' E)) r
    (by positivity) (cartanIdealAdjointAutomorphism T H h v) hnorm
  refine ⟨a, fun u => (ha u).trans_eq ?_, he⟩
  rw [M.boxCost_image_smul T hunimod eW hE hne ht]
  ring

end PolycyclicRecognition.CartanWordModel

end

end OAI
