import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanUniformAction
import OAI.GroupTheory.PolycyclicRecognition.Geometry.WordChartHeight

namespace OAI

/-! # Cartan word envelopes on the actual bounded coordinate samples -/

noncomputable section

namespace PolycyclicRecognition.CartanWordModel

open Module LieAlgebra LieModule Filter
open scoped BigOperators Topology

variable {L W Z I : Type*} [LieRing L] [LieAlgebra ℝ L] [FiniteDimensional ℝ L]
  {H : LieSubalgebra ℝ L} [H.IsCartanSubalgebra] (M : CartanWordModel H)
  {n : ℕ} (T : TriangularAdjoint L n)
  (hunimod : ∀ x : L, LinearMap.trace ℝ L (ad ℝ L x) = 0)
  [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
  (eW : HeightSpace T.character ≃ₗ[ℝ] W) [Fintype I] [DecidableEq I]

/-- Every bounded set of scaled Cartan chart coordinates whose unscaled
heights lie in the interior template has the required uniform word
envelope. Polynomial logarithm control and exact height scaling are
derived, rather than additional hypotheses. -/
theorem exists_chart_adjoint_word_envelope
    (b₀ : Basis (Fin (finrank ℝ (cartanRootIdeal H))) ℝ (cartanRootIdeal H))
    {E : Set W} (hE : IsCompact E) (hne : E.Nonempty) {t : ℝ} (ht : 0 ≤ t)
    (β γ : M.Bases)
    (hβ : IsMaximizingColumnBasis (wordListCoordinates M.letter M.wordList b₀)
      (M.boxCost T hunimod eW E) β.val)
    (X : I → H) (S : Finset (FreeMagma I)) (βD : WordBasisSelections X S)
    (z : Z → Fin (finrank ℝ H) → ℝ) {R : ℝ} (hR : 0 ≤ R)
    (hz : ∀ a, ‖z a‖ ≤ R)
    (hdomain : ∀ a, eW (heightProjection T.character
      ((WordBasisSelections.basis X S βD).equivFun.symm (z a) : L)) ∈
        (fun x => t • x) '' E)
    (v : cartanRootIdeal H) :
    let bD := fun r => exponentialRescaleBasis (WordBasisSelections.basis X S βD)
      (fun j => (bracketWordLength (βD.val j : FreeMagma I) : ℝ)) (Real.log r)
    ∃ (ε : ℝ → ℝ) (a : ℝ → Z → M.wordList → ℝ),
      (∀ r, 0 ≤ ε r) ∧ Tendsto ε atTop (𝓝 0) ∧
      ∀ r, 1 ≤ r → ∀ u,
        (∀ w, |a r u w| ≤ Real.exp (r * (t * M.boxCost T hunimod eW E w + ε r))) ∧
        ∑ w, a r u w • evalBracketWord M.letter w =
          cartanIdealAdjointAutomorphism T H ((bD r).equivFun.symm (z u)) v := by
  classical
  let bD := WordBasisSelections.basis X S βD
  let cost := fun j => bracketWordLength (βD.val j : FreeMagma I)
  let p := Finset.univ.sup cost
  have hp (j : Fin (finrank ℝ H)) : cost j ≤ p := Finset.le_sup (Finset.mem_univ j)
  let B := (∑ j, ‖(Module.finBasis ℝ H).equivFun (bD j)‖) * R
  have hB : 0 ≤ B := by dsimp [B]; positivity
  let h := fun r u =>
    (exponentialRescaleBasis bD (fun j => (cost j : ℝ)) (Real.log r)).equivFun.symm (z u)
  let height : H →ₗ[ℝ] W := eW.toLinearMap.comp
    ((heightProjection T.character).comp H.subtype)
  have hbracket (x y : H) : height ⁅x, y⁆ = 0 := by
    change eW (heightProjection T.character ⁅(x : L), (y : L)⁆) = 0
    rw [T.height_lie, map_zero]
  have hh (r : ℝ) (hr : 1 ≤ r) (u : Z) :
      eW (heightProjection T.character (h r u : L)) =
        r • eW (heightProjection T.character (bD.equivFun.symm (z u) : L)) :=
    word_length_chart_height X S βD height hbracket (by linarith) (z u)
  have hlog (r : ℝ) (hr : 1 ≤ r) (u : Z) :
      ‖(Module.finBasis ℝ H).equivFun (h r u)‖ ≤ B * (1 + r) ^ p := by
    apply (norm_polynomial_chart_log_le bD (Module.finBasis ℝ H) cost p hp hr (z u)).trans
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (hz u) (Finset.sum_nonneg (fun _ _ => norm_nonneg _)))
      (by positivity)
  exact M.exists_uniform_adjoint_word_envelope T hunimod eW b₀ hE hne ht β γ hβ
    h (fun _ u => eW (heightProjection T.character (bD.equivFun.symm (z u) : L)))
    (fun _ _ u => hdomain u) hh hB p hlog v

end PolycyclicRecognition.CartanWordModel

end

end OAI
