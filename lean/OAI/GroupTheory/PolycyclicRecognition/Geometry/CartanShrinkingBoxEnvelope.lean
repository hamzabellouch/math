import OAI.GroupTheory.PolycyclicRecognition.Analysis.TemplateBoxEnvelopes
import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanBoxScaling

namespace OAI

/-! # Absorbing vanishing homothetic enlargements into the box radius -/

noncomputable section
namespace PolycyclicRecognition.CartanWordModel

open Module LieAlgebra LieModule Set Filter
open scoped Topology

variable {L W : Type*} [LieRing L] [LieAlgebra ℝ L] [FiniteDimensional ℝ L]
  {H : LieSubalgebra ℝ L} [H.IsCartanSubalgebra] (M : CartanWordModel H)
  {a : ℕ} (T : TriangularAdjoint L a)
  (hunimod : ∀ x : L, LinearMap.trace ℝ L (ad ℝ L x) = 0)
  [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
  (eW : HeightSpace T.character ≃ₗ[ℝ] W)

/-- The diagonal's shrinking enlargement changes only a subexponential
radius in one fixed maximizing box. The enlarged basis may vary with scale. -/
theorem exists_homothetic_box_envelope_sequence {N : Type*}
    (Exp : cartanRootIdeal H → N)
    (b₀ : Basis (Fin (finrank ℝ (cartanRootIdeal H))) ℝ (cartanRootIdeal H))
    {E : Set W} (hE : IsCompact E) (hne : E.Nonempty)
    (β : M.Bases)
    (hβ : IsMaximizingColumnBasis (wordListCoordinates M.letter M.wordList b₀)
      (M.boxCost T hunimod eW E) β.val)
    (scale δ R : ℕ → ℝ) (hscale : Tendsto scale atTop atTop)
    (hscale0 : ∀ n, 0 ≤ scale n) (hδ0 : ∀ n, 0 ≤ δ n) (hδ : Tendsto δ atTop (𝓝 0))
    (hR0 : ∀ n, 0 ≤ R n) (hR : HasSubexponentialUpperBoundSeq scale R) :
    ∃ V : ℕ → ℝ, (∀ n, 0 ≤ V n) ∧ HasSubexponentialUpperBoundSeq scale V ∧
      ∀ n (γ : M.Bases),
        M.groupBox T hunimod eW Exp ((fun w => (1 + δ n) • w) '' E) γ (scale n) (R n) ⊆
          M.groupBox T hunimod eW Exp E β (scale n) (V n) := by
  let C := ∑ w : M.wordList, |M.boxCost T hunimod eW E w|
  have hC w : M.boxCost T hunimod eW E w ≤ C :=
    (le_abs_self _).trans (Finset.single_le_sum (f := fun w : M.wordList => |M.boxCost T hunimod eW E w|) (fun _ _ => abs_nonneg _)
      (Finset.mem_univ w))
  have heps : Tendsto (fun n => δ n * C) atTop (𝓝 0) := by
    simpa only [zero_mul] using hδ.mul_const C
  obtain ⟨V, hV0, hV, hv⟩ := exists_sequence_word_box_envelope M.letter M.wordList b₀
    (M.boxCost T hunimod eW E) β hβ scale (fun n => δ n * C) R hscale hscale0 heps hR0 hR
  refine ⟨V, hV0, hV, ?_⟩
  intro n γ x hx
  obtain ⟨v, he, hb⟩ := hx
  refine ⟨v, he, hv n _ γ ?_ v hb⟩
  intro w
  rw [M.boxCost_image_smul T hunimod eW hE hne (by linarith [hδ0 n])]
  nlinarith [mul_le_mul_of_nonneg_left (hC w) (hδ0 n)]

end PolycyclicRecognition.CartanWordModel

end

end OAI
