import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanRootWidths
import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanGroupBoxes

namespace OAI

/-! # Generator steps lie in the actual enlarged Cartan boxes -/

noncomputable section
namespace PolycyclicRecognition.CartanWordModel

open Module LieAlgebra LieModule Set

variable {L W : Type*} [LieRing L] [LieAlgebra ℝ L] [FiniteDimensional ℝ L]
  {H : LieSubalgebra ℝ L} [H.IsCartanSubalgebra] (M : CartanWordModel H)
  {a : ℕ} (T : TriangularAdjoint L a)
  (hunimod : ∀ x : L, LinearMap.trace ℝ L (ad ℝ L x) = 0)
  [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
  (eW : HeightSpace T.character ≃ₗ[ℝ] W)

/-- A generator interval of its support width fits the word box. The only
constant is the generator's coordinate norm in the unscaled word basis. -/
theorem letter_step_mem_groupBox {N : Type*} (Exp : cartanRootIdeal H → N)
    {E : Set W} (hE : IsCompact E) (hne : E.Nonempty) (β : M.Bases)
    (i : Fin M.letterCount) {r R t : ℝ} (hr : 0 ≤ r)
    (ht : |t| ≤ R * Real.exp (r * (M.supportIn T hunimod eW).weightSupport E i)) :
    Exp (t • M.letter i) ∈ M.groupBox T hunimod eW Exp E β r
      (R * ‖(WordBasisSelections.basis M.letter M.wordList β).equivFun (M.letter i)‖) := by
  let s := Real.exp (r * (M.supportIn T hunimod eW).weightSupport E i)
  have hs : 0 < s := Real.exp_pos _
  have hc : |t / s| ≤ R := by
    rw [abs_div, abs_of_pos hs, div_le_iff₀ hs]
    exact ht
  have hv : t • M.letter i = (t / s) • (s • M.letter i) := by
    rw [smul_smul, div_mul_cancel₀ _ hs.ne']
  refine ⟨t • M.letter i, rfl, ?_⟩
  rw [hv, map_smul, norm_smul, Real.norm_eq_abs]
  exact (mul_le_mul_of_nonneg_left
    (M.norm_scaled_root_le T hunimod eW hE hne β i (M.letter i) (M.letter_root i) hr)
    (abs_nonneg _)).trans (mul_le_mul_of_nonneg_right hc (norm_nonneg _))

/-- One constant works for every generator and every selected word basis,
independently of the template and the physical scale. -/
theorem exists_uniform_letter_groupBox_bound {N : Type*} (Exp : cartanRootIdeal H → N) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (E : Set W), IsCompact E → E.Nonempty →
      ∀ (β : M.Bases) (i : Fin M.letterCount) (r R t : ℝ), 0 ≤ r → 0 ≤ R →
      |t| ≤ R * Real.exp (r * (M.supportIn T hunimod eW).weightSupport E i) →
      Exp (t • M.letter i) ∈ M.groupBox T hunimod eW Exp E β r (R * C) := by
  let C := ∑ β : M.Bases, ∑ i : Fin M.letterCount,
    ‖(WordBasisSelections.basis M.letter M.wordList β).equivFun (M.letter i)‖
  have hC : 0 ≤ C := Finset.sum_nonneg (fun _ _ => Finset.sum_nonneg (fun _ _ => norm_nonneg _))
  refine ⟨C, hC, ?_⟩
  intro E hE hne β i r R t hr hR ht
  have hc : ‖(WordBasisSelections.basis M.letter M.wordList β).equivFun (M.letter i)‖ ≤ C :=
    (Finset.single_le_sum
      (f := fun i => ‖(WordBasisSelections.basis M.letter M.wordList β).equivFun (M.letter i)‖)
      (fun _ _ => norm_nonneg _) (Finset.mem_univ i)).trans
      (Finset.single_le_sum
        (f := fun β : M.Bases => ∑ i : Fin M.letterCount,
          ‖(WordBasisSelections.basis M.letter M.wordList β).equivFun (M.letter i)‖)
        (fun _ _ => Finset.sum_nonneg (fun _ _ => norm_nonneg _)) (Finset.mem_univ β))
  obtain ⟨v, hv, hb⟩ := M.letter_step_mem_groupBox T hunimod eW Exp hE hne β i hr ht
  exact ⟨v, hv, hb.trans (mul_le_mul_of_nonneg_left hc hR)⟩

end PolycyclicRecognition.CartanWordModel

end

end OAI
