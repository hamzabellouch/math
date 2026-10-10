import Mathlib
import OAI.Geometry.PrescribedPotential.IntegerBounds

namespace OAI

/-! Sobolev Family Bounds. -/

noncomputable section
open Filter Topology _root_.MeasureTheory _root_.OAI.MeasureTheory TemperedDistribution LineDeriv
open scoped SchwartzMap ContDiff Classical Laplacian
namespace SobolevChart
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

def FamilyBound {α : Type*} (t : ℝ) (R : α → ℝ) (T : α → 𝓢(E,ℂ)) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ x, ‖schwartzCoord t (T x)‖ ≤ C * R x

lemma familyBound_raise_one {t : ℝ} {α : Type*} {R : α → ℝ} (T : α → 𝓢(E, ℂ))
    (hT : FamilyBound t R T)
    (hD : ∀ j, FamilyBound t R (fun f => ∂_{stdOrthonormalBasis ℝ E j} (T f))) :
    FamilyBound (t + 1) R T := by
  obtain ⟨C, hC, hc⟩ := hT
  choose D hD0 hdb using hD
  let c : ℝ := ‖(((2 * Real.pi)^2 : ℝ) : ℂ)⁻¹‖
  refine ⟨‖raiseZero (E := E) t‖ * C + c * ∑ j, ‖raiseDeriv t (stdOrthonormalBasis ℝ E j)‖ * D j,
    add_nonneg (mul_nonneg (norm_nonneg _) hC)
      (mul_nonneg (norm_nonneg _) (Finset.sum_nonneg (fun j _ => mul_nonneg (norm_nonneg _) (hD0 j)))), fun f => ?_⟩
  rw [schwartzCoord_raise_one]
  calc
    _ ≤ ‖raiseZero t (schwartzCoord t (T f))‖ +
        c * ‖∑ j, raiseDeriv t (stdOrthonormalBasis ℝ E j)
          (schwartzCoord t (∂_{stdOrthonormalBasis ℝ E j} (T f)))‖ := by
      simpa only [norm_smul] using norm_sub_le
        (raiseZero t (schwartzCoord t (T f)))
        ((((2 * Real.pi)^2 : ℝ) : ℂ)⁻¹ • ∑ j, raiseDeriv t (stdOrthonormalBasis ℝ E j)
          (schwartzCoord t (∂_{stdOrthonormalBasis ℝ E j} (T f))))
    _ ≤ (‖raiseZero (E := E) t‖ * C) * R f +
        c * ∑ j, (‖raiseDeriv t (stdOrthonormalBasis ℝ E j)‖ * D j) * R f := by
      apply add_le_add
      · exact ((raiseZero t).le_opNorm _).trans (by
          simpa only [mul_assoc] using
            (mul_le_mul_of_nonneg_left (hc f) (norm_nonneg (raiseZero (E := E) t))))
      · apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
        apply (norm_sum_le _ _).trans
        apply Finset.sum_le_sum
        intro j _
        exact ((raiseDeriv t (stdOrthonormalBasis ℝ E j)).le_opNorm _).trans (by
          simpa only [mul_assoc] using mul_le_mul_of_nonneg_left (hdb j f)
            (norm_nonneg (raiseDeriv t (stdOrthonormalBasis ℝ E j))))
    _ = _ := by rw [← Finset.sum_mul]; ring

lemma familyBound_of_words_integer (k : ℕ) {t : ℝ} {α : Type*} {R : α → ℝ} (T : α → 𝓢(E, ℂ))
    (h : ∀ ws : List E, ws.length ≤ k → FamilyBound t R (fun f => schwartzWord ws (T f))) :
    FamilyBound (t + k) R T := by
  induction k generalizing T with
  | zero => simpa [schwartzWord] using h [] (by simp)
  | succ k ih =>
    have ht := ih T (fun ws hw => h ws (by omega))
    have hd (j : Fin (Module.finrank ℝ E)) := ih
      (fun f => ∂_{stdOrthonormalBasis ℝ E j} (T f))
      (fun ws hw => by
        have hh := h (ws ++ [stdOrthonormalBasis ℝ E j])
          (by simp only [List.length_append, List.length_cons, List.length_nil]; omega)
        simpa only [schwartzWord_append, schwartzWord, ContinuousLinearMap.comp_apply,
          ContinuousLinearMap.id_apply, lineDerivOpCLM_apply] using hh)
    convert familyBound_raise_one T ht hd using 1
    push_cast
    ring

end SobolevChart

end

end OAI
