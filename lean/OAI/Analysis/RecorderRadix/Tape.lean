import Mathlib
import OAI.Analysis.RecorderRadix.Codes
import OAI.Computability.SolenoidalRecorder.Machines

namespace OAI

/-! Exact affine radix updates for two-sided tapes. -/

namespace Solenoidal
namespace Radix
noncomputable def update {m : ℕ} (a b l : Fin (m + 1)) : Move → (ℝ × ℝ) → ℝ × ℝ
  | .right => Prod.map (pushDigit b) (pop a)
  | .stay => Prod.map id (pushDigit b ∘ pop a)
  | .left => Prod.map (pop l) (pushDigit l ∘ pushDigit b ∘ pop a)

def source {m : ℕ} (a l : Fin (m + 1)) : Set (ℝ × ℝ) := first l ×ˢ first a

def target {m : ℕ} (b l : Fin (m + 1)) : Move → Set (ℝ × ℝ)
  | .right => two b l ×ˢ Set.Icc 0 1
  | .stay => first l ×ˢ first b
  | .left => Set.Icc 0 1 ×ˢ two l b

 
theorem full_image {m : ℕ} (a b l : Fin (m + 1)) (d : Move) :
    update a b l d '' source a l = target b l d := by
  cases d <;>
    simp only [update, target, source, Set.prodMap_image_prod, Set.image_comp,
      pop_image_first, prefix_image_unit, prefix_image_first, Set.image_id]

noncomputable def scale (m : ℕ) : Move → ℝ
  | .right => (base m)⁻¹
  | .stay => 1
  | .left => base m

 
theorem reciprocal_linear_part {m : ℕ} (a b l : Fin (m + 1)) (d : Move) (p q : ℝ × ℝ) :
    update a b l d p - update a b l d q =
      (scale m d * (p.1 - q.1), (scale m d)⁻¹ * (p.2 - q.2)) := by
  have hb : base m ≠ 0 := (base_pos m).ne'
  cases d <;> apply Prod.ext <;> dsimp [update, pushDigit, pop, scale] <;> field_simp <;> ring

 
def leftStack {m : ℕ} (t : ℤ → Fin (m + 1)) (k : ℤ) : ℕ → Fin (m + 1) :=
  fun j => t (k - ((j : ℤ) + 1))

 
def rightStack {m : ℕ} (t : ℤ → Fin (m + 1)) (k : ℤ) : ℕ → Fin (m + 1) :=
  fun j => t (k + (j : ℤ))

noncomputable def tapeCode {m : ℕ} (t : ℤ → Fin (m + 1)) (k : ℤ) : ℝ × ℝ :=
  (code (leftStack t k), code (rightStack t k))

theorem tapeCode_mem_source {m : ℕ} (t : ℤ → Fin (m + 1)) (k : ℤ) :
    tapeCode t k ∈ source (t k) (t (k - 1)) := by
  constructor
  · simpa [leftStack, tapeCode] using code_mem_first (leftStack t k)
  · simpa [rightStack, tapeCode] using code_mem_first (rightStack t k)

theorem stacks_right {m : ℕ} (t : ℤ → Fin (m + 1)) (k : ℤ) (b : Fin (m + 1)) :
    leftStack (Function.update t k b) (k + 1) = cons b (leftStack t k) ∧
    rightStack (Function.update t k b) (k + 1) = (fun j => rightStack t k (j + 1)) := by
  constructor
  · funext j
    cases j with
    | zero => simp [leftStack, cons]
    | succ j =>
      have hn : k - ((j : ℤ) + 1) ≠ k := by omega
      simp [leftStack, cons, hn]
  · funext j
    have he : k + 1 + (j : ℤ) = k + ↑(j + 1) := by omega
    have hn : k + (↑(j + 1) : ℤ) ≠ k := by omega
    simp only [rightStack, he, Function.update_of_ne hn]

theorem stacks_stay {m : ℕ} (t : ℤ → Fin (m + 1)) (k : ℤ) (b : Fin (m + 1)) :
    leftStack (Function.update t k b) k = leftStack t k ∧
    rightStack (Function.update t k b) k = cons b (fun j => rightStack t k (j + 1)) := by
  constructor
  · funext j
    have hn : k - ((j : ℤ) + 1) ≠ k := by omega
    simp only [leftStack, Function.update_of_ne hn]
  · funext j
    cases j with
    | zero => simp [rightStack, cons]
    | succ j =>
      have hn : k + (↑(j + 1) : ℤ) ≠ k := by omega
      simp only [rightStack, cons, Function.update_of_ne hn]

theorem stacks_left {m : ℕ} (t : ℤ → Fin (m + 1)) (k : ℤ) (b : Fin (m + 1)) :
    leftStack (Function.update t k b) (k - 1) = (fun j => leftStack t k (j + 1)) ∧
    rightStack (Function.update t k b) (k - 1) =
      cons (t (k - 1)) (cons b (fun j => rightStack t k (j + 1))) := by
  constructor
  · funext j
    have he : k - 1 - ((j : ℤ) + 1) = k - ((↑(j + 1) : ℤ) + 1) := by omega
    have hn : k - ((↑(j + 1) : ℤ) + 1) ≠ k := by omega
    simp only [leftStack, he, Function.update_of_ne hn]
  · funext j
    cases j with
    | zero =>
      have hn : k - 1 ≠ k := by omega
      simp [rightStack, cons, hn]
    | succ j =>
      cases j with
      | zero => simp [rightStack, cons]
      | succ j =>
        have he : k - 1 + (↑(j + 1 + 1) : ℤ) = k + ↑(j + 1) := by omega
        have hn : k + (↑(j + 1) : ℤ) ≠ k := by omega
        simp only [rightStack, cons, he, Function.update_of_ne hn]

 
theorem update_tapeCode {m : ℕ} (t : ℤ → Fin (m + 1)) (k : ℤ) (b : Fin (m + 1))
    (d : Move) :
    update (t k) b (t (k - 1)) d (tapeCode t k) =
      tapeCode (Function.update t k b) (k + d.displacement) := by
  have hL : pop (t (k - 1)) (code (leftStack t k)) = code (fun j => leftStack t k (j + 1)) := by
    simpa only [leftStack, Nat.cast_zero, zero_add] using pop_code (leftStack t k)
  have hR : pop (t k) (code (rightStack t k)) = code (fun j => rightStack t k (j + 1)) := by
    simpa only [rightStack, Nat.cast_zero, add_zero] using pop_code (rightStack t k)
  cases d with
  | right =>
    simp only [update, tapeCode, Move.displacement, (stacks_right t k b).1,
      (stacks_right t k b).2, code_cons, Prod.map, hR]
  | stay =>
    simp only [update, tapeCode, Move.displacement, add_zero, (stacks_stay t k b).1,
      (stacks_stay t k b).2, code_cons, Prod.map, Function.comp_apply, id_eq, hR]
  | left =>
    simp only [update, tapeCode, Move.displacement, ← sub_eq_add_neg, (stacks_left t k b).1,
      (stacks_left t k b).2, code_cons, Prod.map, Function.comp_apply, hR, hL]
end Radix
end Solenoidal

end OAI
