import OAI.MathematicalPhysics.RapidForcing.RawMachine

namespace OAI

section
open Encodable
namespace RapidForcing

private lemma flatMap_getElem_block {A B : Type} (l : List A) (f : A → List B)
    (s : ℕ) (hf : ∀ a ∈ l, (f a).length = s) (i j : ℕ) (hj : j < s) :
    (l.flatMap f)[i * s + j]? = l[i]?.bind (fun a => (f a)[j]?) := by
  induction l generalizing i with
  | nil => simp
  | cons a l ih =>
    have ha := hf a (by simp)
    have hl := fun b hb => hf b (List.mem_cons_of_mem a hb)
    cases i with
    | zero =>
      simp only [Nat.zero_mul, Nat.zero_add, List.flatMap_cons, List.getElem?_cons_zero,
        Option.bind_some]
      exact List.getElem?_append_left (by simpa only [ha] using hj)
    | succ i =>
      rw [List.flatMap_cons, List.getElem?_append_right (by rw [ha, Nat.succ_mul]; omega), ha]
      have he : (i + 1) * s + j - s = i * s + j := by rw [Nat.add_mul, Nat.one_mul]; omega
      simpa only [he, List.getElem?_cons_succ] using ih hl i

namespace Machine
lemma description_instruction (M : Machine) (q z : ℕ) :
    RawMachine.instruction M.description q z = M.instruction q z := by
  unfold RawMachine.instruction instruction
  by_cases hq : q < M.states
  · by_cases hz : z < M.symbols
    · simp only [description, hq, hz, and_self, ↓reduceIte, ↓reduceDIte]
      rw [flatMap_getElem_block _ _ M.symbols
        (fun a _ => by simp) q z hz]
      have hqs : (List.finRange M.states)[q]? = some ⟨q, hq⟩ := by
        rw [List.getElem?_eq_getElem (by simpa using hq)]
        simp
      have hzs : (List.finRange M.symbols)[z]? = some ⟨z, hz⟩ := by
        rw [List.getElem?_eq_getElem (by simpa using hz)]
        simp
      simp only [hqs, Option.bind_some, List.getElem?_map, hzs, Option.map_some]
      cases M.transition ⟨q, hq⟩ ⟨z, hz⟩ <;> rfl
    · simp [description, hq, hz]
  · simp [description, hq]

@[simp] lemma description_scaleData (M : Machine) (w : M.Input) :
    RawMachine.scaleData M.description (w.map Fin.val) = M.scaleData w := by
  simp [RawMachine.scaleData, description, scaleData]

@[simp] lemma description_terminalDigit (M : Machine) (d : ScaleData) (k : ℕ) :
    RawMachine.terminalDigit M.description d k = M.terminalDigit d k := rfl

@[simp] lemma description_nextDigit (M : Machine) (d : ScaleData) (n k : ℕ) :
    RawMachine.nextDigit M.description d n k = M.nextDigit d n k := by
  simp only [RawMachine.nextDigit, nextDigit, description_instruction]
  rfl

@[simp] lemma description_initialDigit (M : Machine) (w : M.Input) :
    RawMachine.initialDigit M.description (w.map Fin.val) = M.initialDigit w := by
  simp only [RawMachine.initialDigit, initialDigit, description_scaleData]
  rfl
end Machine
end RapidForcing

end

end OAI
