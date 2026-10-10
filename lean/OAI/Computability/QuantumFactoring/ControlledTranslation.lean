import Mathlib
import OAI.Computability.QuantumFactoring.BitArithmeticDivision

namespace OAI

section
open scoped BigOperators


namespace ExactQuantumFactoring
open BooleanNetwork

namespace ControlledTranslation

def dataPart {p b : ℕ} (x : Basis (p+b)) : Basis p := fun i => x (i.castAdd b)
def phasePart {p b : ℕ} (x : Basis (p+b)) : Basis b := fun i => x (Fin.natAdd p i)

def addInput {p b : ℕ} (δ : BooleanNetwork p b) : BooleanNetwork (p+b) (b+b) :=
  (select (Fin.natAdd p)).pair ((select (fun i => i.castAdd b)).comp δ)

def forward {p b : ℕ} (δ : BooleanNetwork p b) : BooleanNetwork (p+b) (p+b) :=
  (select (fun i => i.castAdd b)).pair ((addInput δ).comp (BitArithmetic.add b))

def backward {p b : ℕ} (δ : BooleanNetwork p b) : BooleanNetwork (p+b) (p+b) :=
  (select (fun i => i.castAdd b)).pair ((addInput δ).comp (BitArithmetic.sub b))

def translate {p b : ℕ} (δ : Basis p → BitVec b) (x : Basis (p+b)) : Basis (p+b) :=
  Fin.append (dataPart x) (fun i => (bitsValue (phasePart x) + δ (dataPart x)).getLsbD i.val)

def untranslate {p b : ℕ} (δ : Basis p → BitVec b) (x : Basis (p+b)) : Basis (p+b) :=
  Fin.append (dataPart x) (fun i => (bitsValue (phasePart x) - δ (dataPart x)).getLsbD i.val)

lemma input_words {p b : ℕ} (δ : BooleanNetwork p b) (x : Basis (p+b)) :
    BitArithmetic.leftWord ((addInput δ).eval x) = bitsValue (phasePart x) ∧
      BitArithmetic.rightWord ((addInput δ).eval x) = bitsValue (δ.eval (dataPart x)) := by
  simp only [addInput, eval_pair, eval_comp, eval_select, BitArithmetic.leftWord,
    BitArithmetic.rightWord, Function.comp_apply, Fin.append_left, Fin.append_right]
  exact ⟨rfl,rfl⟩

lemma forward_correct {p b : ℕ} (δ : BooleanNetwork p b) (x : Basis (p+b)) :
    (forward δ).eval x = translate (fun d => bitsValue (δ.eval d)) x := by
  rw [forward, eval_pair, eval_comp]
  unfold translate
  congr 1
  funext i
  rw [BitArithmetic.add_correct, (input_words δ x).1, (input_words δ x).2]

lemma backward_correct {p b : ℕ} (δ : BooleanNetwork p b) (x : Basis (p+b)) :
    (backward δ).eval x = untranslate (fun d => bitsValue (δ.eval d)) x := by
  rw [backward, eval_pair, eval_comp]
  unfold untranslate
  congr 1
  funext i
  rw [BitArithmetic.sub_correct, (input_words δ x).1, (input_words δ x).2]

@[simp] lemma dataPart_append {p b : ℕ} (d : Basis p) (z : Basis b) :
    dataPart (Fin.append d z) = d := by funext i; simp [dataPart]
@[simp] lemma phasePart_append {p b : ℕ} (d : Basis p) (z : Basis b) :
    phasePart (Fin.append d z) = z := by funext i; simp [phasePart]

lemma untranslate_translate {p b : ℕ} (δ : Basis p → BitVec b) (x : Basis (p+b)) :
    untranslate δ (translate δ x) = x := by
  simp only [untranslate, translate, dataPart_append, phasePart_append, bitsValue_bits,
    BitVec.add_sub_cancel, bitsValue_bit]
  exact Fin.append_castAdd_natAdd

lemma translate_untranslate {p b : ℕ} (δ : Basis p → BitVec b) (x : Basis (p+b)) :
    translate δ (untranslate δ x) = x := by
  simp only [untranslate, translate, dataPart_append, phasePart_append, bitsValue_bits,
    BitVec.sub_add_cancel, bitsValue_bit]
  exact Fin.append_castAdd_natAdd

lemma forward_backward {p b : ℕ} (δ : BooleanNetwork p b) (x : Basis (p+b)) :
    (backward δ).eval ((forward δ).eval x) = x := by
  rw [backward_correct, forward_correct, untranslate_translate]

lemma forward_count {p b : ℕ} (δ : BooleanNetwork p b) :
    (forward δ).net.count ≤ δ.net.count+86*b+6 := by
  simp only [forward, addInput, count_pair, count_comp, count_select, Nat.zero_add]
  have := BitArithmetic.add_count b
  omega

lemma backward_count {p b : ℕ} (δ : BooleanNetwork p b) :
    (backward δ).net.count ≤ δ.net.count+158*b+6 := by
  simp only [backward, addInput, count_pair, count_comp, count_select, Nat.zero_add]
  have := BitArithmetic.sub_count b
  omega

end ControlledTranslation
end ExactQuantumFactoring


end

end OAI
