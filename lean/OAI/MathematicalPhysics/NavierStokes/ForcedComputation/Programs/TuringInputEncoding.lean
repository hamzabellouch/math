import Mathlib.Computability.TuringMachine.ToPartrec
import Mathlib.Computability.Primrec.List

namespace OAI

/-! The input word of Mathlib's fixed interpreter is primitive recursive.
No computability claim about varying the machine table is needed. -/

namespace ForcedComputation.FiniteMachine

open Turing PartrecToTM2

private theorem trNat_pos (p : PosNum) : trNat (p : ℕ) = trPosNum p := by
  unfold trNat
  rw [PosNum.of_to_nat]
  rfl

theorem trNat_rec (n : ℕ) :
    trNat n = if n = 0 then [] else
      (if n % 2 = 0 then Γ'.bit0 else Γ'.bit1) :: trNat (n / 2) := by
  have h := Num.to_of_nat n
  generalize (n : Num) = m at h ⊢
  rw [← h]
  cases m with
  | zero => simp [trNat, trNum]
  | pos p =>
    change trNat (p : ℕ) = _
    rw [trNat_pos]
    cases p with
    | one => simp [trNat, trNum, trPosNum]
    | bit0 p =>
      have hp := PosNum.to_nat_pos p
      have hzero : (p : ℕ) + p ≠ 0 := by omega
      have hmod : ((p : ℕ) + p) % 2 = 0 := by omega
      have hdiv : ((p : ℕ) + p) / 2 = p := by omega
      simp only [trPosNum, Num.cast_pos, PosNum.cast_bit0, hzero, ↓reduceIte, hmod, hdiv,
        trNat_pos]
    | bit1 p =>
      have hzero : (p : ℕ) + p + 1 ≠ 0 := by omega
      have hmod : ((p : ℕ) + p + 1) % 2 ≠ 0 := by omega
      have hdiv : ((p : ℕ) + p + 1) / 2 = p := by omega
      simp only [trPosNum, Num.cast_pos, PosNum.cast_bit1, hzero, ↓reduceIte, hmod, hdiv,
        trNat_pos]

section
variable [Primcodable Γ']

private def nextBits (l : List (List Γ')) : Option (List Γ') :=
  if l.length = 0 then some [] else
    (l[l.length / 2]?).map fun bs =>
      (if l.length % 2 = 0 then Γ'.bit0 else Γ'.bit1) :: bs

private theorem nextBits_primrec : Primrec nextBits := by
  apply Primrec.ite (Primrec.eq.comp Primrec.list_length (Primrec.const 0))
    (Primrec.const (some []))
  apply Primrec.option_map
    (Primrec.list_getElem?.comp Primrec.id
      (Primrec.nat_div.comp Primrec.list_length (Primrec.const 2)))
  apply Primrec₂.uncurry.mp
  apply Primrec.list_cons.comp
    (Primrec.ite
      (Primrec.eq.comp
        (Primrec.nat_mod.comp (Primrec.list_length.comp Primrec.fst) (Primrec.const 2))
        (Primrec.const 0))
      (Primrec.const Γ'.bit0) (Primrec.const Γ'.bit1)) Primrec.snd

theorem trNat_primrec : Primrec trNat := by
  have h : Primrec₂ (fun (_ : Unit) n => trNat n) :=
    Primrec.nat_strong_rec (fun (_ : Unit) n => trNat n)
      (nextBits_primrec.comp Primrec.snd).to₂ (by
        intro _ n
        rw [nextBits, List.length_map, List.length_range]
        by_cases hn : n = 0
        · subst n
          simp [trNat_zero]
        · have hlt : n / 2 < n := Nat.div_lt_self (Nat.pos_of_ne_zero hn) (by decide)
          simp only [hn, ↓reduceIte, List.getElem?_map,
            List.getElem?_range hlt, Option.map_some]
          rw [trNat_rec n, ite_eq_right hn])
  exact h.comp (Primrec.const ()) Primrec.id

theorem trList_primrec : Primrec trList := by
  have h : Primrec fun l : List ℕ => l.flatMap (fun n => trNat n ++ [Γ'.cons]) :=
    Primrec.list_flatMap Primrec.id
      (Primrec.list_append.comp (trNat_primrec.comp Primrec.snd)
        (Primrec.const [Γ'.cons])).to₂
  exact h.of_eq (by intro l; induction l <;> simp_all [trList])

end

theorem trInit_primrec {K : Type*} [DecidableEq K]
    {Γ : K → Type*} (k : K) [Finite (Γ k)]
    [Primcodable (Γ k)] [Primcodable (TM2to1.Γ' K Γ)]
    [Finite (TM2to1.Γ' K Γ)] :
    Primrec (TM2to1.trInit (Γ := Γ) k) := by
  let f : Γ k → TM2to1.Γ' K Γ :=
    fun a => (false, Function.update (fun _ => none) k (some a))
  have hL : Primrec (fun L : List (Γ k) => L.reverse.map f) :=
    Primrec.list_map Primrec.list_reverse
      ((Primrec.dom_finite f).comp Primrec.snd).to₂
  exact (Primrec.list_cons.comp
    ((Primrec.dom_finite (fun a : TM2to1.Γ' K Γ =>
      (show TM2to1.Γ' K Γ from (true, a.2)))).comp
      (Primrec.list_headI.comp hL))
    (Primrec.list_tail.comp hL))

end ForcedComputation.FiniteMachine

end OAI
