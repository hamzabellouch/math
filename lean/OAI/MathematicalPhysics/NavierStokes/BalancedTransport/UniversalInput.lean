import OAI.MathematicalPhysics.NavierStokes.BalancedTransport.FiniteSimulator

namespace OAI

noncomputable section
namespace BalancedTransport.Universal
open Turing PartrecToTM2
open scoped Classical

instance : Fintype K' := ⟨{.main,.rev,.aux,.stack}, by intro k; cases k <;> simp⟩

instance : Primcodable Γ' := Primcodable.ofEquiv (Fin (Fintype.card Γ')) (Fintype.equivFin Γ')

lemma trNat_rec (n : ℕ) : trNat n =
    if n = 0 then [] else (if n % 2 = 0 then Γ'.bit0 else Γ'.bit1) :: trNat (n / 2) := by
  have h (p : Num) : trNat (p : ℕ) =
      if (p : ℕ) = 0 then [] else
        (if (p : ℕ) % 2 = 0 then Γ'.bit0 else Γ'.bit1) :: trNat ((p : ℕ) / 2) := by
    cases p with
    | zero => simp [trNat,trNum]
    | pos p =>
      have hp := PosNum.to_nat_pos p
      cases p with
      | one => norm_num [trNat,trNum,trPosNum]
      | bit0 p =>
        have hp := PosNum.to_nat_pos p
        have he : ((Num.pos (PosNum.bit0 p) : Num) : ℕ) = (p : ℕ) + (p : ℕ) := rfl
        rw [he]
        have hdiv : ((p : ℕ) + (p : ℕ)) / 2 = (p : ℕ) := by omega
        have hmod : ((p : ℕ) + (p : ℕ)) % 2 = 0 := by omega
        rw [ite_eq_right (by omega),ite_eq_left hmod,hdiv]
        change trNum (((Num.pos (PosNum.bit0 p) : Num) : ℕ) : Num) =
          Γ'.bit0 :: trNum (((Num.pos p : Num) : ℕ) : Num)
        rw [Num.of_to_nat, Num.of_to_nat]
        rfl
      | bit1 p =>
        have hp := PosNum.to_nat_pos p
        have he : ((Num.pos (PosNum.bit1 p) : Num) : ℕ) = (p : ℕ) + (p : ℕ) + 1 := rfl
        rw [he]
        have hdiv : ((p : ℕ) + (p : ℕ) + 1) / 2 = (p : ℕ) := by omega
        have hmod : ((p : ℕ) + (p : ℕ) + 1) % 2 ≠ 0 := by omega
        rw [ite_eq_right (by omega),ite_eq_right hmod,hdiv]
        change trNum (((Num.pos (PosNum.bit1 p) : Num) : ℕ) : Num) =
          Γ'.bit1 :: trNum (((Num.pos p : Num) : ℕ) : Num)
        rw [Num.of_to_nat, Num.of_to_nat]
        rfl
  simpa using h (n : Num)

lemma computable_trNat : Computable trNat := by
  let g : Unit → List (List Γ') → Option (List Γ') := fun _ l =>
    some (if l.length = 0 then [] else
      (if l.length % 2 = 0 then Γ'.bit0 else Γ'.bit1) :: (l.getD (l.length / 2) []))
  have hg : Primrec₂ g := by
    change Primrec (fun z : Unit × List (List Γ') => g z.1 z.2)
    dsimp only [g]
    apply Primrec.option_some.comp
    apply Primrec.ite (Primrec.eq.comp (Primrec.list_length.comp Primrec.snd) (Primrec.const 0))
      (Primrec.const [])
    apply Primrec.list_cons.comp
    · exact Primrec.ite (Primrec.eq.comp
        (Primrec.nat_mod.comp (Primrec.list_length.comp Primrec.snd) (Primrec.const 2))
        (Primrec.const 0)) (Primrec.const Γ'.bit0) (Primrec.const Γ'.bit1)
    · exact (Primrec.list_getD ([] : List Γ')).comp Primrec.snd
        (Primrec.nat_div.comp (Primrec.list_length.comp Primrec.snd) (Primrec.const 2))
  have hh := Primrec.nat_strong_rec (fun (_ : Unit) => trNat) hg (by
    intro u n
    dsimp [g]
    simp only [List.length_map,List.length_range]
    by_cases hn : n = 0
    · subst n; simp
    · rw [ite_eq_right hn, List.getD_eq_getElem?_getD,
        List.getElem?_map, List.getElem?_range (by omega : n / 2 < n)]
      simp only [Option.map_some,Option.getD_some]
      rw [trNat_rec n,ite_eq_right hn])
  exact hh.to_comp.comp (Computable.const ()) Computable.id

abbrev StackAlphabet := TM2to1.Γ' K' (fun _ => Γ')

instance : Primcodable (Bool × (K' → Option Γ')) :=
  Primcodable.ofEquiv (Fin (Fintype.card StackAlphabet)) (Fintype.equivFin StackAlphabet)

instance : Primcodable StackAlphabet :=
  (inferInstance : Primcodable (Bool × (K' → Option Γ')))

lemma computable_trInit : Computable (TM2to1.trInit (Γ := fun _ : K' => Γ') K'.main) := by
  have hm : Computable (fun L : List Γ' => L.reverse.map
      (fun a => ((false, Function.update (fun _ : K' => (none : Option Γ')) K'.main (some a)) : StackAlphabet))) :=
    (Primrec.list_map Primrec.list_reverse ((Primrec.dom_finite
      (fun a : Γ' => ((false, Function.update (fun _ : K' => (none : Option Γ')) K'.main (some a)) : StackAlphabet))).comp Primrec.snd).to₂).to_comp
  exact Primrec.list_cons.to_comp.comp
    ((Primrec.dom_finite (fun a : StackAlphabet => ((true,a.2) : StackAlphabet))).to_comp.comp
      (Primrec.list_headI.to_comp.comp hm))
    (Primrec.list_tail.to_comp.comp hm)

lemma computable_translatedInput : Computable (fun n : ℕ =>
    (TM2to1.trInit (Γ := fun _ : K' => Γ') K'.main (trList [n])).map finiteIndex) := by
  have ht : Computable (fun n : ℕ => trList [n]) :=
    Primrec.list_append.to_comp.comp computable_trNat (Computable.const [Γ'.cons])
  exact (Primrec.list_map Primrec.id ((Primrec.dom_finite finiteIndex).comp Primrec.snd).to₂).to_comp.comp
    (computable_trInit.comp ht)

end BalancedTransport.Universal
end

end OAI
