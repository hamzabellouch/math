import Mathlib
import OAI.Combinatorics.UniformKServer.RawBinary

namespace OAI

noncomputable section
                              
section

namespace UniformKServer.RawBits
open Primrec

 theorem size_graph (a b : ℕ) : a.size=b ↔ a<2^b ∧ (b=0 ∨ 2^(b-1)≤a) := by
  constructor
  · rintro rfl
    refine ⟨Nat.lt_size_self a,?_⟩
    by_cases h : a.size=0
    · exact Or.inl h
    · exact Or.inr (Nat.lt_size.mp (by omega))
  · rintro ⟨h,he|he⟩
    · have:=Nat.size_le.mpr h;omega
    · have:=Nat.size_le.mpr h
      have:=Nat.lt_size.mpr he
      omega

 theorem primitive_size : Primrec Nat.size := by
  apply Primrec.of_graph ⟨id,Primrec.id,fun a=>Nat.size_le.mpr Nat.lt_two_pow_self⟩
  refine ⟨inferInstance,?_⟩
  have h : Primrec (fun p : ℕ×ℕ=>decide (p.1<2^p.2) &&
      (decide (p.2=0) || decide (2^(p.2-1)≤p.1))) := by fun_prop
  exact h.of_eq (by
    intro p
    change _=decide (p.1.size=p.2)
    apply Bool.eq_iff_iff.mpr
    simp only [Bool.and_eq_true,Bool.or_eq_true,decide_eq_true_eq,size_graph])

 theorem primitive_testBit : Primrec₂ Nat.testBit := by
  have h : Primrec (fun p : ℕ×ℕ=>decide (p.1/2^p.2%2=1)) :=
    (Primrec.eq.comp (Primrec.nat_mod.comp (by fun_prop) (Primrec.const 2)) (Primrec.const 1)).decide
  exact h.of_eq (by intro p;exact Nat.testBit_eq_decide_div_mod_eq.symm)

 theorem bits_eq (a : ℕ) : a.bits=(List.range a.size).map (Nat.testBit a) := by
  apply List.ext_getElem
  · simp [Nat.size_eq_bits_len]
  · intro i h₁ h₂
    simp only [List.getElem_map,List.getElem_range,Nat.testBit_eq_inth]
    exact (List.getI_eq_getElem _ h₁).symm

 theorem primitive_bits : Primrec Nat.bits := by
  have h : Primrec (fun a=>(List.range a.size).map (Nat.testBit a)) :=
    Primrec.list_map (Primrec.list_range.comp primitive_size) primitive_testBit
  exact h.of_eq (fun a=>(bits_eq a).symm)

 theorem bits_value (w : List Bool) : (RawBinary.value (w++[true])).bits=w++[true] := by
  induction w with
  | nil=>simp
  | cons b w ih=>
    simp only [List.cons_append,RawBinary.value_cons]
    rw [Nat.bits_append_bit _ _ (fun h=>by
      have hh:=congrArg Nat.bits h
      rw [ih] at hh
      simp at hh),ih]

 theorem value_positive (w : List Bool) : 0<RawBinary.value (w++[true]) := by
  have h:=bits_value w
  by_contra hn
  have hz : RawBinary.value (w++[true])=0 := by omega
  rw [hz] at h
  simp at h

open Turing.PartrecToTM2

def letter (b : Bool) : Γ' := bif b then .bit1 else .bit0

theorem trPos_bits (a : PosNum) : trPosNum a=((a:ℕ).bits.map letter) := by
  induction a with
  | one=>rfl
  | bit0 a ih=>
    rw [PosNum.cast_bit0,←two_mul,Nat.bit0_bits _ (ne_of_gt (PosNum.to_nat_pos a))]
    simp only [trPosNum,List.map_cons,←ih]
    rfl
  | bit1 a ih=>
    rw [PosNum.cast_bit1,←two_mul,Nat.bit1_bits]
    simp only [trPosNum,List.map_cons,←ih]
    rfl

theorem trNum_bits (a : Num) : trNum a=((a:ℕ).bits.map letter) := by
  cases a with
  | zero=>rfl
  | pos a=>exact trPos_bits a

theorem trNat_bits (a : ℕ) : trNat a=a.bits.map letter := by
  unfold trNat
  rw [trNum_bits,Num.to_of_nat]

end UniformKServer.RawBits

end


end

end OAI
