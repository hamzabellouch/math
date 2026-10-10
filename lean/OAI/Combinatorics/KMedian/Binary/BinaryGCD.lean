import Mathlib
import OAI.Combinatorics.KMedian.Binary.BinaryDivision

namespace OAI


                                 
section
namespace MetricKMedian.Binary
open Function Polynomial

namespace NatBinary
 theorem mod_length_lt {a b : ℕ} (hb : 0 < b) (hba : b ≤ a) : (a%b).bits.length < a.bits.length := by
  have ha : 0 < a := hb.trans_le hba
  by_cases hz : a%b=0
  · rw [hz,Nat.zero_bits,List.length_nil]
    apply List.length_pos_iff.mpr
    intro h
    have := (zero_iff a).mp h
    omega
  · have hr := Nat.mod_lt a hb
    have he := Nat.mod_add_div a b
    have hq : 1 ≤ a/b := (Nat.le_div_iff_mul_le hb).mpr (by simpa only [one_mul] using hba)
    have hm : b ≤ b*(a/b) := by nlinarith
    have hsmall : 2*(a%b) < a := by omega
    have hlen := length_mono hsmall.le
    have hbit : (2*(a%b)).bits.length=(a%b).bits.length+1 := by
      have hn : Nat.bit false (a%b) ≠ 0 := by
        simp only [Nat.bit_val,Bool.toNat_false,Nat.add_zero]
        omega
      simpa only [Nat.size_eq_bits_len,Nat.bit_val,Bool.toNat_false,Nat.add_zero,Nat.succ_eq_add_one]
        using Nat.size_bit hn
    omega
end NatBinary

namespace GCDLoop
abbrev S := ℕ × ℕ
abbrev enc : S → List Bool := encodePair Nat.bits Nat.bits
 def next (s : S) : S := (s.2,s.1%s.2)
 def body (s : S) : ℕ ⊕ S := if s.2=0 then .inl s.1 else .inr (next s)
 def result (s : S) : ℕ := s.1.gcd s.2
 def potential (s : S) : ℕ := s.1.bits.length+s.2.bits.length

 theorem enc_length (s : S) : (enc s).length=2*s.1.bits.length+1+s.2.bits.length := by
  exact encodePair_length _ _ _
 theorem length_le_potential (s : S) : (enc s).length ≤ 2*potential s+1 := by
  simp only [enc_length,potential]; omega
 theorem potential_le_length (s : S) : potential s ≤ (enc s).length := by
  simp only [enc_length,potential]; omega

 theorem next_result (s : S) : result (next s)=result s := by
  simp only [result,next]
  calc s.2.gcd (s.1%s.2)=(s.1%s.2).gcd s.2 := Nat.gcd_comm _ _
    _=s.2.gcd s.1 := (Nat.gcd_rec _ _).symm
    _=s.1.gcd s.2 := Nat.gcd_comm _ _

 theorem next_potential (s : S) : potential (next s) ≤ potential s := by
  have hm := NatBinary.length_mono (Nat.mod_le s.1 s.2)
  simp only [potential,next]
  omega

 theorem next_potential_lt (s : S) (ho : s.2 ≤ s.1) (hb : s.2 ≠ 0) : potential (next s) < potential s := by
  have h := NatBinary.mod_length_lt (Nat.pos_of_ne_zero hb) ho
  simp only [potential,next]
  omega

noncomputable def program : PolyProgram enc (encodeLoop enc Nat.bits) body := by
  let px := PolyProgram.fst Nat.bits Nat.bits
  let py := PolyProgram.snd Nat.bits Nat.bits
  let pn := py.fanout PolyProgram.natMod
  exact (PolyProgram.ite (py.comp PolyProgram.natZero)
    (pn.comp (PolyProgram.injectRight enc Nat.bits))
    (px.comp (PolyProgram.injectLeft enc Nat.bits))).congr _ (fun _ => by
      simp only [Function.comp_apply,body,next,decide_eq_true_eq])

 theorem run_ordered (L : ℕ) : ∀ (s : S) (S : ℕ), potential s=L →
    s.2 ≤ s.1 → 2*L+1 ≤ S → ∃ n ≤ L+1, BoundedRun enc body S n s (result s) := by
  induction L using Nat.strong_induction_on with
  | h L ih =>
      intro s S hL ho hs
      have hsize : (enc s).length ≤ S := (length_le_potential s).trans (by omega)
      by_cases hz : s.2=0
      · refine ⟨1,by omega,BoundedRun.stop hsize ?_⟩
        simp only [body,hz,ite_true,result,Nat.gcd_zero_right]
      · have hpot : potential (next s) < L := by simpa only [hL] using next_potential_lt s ho hz
        have horder : (next s).2 ≤ (next s).1 := (Nat.mod_lt s.1 (Nat.pos_of_ne_zero hz)).le
        obtain ⟨n,hn,hr⟩ := ih _ hpot (next s) S rfl horder (by omega)
        refine ⟨n+1,by omega,?_⟩
        rw [next_result] at hr
        exact BoundedRun.step hsize (by simp only [body,hz,ite_false]) hr

 theorem run (s : S) (S : ℕ) (hs : 2*potential s+1 ≤ S) :
    ∃ n ≤ potential s+2, BoundedRun enc body S n s (result s) := by
  by_cases ho : s.2 ≤ s.1
  · obtain ⟨n,hn,hr⟩ := run_ordered (potential s) s S rfl ho hs
    exact ⟨n,by omega,hr⟩
  · have hb : s.2 ≠ 0 := by omega
    have hn := next_potential s
    have horder : (next s).2 ≤ (next s).1 := (Nat.mod_lt s.1 (Nat.pos_of_ne_zero hb)).le
    obtain ⟨n,hbound,hr⟩ := run_ordered (potential (next s)) (next s) S rfl horder (by omega)
    refine ⟨n+1,by omega,?_⟩
    rw [next_result] at hr
    exact BoundedRun.step ((length_le_potential s).trans hs)
      (by simp only [body,hb,ite_false]) hr

noncomputable def loop : PolyProgram enc Nat.bits result :=
  program.loop result (X+2) (2*X+1) (fun s => by
    have hs := potential_le_length s
    obtain ⟨n,hn,hr⟩ := run s (2*(enc s).length+1) (by omega)
    refine ⟨n,?_,?_⟩
    · simp only [eval_add,eval_X,eval_ofNat]; omega
    · simpa only [eval_add,eval_mul,eval_ofNat,eval_one,eval_X] using hr)
end GCDLoop

namespace PolyProgram
noncomputable def natGcd : PolyProgram (encodePair Nat.bits Nat.bits) Nat.bits (fun x : ℕ × ℕ => x.1.gcd x.2) :=
  GCDLoop.loop
end PolyProgram
end MetricKMedian.Binary
end

end OAI
