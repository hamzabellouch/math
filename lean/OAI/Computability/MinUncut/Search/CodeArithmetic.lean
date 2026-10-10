import Mathlib
import OAI.Computability.MinUncut.Estimates.CodeComputability

namespace OAI

section
namespace MinUncut.Costed
open Turing.ToPartrec

def addCode : Code := .prec .head (.comp .succ .tail)
def subCode : Code := .prec .head (.comp .pred .tail)

lemma run_add (n a : ℕ) (v : List ℕ) :
    Runs addCode (n::a::v) [a+n] (100000*(magnitude (n::a::v)+2)^2) := by
  let M := magnitude (n::a::v)
  have hn : n≤M := by dsimp [M]; omega
  have ha : a≤M := by dsimp [M]; omega
  have hv : magnitude (a::v)≤M := by dsimp [M]; omega
  have hr : ∀i≤n,a+i≤M := by intro i hi; dsimp [M]; omega
  have hg : ∀i<n, Runs (.comp .succ .tail) (i::(a+i)::a::v) [a+(i+1)] (200*(M+1)) := by
    intro i hi
    have hh := run_comp (run_tail (i::(a+i)::a::v)) (run_succ ((a+i)::a::v))
    have hri := hr i (by omega)
    apply hh.mono
    simp only [magnitude_cons] at *
    omega
  have hh := run_prec .head (.comp .succ .tail) n (fun i=>a+i) (a::v) M
    (300*(M+1)) (200*(M+1)) hn hr hv ((run_head (a::v)).mono (by gcongr)) hg
  apply hh.mono
  dsimp [M] at *
  nlinarith

lemma run_sub (n a : ℕ) (v : List ℕ) :
    Runs subCode (n::a::v) [a-n] (100000*(magnitude (n::a::v)+2)^2) := by
  let M := magnitude (n::a::v)
  have hn : n≤M := by dsimp [M]; omega
  have ha : a≤M := by dsimp [M]; omega
  have hv : magnitude (a::v)≤M := by dsimp [M]; omega
  have hr : ∀i≤n,a-i≤M := by intro i _; omega
  have hg : ∀i<n, Runs (.comp .pred .tail) (i::(a-i)::a::v) [a-(i+1)] (1000*(M+1)) := by
    intro i hi
    have hh := run_comp (run_tail (i::(a-i)::a::v)) (run_pred ((a-i)::a::v))
    have he : a-i-1=a-(i+1) := by omega
    simp only [List.headI_cons,he] at hh
    apply hh.mono
    simp only [magnitude_cons] at *
    omega
  have hh := run_prec .head (.comp .pred .tail) n (fun i=>a-i) (a::v) M
    (300*(M+1)) (1000*(M+1)) hn hr hv ((run_head (a::v)).mono (by gcongr)) hg
  apply hh.mono
  dsimp [M] at *
  nlinarith

def mulCode : Code := .prec .zero (.comp addCode .tail)

lemma run_mul (n a : ℕ) (v : List ℕ) :
    Runs mulCode (n::a::v) [a*n] (10000000*(magnitude (n::a::v)+2)^6) := by
  let S := magnitude (n::a::v)
  let M := (S+2)^2
  have hnS : n≤S := by dsimp [S]; omega
  have haS : a≤S := by dsimp [S]; omega
  have hvS : magnitude (a::v)≤S := by dsimp [S]; omega
  have hSM : S≤M := by dsimp [M]; nlinarith
  have hr : ∀i≤n,a*i≤M := by
    intro i hi
    have hh : a*i≤S*S := Nat.mul_le_mul haS (hi.trans hnS)
    dsimp [M]; nlinarith
  have hg : ∀i<n,Runs (.comp addCode .tail) (i::(a*i)::a::v) [a*(i+1)]
      (1000000*(M+2)^2) := by
    intro i hi
    have hh := run_comp (run_tail (i::(a*i)::a::v)) (run_add (a*i) a v)
    have he : a+a*i=a*(i+1) := by ring
    rw [he] at hh
    apply hh.mono
    have hri := hr i (by omega)
    simp only [magnitude_cons] at *
    have hinput : a*i+1+(a+1+magnitude v)≤M+1+S := by omega
    have hiM : i≤M := (Nat.le_of_lt hi).trans (hnS.trans hSM)
    calc
      _ ≤ 32*(M+1+(2*M+1)+1)+100000*(2*M+3)^2+1 := by
        have ht : i+1+(a*i+1+(a+1+magnitude v))+1 ≤
            M+1+(2*M+1)+1 := by omega
        have hc : a*i+1+(a+1+magnitude v)+2 ≤ 2*M+3 := by omega
        exact Nat.add_le_add_right (Nat.add_le_add (Nat.mul_le_mul_left 32 ht)
          (Nat.mul_le_mul_left 100000 (Nat.pow_le_pow_left hc 2))) 1
      _ ≤ _ := by ring_nf; omega
  have hh := run_prec .zero (.comp addCode .tail) n (fun i=>a*i) (a::v) M
    (210*(M+1)) (1000000*(M+2)^2) (hnS.trans hSM) hr (hvS.trans hSM)
    ((run_const_zero (a::v)).mono (by gcongr; exact hvS.trans hSM)) hg
  apply hh.mono
  change 210*(M+1)+(n+2)*(1000000*(M+2)^2+50000*(M+1))≤10000000*(S+2)^6
  calc
    _ ≤ 210*(M+1)+(S+2)*(1000000*(M+2)^2+50000*(M+1)) := by gcongr
    _ ≤ _ := by dsimp [M]; ring_nf; omega

end MinUncut.Costed

end

end OAI
