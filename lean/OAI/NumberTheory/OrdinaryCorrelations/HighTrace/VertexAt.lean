import OAI.NumberTheory.OrdinaryCorrelations.HighTrace.DivisorFamily

namespace OAI

noncomputable section
open scoped BigOperators
open Finset
open Finset Classical
open Filter
open Finset Classical Filter
open scoped Topology

namespace OrdinaryCorrelations.GraphKernel.PrimeSystem.Specification
open OrdinaryCorrelations.SignedTrace
open Finset Classical
variable {S : PrimeSystem} {B τ C₀ : ℝ} {D : S.DivisorFamily B τ C₀} {h L : ℕ}

def vertexAt (s : S.Specification D h L) (n : ℕ) : ℤ :=
  if hn : n  ≤  s.length then s.offset ⟨n,by omega⟩ else 0

def edgeAt (s : S.Specification D h L) (n : ℕ) : ℤ :=
  if hn : n<s.length then s.sign ⟨n,hn⟩*(h:ℤ)*s.label ⟨n,hn⟩ else 0

def coefficientAt (s : S.Specification D h L) (q n : ℕ) : ℤ :=
  if hn : n<s.length then
    if q ∣ s.label ⟨n,hn⟩ then s.sign ⟨n,hn⟩*(h:ℤ)*(s.label ⟨n,hn⟩/q : ℕ) else 0
  else 0

def coefficient (s : S.Specification D h L) (q a b : ℕ) : ℤ :=
  ∑ n ∈ Ico a b, s.coefficientAt q n

lemma edgeAt_eq (s : S.Specification D h L) (n : ℕ) (hn : n<s.length) :
    s.edgeAt n = s.vertexAt (n+1)-s.vertexAt n := by
  simp only [edgeAt,vertexAt,dite_eq_left hn,dite_eq_left (show n+1  ≤  s.length by omega),
    dite_eq_left (show n  ≤  s.length by omega)]
  exact (s.step ⟨n,hn⟩).symm

lemma displacement_eq_sum (s : S.Specification D h L) (a b : ℕ)
    (hab : a ≤ b) (hb : b  ≤  s.length) :
    s.offset ⟨b,by omega⟩-s.offset ⟨a,by omega⟩ = ∑ n ∈ Ico a b, s.edgeAt n := by
  calc
    _ = s.vertexAt b-s.vertexAt a := by
      simp only [vertexAt,dite_eq_left hb,dite_eq_left (hab.trans hb)]
    _ = ∑ n ∈ Ico a b, (s.vertexAt (n+1)-s.vertexAt n) := (sum_Ico_sub _ hab).symm
    _ = _ := sum_congr rfl (fun n hn => (s.edgeAt_eq n (by have := mem_Ico.mp hn; omega)).symm)

lemma mul_coefficient_interval (s : S.Specification D h L) (q a b : ℕ)
    (hab : a ≤ b) (hb : b  ≤  s.length)
    (hq : ∀ n : Fin s.length, a ≤ n.val → n.val<b → q ∣ s.label n) :
    (q:ℤ)*s.coefficient q a b = s.offset ⟨b,by omega⟩-s.offset ⟨a,by omega⟩ := by
  rw [s.displacement_eq_sum a b hab hb,coefficient,mul_sum]
  apply sum_congr rfl
  intro n hn
  have hi := mem_Ico.mp hn
  have hn' : n<s.length := by omega
  have hqn := hq ⟨n,hn'⟩ hi.1 hi.2
  simp only [coefficientAt,edgeAt,dite_eq_left hn',ite_eq_left hqn]
  have he : (q:ℤ)*(s.label ⟨n,hn'⟩/q : ℕ) = (s.label ⟨n,hn'⟩:ℤ) := by
    exact_mod_cast Nat.mul_div_cancel' hqn
  calc
    _ = s.sign ⟨n,hn'⟩*(h:ℤ)*((q:ℤ)*(s.label ⟨n,hn'⟩/q : ℕ)) := by ring
    _ = _ := by rw [he]

lemma coefficient_restrict (s : S.Specification D h L) (q a b c d : ℕ)
    (hca : c ≤ a) (hbd : b ≤ d) (hd : d  ≤  s.length)
    (hzero : ∀ i : Fin s.length, c ≤ i.val → i.val<d →
      (i.val<a ∨ b ≤ i.val) → ¬q ∣ s.label i) :
    s.coefficient q c d = s.coefficient q a b := by
  unfold coefficient
  symm
  apply sum_subset
  · intro n hn
    have hi := mem_Ico.mp hn
    exact mem_Ico.mpr ⟨hca.trans hi.1,lt_of_lt_of_le hi.2 hbd⟩
  · intro n hn hout
    have hi := mem_Ico.mp hn
    have hn' : n<s.length := by omega
    have hsplit : n<a ∨ b ≤ n := by
      by_contra he
      push Not at he
      exact hout (mem_Ico.mpr ⟨by omega,by omega⟩)
    have hq := hzero ⟨n,hn'⟩ hi.1 hi.2 hsplit
    simp only [coefficientAt,dite_eq_left hn',ite_eq_right hq]

end OrdinaryCorrelations.GraphKernel.PrimeSystem.Specification

end

end OAI
