import OAI.NumberTheory.OrdinaryCorrelations.HighTrace.VertexAt

namespace OAI

noncomputable section
open scoped BigOperators
open Finset
open Finset Classical
open Filter
open Finset Classical Filter
open scoped Topology

namespace OrdinaryCorrelations.GraphKernel.PrimeSystem.Specification
open OrdinaryCorrelations.SignedTrace Finset Classical
variable {S : PrimeSystem} {B τ C₀ : ℝ} {D : S.DivisorFamily B τ C₀} {h L : ℕ}

lemma coefficient_eq_single (s : S.Specification D h L) (q : S.Index) (i : Fin s.length)
    (hq : ∀ j, (q:ℕ) ∣ s.label j ↔ j=i) :
    s.coefficient (q:ℕ) 0 s.length = s.sign i*h*(s.label i/(q:ℕ):ℕ) := by
  unfold coefficient
  rw [sum_eq_single i.val]
  · simp [coefficientAt,i.isLt,(hq i).mpr rfl]
  · intro n hn hni
    have hn' : n<s.length := (mem_Ico.mp hn).2
    have hd : ¬(q:ℕ) ∣ s.label ⟨n,hn'⟩ := by
      intro hd
      have he := congrArg Fin.val ((hq ⟨n,hn'⟩).mp hd)
      exact hni he
    simp [coefficientAt,hn',hd]
  · intro hi
    exact (hi (mem_Ico.mpr ⟨Nat.zero_le _,i.isLt⟩)).elim

lemma singleton_coefficient_not_dvd (s : S.Specification D h L) (q : S.Index)
    (i : Fin s.length) (hq : ∀ j, (q:ℕ) ∣ s.label j ↔ j=i)
    (hh : ¬(s.extra:ℕ) ∣ h) :
    ¬((s.extra:ℕ):ℤ) ∣ s.coefficient (q:ℕ) 0 s.length := by
  let p : ℕ := s.extra
  have : Fact (Nat.Prime p) := ⟨S.prime_mem s.extra s.extra.property⟩
  have hquot : ¬p ∣ s.label i/(q:ℕ) := by
    intro hd
    exact s.extra_not_div i (hd.trans (Nat.div_dvd_of_dvd ((hq i).mpr rfl)))
  have hh' : (h:ZMod p)≠0 := by
    intro he
    exact hh ((ZMod.natCast_eq_zero_iff h p).mp he)
  have hquot' : ((s.label i/(q:ℕ):ℕ):ZMod p)≠0 := by
    intro he
    exact hquot ((ZMod.natCast_eq_zero_iff _ p).mp he)
  have hs : (s.sign i:ZMod p)≠0 := by
    rcases s.sign_mem i with he | he <;> simp [he]
  rw [coefficient_eq_single s q i hq]
  intro hd
  have hz := (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mpr hd
  simp only [Int.cast_mul,Int.cast_natCast] at hz
  exact (mul_ne_zero (mul_ne_zero hs hh') hquot') hz

end OrdinaryCorrelations.GraphKernel.PrimeSystem.Specification

end

end OAI
