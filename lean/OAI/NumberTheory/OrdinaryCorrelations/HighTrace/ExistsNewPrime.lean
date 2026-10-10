import OAI.NumberTheory.OrdinaryCorrelations.HighTrace.DivisorFamily
import OAI.NumberTheory.OrdinaryCorrelations.HighTrace.LastEdge

namespace OAI

noncomputable section
open scoped BigOperators
open Finset
open Finset Classical
open Filter
open Finset Classical Filter
open scoped Topology

namespace OrdinaryCorrelations.GraphKernel.PrimeSystem
open OrdinaryCorrelations.SignedTrace
open Finset Classical
variable {S : PrimeSystem} {B τ C₀ : ℝ} {D : S.DivisorFamily B τ C₀} {h L : ℕ}

lemma DivisorFamily.exists_new_prime (D : S.DivisorFamily B τ C₀) (hτ : τ<2)
    {e f : ℕ} (he : e ∈ D.members) (hf : f ∈ D.members) (hne : e≠f) :
    ∃ q : S.Index, (q:ℕ) ∣ e ∧ ¬(q:ℕ) ∣ f := by
  by_contra hn
  have hp (p : ℕ) (hp : p ∈ e.primeFactors) : p ∣ f := by
    by_contra hpf
    exact hn ⟨⟨p,D.support e he hp⟩,(Nat.mem_primeFactors.mp hp).2.1,hpf⟩
  have hdiv : e ∣ f := by
    have hInt : (e:ℤ) ∣ (f:ℤ) := (squarefree_int_dvd_iff e (D.squarefree e he) f).mpr
      (fun p hpe => by exact_mod_cast hp p hpe)
    exact_mod_cast hInt
  obtain ⟨k,hk⟩ := hdiv
  have hep := D.greater_one e he
  have hfp := D.greater_one f hf
  have hk2 : 2 ≤ k := by
    by_contra hnot
    have hk01 : k=0 ∨ k=1 := by omega
    rcases hk01 with hr|hr
    · simp [hr] at hk
      omega
    · simp [hr] at hk
      exact hne hk.symm
  have htwo : (2:ℝ)*e ≤ f := by
    have hnat : 2*e ≤ f := by rw [hk]; nlinarith
    exact_mod_cast hnat
  have hlo := D.lower e he
  have hup := D.upper f hf
  have hH := D.H_lower
  nlinarith

namespace Specification

lemma tail_prime_confined (s : S.Specification D h L) (hs : s.Primitive)
    (hb : 0<s.tailStart.val) (q : S.Index) (hqt : (q:ℕ) ∣ s.label s.tailStart)
    (hprev : ¬(q:ℕ) ∣ s.label ⟨s.tailStart.val-1,by omega⟩) :
    ∀ i : Fin s.length, i<s.tailStart → ¬(q:ℕ) ∣ s.label i := by
  intro i hi hqi
  apply hprev
  apply s.prime_occurrence_interval hs q i ⟨s.tailStart.val-1,by omega⟩ s.tailStart
  · change i.val ≤ s.tailStart.val-1
    change i.val<s.tailStart.val at hi
    omega
  · change s.tailStart.val-1 ≤ s.tailStart.val
    omega
  · exact hqi
  · exact hqt

theorem exists_tail_prime (s : S.Specification D h L) (hs : s.Primitive)
    (hh : 0<h) (hτ : τ<2) (hpp : h<(s.extra:ℕ)) (hpL : L<(s.extra:ℕ)) :
    ∃ q : S.Index, (q:ℕ) ∣ s.label s.tailStart ∧
      ∀ i : Fin s.length, i<s.tailStart → ¬(q:ℕ) ∣ s.label i := by
  have hb := s.tailStart_pos hh hpp hpL
  obtain ⟨q,hqt,hqp⟩ := D.exists_new_prime hτ (s.label_mem s.tailStart)
    (s.label_mem ⟨s.tailStart.val-1,by omega⟩) (s.before_tail_ne hb).symm
  exact ⟨q,hqt,s.tail_prime_confined hs hb q hqt hqp⟩

lemma tail_coefficient (s : S.Specification D h L) (q c : ℕ) (_ : c ≤ s.length)
    (hq : q ∣ s.label s.tailStart)
    (hfree : ∀ i : Fin s.length, i<s.tailStart → ¬q ∣ s.label i) :
    s.coefficient q c s.length = (s.length-max c s.tailStart.val:ℕ)*
      (s.sign s.tailStart*(h:ℤ)*(s.label s.tailStart/q:ℕ)) := by
  rw [s.coefficient_restrict q (max c s.tailStart.val) s.length c s.length
    (le_max_left _ _) le_rfl le_rfl (by
      intro i hci hil hi
      apply hfree i
      change i.val<s.tailStart.val
      rcases hi with hi|hi <;> omega)]
  unfold coefficient
  calc
    _ = ∑ n ∈ Ico (max c s.tailStart.val) s.length,
        s.sign s.tailStart*(h:ℤ)*(s.label s.tailStart/q:ℕ) := by
      apply sum_congr rfl
      intro n hn
      have hi := mem_Ico.mp hn
      have htail : s.tailStart ≤ (⟨n,hi.2⟩ : Fin s.length) := by
        change s.tailStart.val ≤ n
        exact (le_max_right _ _).trans hi.1
      simp only [coefficientAt,dite_eq_left hi.2,s.tail_labels _ htail,s.tail_signs _ htail,
        ite_eq_left hq]
    _ = _ := by simp only [sum_const,Nat.card_Ico,nsmul_eq_mul]

theorem suffix_coefficient_nondvd (s : S.Specification D h L) (hh : 0<h)
    (hpp : h<(s.extra:ℕ)) (hpL : L<(s.extra:ℕ)) (q : S.Index)
    (hq : (q:ℕ) ∣ s.label s.tailStart)
    (hfree : ∀ i : Fin s.length, i<s.tailStart → ¬(q:ℕ) ∣ s.label i) :
    ¬((s.extra:ℕ):ℤ) ∣ s.coefficient q s.suffix.val s.length := by
  rw [s.tail_coefficient q s.suffix.val s.suffix.isLt.le hq hfree]
  have hk : 0<s.length-max s.suffix.val s.tailStart.val :=
    Nat.sub_pos_of_lt (max_lt s.suffix.isLt s.tailStart.isLt)
  apply not_dvd_signed_product (S.prime_mem _ s.extra.property) (s.sign_mem s.tailStart)
  · exact Nat.not_dvd_of_pos_of_lt hk (lt_of_le_of_lt
      ((Nat.sub_le _ _).trans s.length_le) hpL)
  · exact Nat.not_dvd_of_pos_of_lt hh hpp
  · exact fun hp => s.extra_not_div s.tailStart (dvd_trans hp (Nat.div_dvd_of_dvd hq))

end Specification
end OrdinaryCorrelations.GraphKernel.PrimeSystem

end

end OAI
