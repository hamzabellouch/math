import OAI.NumberTheory.OrdinaryCorrelations.HighTrace.VertexAt
import OAI.NumberTheory.OrdinaryCorrelations.HighTrace.PrimeOccurrenceInterval

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

def lastEdge (s : S.Specification D h L) : Fin s.length := ⟨s.length-1,by have := s.length_pos; omega⟩

noncomputable def tailCandidates (s : S.Specification D h L) : Finset (Fin s.length) :=
  univ.filter (fun i => ∀ j, i ≤ j → s.label j=s.label s.lastEdge)

lemma tailCandidates_nonempty (s : S.Specification D h L) : s.tailCandidates.Nonempty := by
  refine ⟨s.lastEdge,mem_filter.mpr ⟨mem_univ _,?_⟩⟩
  intro j hj
  have he : j=s.lastEdge := by
    apply Fin.ext
    change j.val=s.length-1
    change s.length-1 ≤ j.val at hj
    omega
  exact congrArg s.label he

noncomputable def tailStart (s : S.Specification D h L) : Fin s.length :=
  s.tailCandidates.min' s.tailCandidates_nonempty

lemma tail_labels (s : S.Specification D h L) (i : Fin s.length) (hi : s.tailStart ≤ i) :
    s.label i=s.label s.tailStart := by
  have hm := (mem_filter.mp (min'_mem s.tailCandidates s.tailCandidates_nonempty)).2
  exact (hm i hi).trans (hm s.tailStart le_rfl).symm

lemma before_tail_ne (s : S.Specification D h L) (hb : 0<s.tailStart.val) :
    s.label ⟨s.tailStart.val-1,by omega⟩ ≠ s.label s.tailStart := by
  intro he
  let b : Fin s.length := ⟨s.tailStart.val-1,by omega⟩
  have hm : b ∈ s.tailCandidates := by
    refine mem_filter.mpr ⟨mem_univ _,?_⟩
    intro j hj
    have hlast : s.label s.tailStart=s.label s.lastEdge :=
      (mem_filter.mp (min'_mem s.tailCandidates s.tailCandidates_nonempty)).2 _ le_rfl
    rcases eq_or_lt_of_le hj with heq|hlt
    · rw [← heq]
      exact he.trans hlast
    · exact (s.tail_labels j (by change s.tailStart.val ≤ j.val; change s.tailStart.val-1<j.val at hlt; omega)).trans hlast
  have hle := min'_le s.tailCandidates b hm
  change s.tailStart.val ≤ b.val at hle
  dsimp [b] at hle
  omega

lemma tail_signs (s : S.Specification D h L) (i : Fin s.length) (hi : s.tailStart ≤ i) :
    s.sign i=s.sign s.tailStart := by
  have aux : ∀ n : ℕ, ∀ hn : n<s.length, s.tailStart.val ≤ n →
      s.sign ⟨n,hn⟩=s.sign s.tailStart := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro hn hbn
      by_cases he : n=s.tailStart.val
      · have hf : (⟨n,hn⟩ : Fin s.length)=s.tailStart := Fin.ext he
        exact congrArg s.sign hf
      · have hb : s.tailStart.val<n := by omega
        let j : Fin s.length := ⟨n-1,by omega⟩
        have hj : s.tailStart ≤ j := by change s.tailStart.val ≤ n-1; omega
        have hn' : s.tailStart ≤ (⟨n,hn⟩ : Fin s.length) := hbn
        have hstep := s.sign_eq_of_adjacent_label j ⟨n,hn⟩
          (by dsimp [j]; omega) ((s.tail_labels j hj).trans (s.tail_labels _ hn').symm)
        exact hstep.symm.trans (ih (n-1) (by omega) (by omega) (by omega))
  exact aux i.val i.isLt hi

lemma tail_displacement (s : S.Specification D h L) (a b : ℕ)
    (ha : s.tailStart.val ≤ a) (hab : a ≤ b) (hb : b ≤ s.length) :
    s.offset ⟨b,by omega⟩-s.offset ⟨a,by omega⟩ =
      (b-a:ℕ)*(s.sign s.tailStart*(h:ℤ)*s.label s.tailStart) := by
  rw [s.displacement_eq_sum a b hab hb]
  calc
    _ = ∑ n ∈ Ico a b, s.sign s.tailStart*(h:ℤ)*s.label s.tailStart := by
      apply sum_congr rfl
      intro n hn
      have hn' := mem_Ico.mp hn
      have hlen : n<s.length := by omega
      have htail : s.tailStart ≤ (⟨n,hlen⟩ : Fin s.length) := by change s.tailStart.val ≤ n; omega
      simp only [edgeAt,dite_eq_left hlen,s.tail_labels _ htail,s.tail_signs _ htail]
    _ = _ := by simp only [sum_const,Nat.card_Ico,nsmul_eq_mul]

lemma not_dvd_signed_product {p k u e : ℕ} (hp : Nat.Prime p) {z : ℤ}
    (hz : z=-1 ∨ z=1) (hk : ¬p ∣ k) (hu : ¬p ∣ u) (he : ¬p ∣ e) :
    ¬(p:ℤ) ∣ (k:ℤ)*(z*(u:ℤ)*e) := by
  intro hd
  have hd' : (p:ℤ) ∣ ((k*u*e:ℕ):ℤ) := by
    rcases hz with hz|hz
    · have heq : (k:ℤ)*(z*(u:ℤ)*e) = -((k*u*e:ℕ):ℤ) := by simp [hz]; ring
      rw [heq] at hd
      exact dvd_neg.mp hd
    · convert hd using 1
      simp [hz]
      ring
  have hn : p ∣ k*u*e := by exact_mod_cast hd'
  rcases hp.dvd_mul.mp hn with hku|hep
  · exact (hp.dvd_mul.mp hku).elim hk hu
  · exact he hep

theorem tailStart_pos (s : S.Specification D h L) (hh : 0<h)
    (hpp : h<(s.extra:ℕ)) (hpL : L<(s.extra:ℕ)) : 0<s.tailStart.val := by
  by_contra hn
  have hb : s.tailStart.val=0 := by omega
  let k := s.length-s.suffix.val
  have hk : 0<k := by dsimp [k]; exact Nat.sub_pos_of_lt s.suffix.isLt
  have hkle : k ≤ L := (Nat.sub_le _ _).trans s.length_le
  have he := s.tail_displacement s.suffix.val s.length (by rw [hb]; omega) s.suffix.isLt.le le_rfl
  have hd : ((s.extra:ℕ):ℤ) ∣ (k:ℤ)*(s.sign s.tailStart*(h:ℤ)*s.label s.tailStart) := by
    rw [← he]
    exact s.extra_div_suffix
  exact not_dvd_signed_product (S.prime_mem _ s.extra.property) (s.sign_mem s.tailStart)
    (Nat.not_dvd_of_pos_of_lt hk (lt_of_le_of_lt hkle hpL))
    (Nat.not_dvd_of_pos_of_lt hh hpp) (s.extra_not_div s.tailStart) hd

end OrdinaryCorrelations.GraphKernel.PrimeSystem.Specification

end

end OAI
