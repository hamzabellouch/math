import OAI.NumberTheory.OrdinaryCorrelations.HighTrace.ListSupport
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
variable {S : PrimeSystem} {B τ C₀ : ℝ} {D : S.DivisorFamily B τ C₀} {h L ℓ : ℕ}

namespace Specification
lemma support_iff_extra_or_label (s : S.Specification D h L) (p : S.Index) :
    (p:ℕ) ∈ s.primeSupport ↔ p=s.extra ∨ ∃ i : Fin s.length, (p:ℕ) ∣ s.label i := by
  simp only [primeSupport,mem_insert,mem_biUnion,mem_univ,true_and]
  constructor
  · rintro (he|⟨i,hi⟩)
    · exact Or.inl (Subtype.ext he)
    · exact Or.inr ⟨i,(Nat.mem_primeFactors.mp hi).2.1⟩
  · rintro (rfl|⟨i,hi⟩)
    · exact Or.inl rfl
    · exact Or.inr ⟨i,Nat.mem_primeFactors.mpr
        ⟨S.prime_mem p p.property,hi,(D.squarefree _ (s.label_mem i)).ne_zero⟩⟩

noncomputable def activity (s : S.Specification D h L) (p : S.Index)
    (hp : (p:ℕ) ∈ s.primeSupport) : Fin (s.length+1) :=
  if he : p=s.extra then 0 else
    (Classical.choose ((s.support_iff_extra_or_label p).mp hp |>.resolve_left he)).castSucc

lemma activity_divides (s : S.Specification D h L) (p : S.Index)
    (hp : (p:ℕ) ∈ s.primeSupport) (x : ℤ) (hx : s.QualifiesAt x) :
    ((p:ℕ):ℤ) ∣ x+s.offset (s.activity p hp) := by
  unfold activity
  split_ifs with he
  · subst p
    simpa only [s.offset_zero,add_zero] using hx.1
  · exact dvd_trans (by exact_mod_cast (Classical.choose_spec
      (((s.support_iff_extra_or_label p).mp hp).resolve_left he)))
      (hx.2 (Classical.choose (((s.support_iff_extra_or_label p).mp hp).resolve_left he)))

lemma tail_support (s : S.Specification D h L) (r : S.Index)
    (hr : (r:ℕ) ∣ s.label s.tailStart) : (r:ℕ) ∈ s.primeSupport :=
  (s.support_iff_extra_or_label r).mpr (Or.inr ⟨s.tailStart,hr⟩)

lemma occurs_before_or_tail (s : S.Specification D h L) (q : S.Index)
    (hq : (q:ℕ) ∈ s.primeSupport) :
    q=s.extra ∨ (∃ i : Fin s.length, i < s.tailStart ∧ (q:ℕ) ∣ s.label i) ∨
      ((q:ℕ) ∣ s.label s.tailStart ∧
      ∀ i : Fin s.length, i < s.tailStart → ¬(q:ℕ) ∣ s.label i) := by
  rcases (s.support_iff_extra_or_label q).mp hq with he|⟨i,hi⟩
  · exact Or.inl he
  · by_cases hpre : ∃ i : Fin s.length, i < s.tailStart ∧ (q:ℕ) ∣ s.label i
    · exact Or.inr (Or.inl hpre)
    · right; right
      have hat : s.tailStart ≤ i := by
        by_contra hn
        exact hpre ⟨i,lt_of_not_ge hn,hi⟩
      constructor
      · rwa [s.tail_labels i hat] at hi
      · intro j hj hd
        exact hpre ⟨j,hj,hd⟩
end Specification

lemma free_prime_one_side (w : ClosedLine h ℓ) (p : S.Index) (hp : ¬S.IsFixed w p)
    (k : Fin (ℓ+1)) :
    (∀ i : Fin ℓ, i.val < k.val → ¬(p:ℕ) ∣ w.label i) ∨
    (∀ i : Fin ℓ, k.val ≤ i.val → ¬(p:ℕ) ∣ w.label i) := by
  by_cases ha : ∀ i : Fin ℓ, i.val < k.val → ¬(p:ℕ) ∣ w.label i
  · exact Or.inl ha
  · right
    push Not at ha
    obtain ⟨e,hek,he⟩ := ha
    intro i hki hi
    have hei := (unique_occurrence_of_free w p hp e he i).mp hi
    subst i
    omega

lemma attached_activity_comparison (w : ClosedLine h ℓ)
    (a b : AttachedSpec w D L) (r : S.Index)
    (hr : (r:ℕ) ∈ a.spec.primeSupport)
    (hrt : (r:ℕ) ∣ b.spec.label b.spec.tailStart)
    (x : ℤ) (ha : a.spec.QualifiesAt (x+a.vertex))
    (hb : b.spec.QualifiesAt (x+b.vertex)) :
    ((r:ℕ):ℤ) ∣ b.vertex-a.vertex+b.spec.offset b.spec.tailStart.castSucc-
      a.spec.offset (a.spec.activity r hr) := by
  have hi := a.spec.activity_divides r hr (x+a.vertex) ha
  have hj : ((r:ℕ):ℤ) ∣ x+b.vertex+b.spec.offset b.spec.tailStart.castSucc :=
    dvd_trans (by exact_mod_cast hrt) (hb.2 b.spec.tailStart)
  have he : b.vertex-a.vertex+b.spec.offset b.spec.tailStart.castSucc-
      a.spec.offset (a.spec.activity r hr) =
      (x+b.vertex+b.spec.offset b.spec.tailStart.castSucc)-
      (x+a.vertex+a.spec.offset (a.spec.activity r hr)) := by ring
  rw [he]
  exact dvd_sub hj hi

end OrdinaryCorrelations.GraphKernel.PrimeSystem

end

end OAI
