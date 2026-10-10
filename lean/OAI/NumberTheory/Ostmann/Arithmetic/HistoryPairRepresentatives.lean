import OAI.NumberTheory.Ostmann.Arithmetic.HistoryPairRows
import OAI.NumberTheory.Ostmann.Arithmetic.PrimeLineFamiliesRepeated

namespace OAI

noncomputable section
namespace Ostmann.Arithmetic.HistoryPairRepresentatives
open scoped BigOperators
open Construction HistoryOccurrenceVariables HistoryPairRows
variable {l : ℕ} {V : ℕ → ℕ} {outside : List ℕ}

theorem internalSlot_prime (h : History l) (hs : h.Supported V outside) (i : InternalKey h) :
    (internalSlot h i).value.Prime := by
  induction h with
  | leaf a => exact isEmptyElim i
  | @node l a p u hp hm left right ihl ihr =>
      rcases i with i | i
      · have hl := History.supported_left hs
        have hprime : left.root.PrimeSmall := by
          rw [History.Supported.eq_def] at hl
          exact hl.2.1
        exact hprime (u.get i) ((History.supported_child_small hs).1.mem_iff.mpr
          (List.mem_append_left hp (List.get_mem u i)))
      · rcases i with i | i
        · exact ihl (History.supported_left hs) i
        · exact ihr (History.supported_right hs) i

theorem slot_prime (h k : History l) (hs : h.Supported V outside) (ks : k.Supported V outside)
    (i : Occurrences h k) : (slot h k i).value.Prime := by
  rcases i with i | i
  · exact internalSlot_prime h hs i
  · exact internalSlot_prime k ks i

def key (h k : History l) (i : Occurrences h k) : ℕ × ℕ := (level h k i,(slot h k i).value)

def Representative (h k : History l) := {r : ℕ × ℕ // r ∈ Finset.univ.image (key h k)}

instance (h k : History l) : Fintype (Representative h k) :=
  inferInstanceAs (Fintype {r // r ∈ Finset.univ.image (key h k)})

instance (h k : History l) : DecidableEq (Representative h k) :=
  inferInstanceAs (DecidableEq {r : ℕ × ℕ // r ∈ Finset.univ.image (key h k)})

def label (h k : History l) (i : Occurrences h k) : Representative h k :=
  ⟨key h k i,Finset.mem_image.mpr ⟨i,Finset.mem_univ i,rfl⟩⟩

def prime (h k : History l) (r : Representative h k) : ℕ := r.val.2

def Fiber (h k : History l) (r : Representative h k) := {i : Occurrences h k // label h k i=r}

instance fiberFintype (h k : History l) (r : Representative h k) : Fintype (Fiber h k r) := by
  classical
  exact inferInstanceAs (Fintype {i : Occurrences h k // label h k i=r})

theorem label_surjective (h k : History l) : Function.Surjective (label h k) := by
  intro r
  obtain ⟨i,_,hi⟩ := Finset.mem_image.mp r.property
  exact ⟨i,Subtype.ext hi⟩

@[simp] theorem label_eq_iff (h k : History l) (i j : Occurrences h k) :
    label h k i=label h k j ↔ level h k i=level h k j ∧ (slot h k i).value=(slot h k j).value := by
  constructor
  · intro he
    have he' : key h k i=key h k j := congrArg (fun r : Representative h k => r.val) he
    exact Prod.mk.inj he'
  · rintro ⟨hl,hv⟩
    exact Subtype.ext (Prod.ext hl hv)

@[simp] theorem prime_label (h k : History l) (i : Occurrences h k) :
    prime h k (label h k i)=(slot h k i).value := rfl

theorem representative_prime (h k : History l) (hs : h.Supported V outside) (ks : k.Supported V outside)
    (r : Representative h k) : (prime h k r).Prime := by
  obtain ⟨i,rfl⟩ := label_surjective h k r
  exact slot_prime h k hs ks i

theorem fiber_nonempty (h k : History l) (r : Representative h k) : Nonempty (Fiber h k r) := by
  obtain ⟨i,hi⟩ := label_surjective h k r
  exact ⟨i,hi⟩

theorem product_occurrences (h k : History l) {M : Type*} [CommMonoid M] (f : SmallSlot → M) :
    (∏ i : Occurrences h k, f (slot h k i)) =
      (h.internalOccurrences.map f).prod*(k.internalOccurrences.map f).prod := by
  simp only [Occurrences,Fintype.prod_sum_type,slot,Sum.elim_inl,Sum.elim_inr,prod_internalSlot]

theorem product_by_multiplicity (h k : History l) :
    (∏ i : Occurrences h k, ((slot h k i).value:ℝ)) =
      ∏ r : Representative h k, (prime h k r:ℝ)^
        RepeatedLabels.multiplicity Finset.univ (label h k) r := by
  classical
  exact RepeatedLabels.product_by_multiplicity Finset.univ (label h k) (fun r => (prime h k r:ℝ))

end Ostmann.Arithmetic.HistoryPairRepresentatives

end

end OAI
