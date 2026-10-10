import OAI.NumberTheory.OrdinaryCorrelations.HighTrace.Cylinder

namespace OAI

noncomputable section
open scoped BigOperators
open Finset
open Finset Classical
open Filter
open Finset Classical Filter
open scoped Topology

namespace OrdinaryCorrelations.SourceCylinder
variable {ι : Type*} [Fintype ι] {Ω : ι → Type*}

local instance memSupportDecidableEq : DecidableEq ι := Classical.decEq _

namespace Cylinder

@[simp] lemma mem_support (c : Cylinder Ω) (p : ι) :
    p ∈ c.support ↔ ∃ a, c.value p = some a := by
  classical
  simp only [support, Finset.mem_filter, Finset.mem_univ, true_and]
  cases c.value p <;> simp

@[simp] lemma support_bot : (⊥ : Cylinder Ω).support = ∅ := by
  classical
  ext p
  simp only [mem_support, Finset.notMem_empty, iff_false]
  rintro ⟨a,h⟩
  cases h

lemma support_mono {c d : Cylinder Ω} (h : c ≤ d) : c.support ⊆ d.support := by
  intro p hp
  obtain ⟨a, ha⟩ := (mem_support c p).mp hp
  exact (mem_support d p).mpr ⟨a, h p a ha⟩

lemma le_of_support_subset {c d e : Cylinder Ω} (hc : c ≤ e) (hd : d ≤ e)
    (hs : c.support ⊆ d.support) : c ≤ d := by
  intro p a hpa
  obtain ⟨b, hpb⟩ := (mem_support d p).mp (hs ((mem_support c p).mpr ⟨a,hpa⟩))
  have hab : a = b := Option.some.inj ((hc p a hpa).symm.trans (hd p b hpb))
  simpa [hab] using hpb

lemma eq_of_support_eq {c d e : Cylinder Ω} (hc : c ≤ e) (hd : d ≤ e)
    (hs : c.support = d.support) : c = d :=
  le_antisymm (le_of_support_subset hc hd hs.subset)
    (le_of_support_subset hd hc hs.symm.subset)

lemma eq_bot_iff (c : Cylinder Ω) : c = ⊥ ↔ c.support = ∅ := by
  constructor
  · rintro rfl; exact support_bot
  · intro h
    apply le_antisymm _ bot_le
    intro p a hp
    have := (mem_support c p).mpr ⟨a,hp⟩
    simp [h] at this

lemma support_ssubset {c d : Cylinder Ω} (h : c < d) : c.support ⊂ d.support := by
  refine Finset.ssubset_iff_subset_ne.mpr ⟨support_mono h.le, ?_⟩
  intro heq
  exact h.ne (eq_of_support_eq h.le le_rfl heq)

omit [Fintype ι] in
lemma holds_mono {c d : Cylinder Ω} (hcd : c ≤ d) {x : ∀ p, Ω p}
    (hd : d.Holds x) : c.Holds x := fun p a hp => hd p a (hcd p a hp)

omit [Fintype ι] in
@[simp] lemma holds_bot (x : ∀ p, Ω p) : (⊥ : Cylinder Ω).Holds x := by
  intro p a hp
  cases hp

lemma generates_support {A : Finset (Cylinder Ω)} {c : Cylinder Ω}
    (h : Generates A c) : c.support = A.biUnion support := by
  classical
  ext p
  simp only [Finset.mem_biUnion]
  exact ⟨fun hp => h.2 p hp, fun ⟨e, he, hp⟩ => support_mono (h.1 e he) hp⟩

lemma generates_le {A : Finset (Cylinder Ω)} {c d : Cylinder Ω}
    (hc : Generates A c) (hd : ∀e ∈ A, e ≤ d) : c ≤ d := by
  intro p a hp
  obtain ⟨e, he, hpe⟩ := hc.2 p ((mem_support c p).mpr ⟨a,hp⟩)
  obtain ⟨b, hb⟩ := (mem_support e p).mp hpe
  have hab : a = b := Option.some.inj (hp.symm.trans (hc.1 e he p b hb))
  simpa [hab] using hd e he p b hb

lemma generates_unique {A : Finset (Cylinder Ω)} {c d : Cylinder Ω}
    (hc : Generates A c) (hd : Generates A d) : c = d :=
  le_antisymm (generates_le hc hd.1) (generates_le hd hc.1)

lemma generates_holds {A : Finset (Cylinder Ω)} {c : Cylinder Ω}
    (h : Generates A c) {x : ∀ p, Ω p} : c.Holds x ↔ ∀e ∈ A, e.Holds x := by
  constructor
  · intro hx e he; exact holds_mono (h.1 e he) hx
  · intro hx p a hp
    obtain ⟨e, he, hpe⟩ := h.2 p ((mem_support c p).mpr ⟨a,hp⟩)
    obtain ⟨b,hb⟩ := (mem_support e p).mp hpe
    have hab : a = b := Option.some.inj (hp.symm.trans (h.1 e he p b hb))
    simpa [hab] using hx e he p b hb

variable [∀ p, Fintype (Ω p)]

lemma rank_mono (E : Finset (Cylinder Ω)) : Monotone (rank E) := by
  classical
  intro c d hcd
  apply Finset.sup_le
  intro A hA
  obtain ⟨hAE, hle, hpriv⟩ := Finset.mem_filter.mp hA
  apply Finset.le_sup
  exact Finset.mem_filter.mpr ⟨hAE, fun e he => (hle e he).trans hcd, hpriv⟩

lemma card_le_rank {A E : Finset (Cylinder Ω)} {c : Cylinder Ω}
    (hAE : A ⊆ E) (hle : ∀e ∈ A, e ≤ c) (hpriv : Private A) : A.card ≤ rank E c := by
  classical
  exact Finset.le_sup (Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr hAE, hle, hpriv⟩)

lemma minimal_generators (E : Finset (Cylinder Ω)) (c : Cylinder Ω)
    (hc : ∃ A ⊆ E, Generates A c) :
    ∃ A ⊆ E, A.card ≤ rank E c ∧ Generates A c := by
  classical
  let S := E.powerset.filter (fun A => Generates A c)
  have hS : S.Nonempty := by
    obtain ⟨A, hAE, hA⟩ := hc
    exact ⟨A, Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr hAE,hA⟩⟩
  obtain ⟨A, hAS, hmin⟩ := Finset.exists_min_image S Finset.card hS
  have hAE : A ⊆ E := Finset.mem_powerset.mp (Finset.mem_filter.mp hAS).1
  have hgen : Generates A c := (Finset.mem_filter.mp hAS).2
  have hpriv : Private A := by
    intro e he
    by_contra h
    push Not at h
    have hg : Generates (A.erase e) c := by
      refine ⟨fun f hf => hgen.1 f (Finset.mem_of_mem_erase hf), ?_⟩
      intro p hp
      obtain ⟨f,hf,hpf⟩ := hgen.2 p hp
      by_cases hfe : f = e
      · subst f
        obtain ⟨g,hg,hpg,hge⟩ := h p hpf
        exact ⟨g, Finset.mem_erase.mpr ⟨hge,hg⟩,hpg⟩
      · exact ⟨f,Finset.mem_erase.mpr ⟨hfe,hf⟩,hpf⟩
    have hm := hmin (A.erase e) (Finset.mem_filter.mpr
      ⟨Finset.mem_powerset.mpr ((Finset.erase_subset e A).trans hAE), hg⟩)
    have hl := Finset.card_erase_lt_of_mem he
    omega
  exact ⟨A,hAE,card_le_rank hAE hgen.1 hpriv,hgen⟩

omit [∀ p, Fintype (Ω p)] in
lemma generated_width {E A : Finset (Cylinder Ω)} {c : Cylinder Ω} {w : ℕ}
    (hAE : A ⊆ E) (hgen : Generates A c)
    (hwidth : ∀e ∈ E, e.support.card ≤ w) : c.support.card ≤ A.card * w := by
  classical
  rw [generates_support hgen]
  calc
    (A.biUnion support).card ≤ ∑ e ∈ A, e.support.card := Finset.card_biUnion_le
    _ ≤ ∑ _e ∈ A, w := Finset.sum_le_sum fun e he => hwidth e (hAE he)
    _ = A.card * w := by simp

lemma rank_width {E : Finset (Cylinder Ω)} {c : Cylinder Ω} {w : ℕ}
    (hc : ∃ A ⊆ E, Generates A c) (hwidth : ∀e ∈ E, e.support.card ≤ w) :
    c.support.card ≤ w * rank E c := by
  obtain ⟨A,hAE,hcard,hgen⟩ := minimal_generators E c hc
  exact (generated_width hAE hgen hwidth).trans (by simpa [Nat.mul_comm] using Nat.mul_le_mul_right w hcard)

end Cylinder

end OrdinaryCorrelations.SourceCylinder

end

end OAI
