import OAI.NumberTheory.Ostmann.Arithmetic.MovingSlotLines

namespace OAI

/-! # Actual occurrence paths and absence of their compensation type -/

namespace Ostmann
open scoped Classical

/-- At a node, the two regular lists exclude its moving giants. The
compensation list is inserted in both children by the sampler. -/
inductive MovingSlotData (σ : Type*) : ℕ → Type _
  | leaf (s : ℤ) (regular : List σ) : MovingSlotData σ 0
  | node {n : ℕ} (s : ℤ) (leftRegular rightRegular compensation : List σ)
      (left right : MovingSlotData σ n) : MovingSlotData σ (n + 1)

def MovingSlotData.frequency {σ : Type*} : {n : ℕ} → MovingSlotData σ n → ℤ
  | _, .leaf s _ => s
  | _, .node s _ _ _ _ _ => s

def MovingSlotData.step {σ : Type*} {n : ℕ} (s : ℤ) (CL CR u : List σ)
    (left right : MovingSlotData σ n) (b : Bool) : MovingSlotReversal σ where
  left := b
  rootFrequency := s
  leftFrequency := left.frequency
  rightFrequency := right.frequency
  leftSlots := CL
  rightSlots := CR
  compensationSlots := u

structure MovingSlotOccurrence (σ : Type*) where
  level : ℕ
  current : MovingSlotReversal σ
  path : List (MovingSlotReversal σ)

def MovingSlotOccurrence.extend {σ : Type*} (o : MovingSlotOccurrence σ)
    (s : MovingSlotReversal σ) : MovingSlotOccurrence σ :=
  { o with path := o.path ++ [s] }

/-- Each root-to-occurrence path is recorded in the order of the cleared
ancestor recursion, so the newest reversal occurs first. -/
def MovingSlotData.occurrences {σ : Type*} : {n : ℕ} → MovingSlotData σ n → List (MovingSlotOccurrence σ)
  | _, .leaf _ _ => []
  | n + 1, .node s CL CR u left right =>
      ⟨n + 1, step s CL CR u left right false, []⟩ ::
        (left.occurrences.map (fun o => o.extend (step s CL CR u left right true))) ++
        (right.occurrences.map (fun o => o.extend (step s CL CR u left right false)))

def MovingSlotData.Levels {σ : Type*} (tier : σ → ℕ) :
    {n : ℕ} → MovingSlotData σ n → Prop
  | _, .leaf _ _ => True
  | n + 1, .node _ CL CR u left right =>
      (∀ i ∈ CL, n + 1 ≤ tier i) ∧ (∀ i ∈ CR, n + 1 ≤ tier i) ∧
      (∀ i ∈ u, tier i = n) ∧ left.Levels tier ∧ right.Levels tier

def MovingSlotOccurrence.AvoidsBelow {σ : Type*} (tier : σ → ℕ)
    (o : MovingSlotOccurrence σ) : Prop :=
  (∀ s ∈ o.path, (∀ i ∈ s.leftSlots, o.level ≤ tier i) ∧
    (∀ i ∈ s.rightSlots, o.level ≤ tier i) ∧
    (∀ i ∈ s.compensationSlots, o.level ≤ tier i)) ∧
  (∀ i ∈ o.current.leftSlots, o.level ≤ tier i) ∧
  (∀ i ∈ o.current.rightSlots, o.level ≤ tier i)

/-- The current compensation type is strictly below every variable in the
current numerator and all its ancestor denominators. This holds for every
occurrence simultaneously, including repeated occurrences of one sample. -/
theorem MovingSlotData.occurrence_bounds {σ : Type*} (tier : σ → ℕ) {n : ℕ}
    (T : MovingSlotData σ n) (hT : T.Levels tier) :
    ∀ o ∈ T.occurrences, 0 < o.level ∧ o.level + o.path.length ≤ n ∧ o.AvoidsBelow tier := by
  induction T with
  | leaf s regular => simp [occurrences]
  | @node n s CL CR u left right ihL ihR =>
    intro o ho
    rcases List.mem_cons.mp ho with ho | ho
    · subst o
      refine ⟨by change 0 < n + 1; omega, by change n + 1 + 0 ≤ n + 1; omega, ?_⟩
      exact ⟨by simp, hT.1, hT.2.1⟩
    · have hl := ihL hT.2.2.2.1
      have hr := ihR hT.2.2.2.2
      rcases List.mem_append.mp ho with ho | ho
      · obtain ⟨o', ho', rfl⟩ := List.mem_map.mp ho
        obtain ⟨hp, hlen, ha, hb, hc⟩ := hl o' ho'
        refine ⟨hp, ?_, ?_, hb, hc⟩
        · simpa only [MovingSlotOccurrence.extend, List.length_append, List.length_singleton] using
            (show o'.level + (o'.path.length + 1) ≤ n + 1 by omega)
        · intro t ht
          rcases List.mem_append.mp ht with ht | ht
          · exact ha t ht
          · have he := List.mem_singleton.mp ht
            subst t
            refine ⟨?_, ?_, ?_⟩
            · intro i hi
              exact (show o'.level ≤ n + 1 by omega).trans (hT.1 i hi)
            · intro i hi
              exact (show o'.level ≤ n + 1 by omega).trans (hT.2.1 i hi)
            · intro i hi
              change o'.level ≤ tier i
              rw [hT.2.2.1 i hi]
              omega
      · obtain ⟨o', ho', rfl⟩ := List.mem_map.mp ho
        obtain ⟨hp, hlen, ha, hb, hc⟩ := hr o' ho'
        refine ⟨hp, ?_, ?_, hb, hc⟩
        · simpa only [MovingSlotOccurrence.extend, List.length_append, List.length_singleton] using
            (show o'.level + (o'.path.length + 1) ≤ n + 1 by omega)
        · intro t ht
          rcases List.mem_append.mp ht with ht | ht
          · exact ha t ht
          · have he := List.mem_singleton.mp ht
            subst t
            refine ⟨?_, ?_, ?_⟩
            · intro i hi
              exact (show o'.level ≤ n + 1 by omega).trans (hT.1 i hi)
            · intro i hi
              exact (show o'.level ≤ n + 1 by omega).trans (hT.2.1 i hi)
            · intro i hi
              change o'.level ≤ tier i
              rw [hT.2.2.1 i hi]
              omega

theorem MovingSlotOccurrence.absent_of_level {σ : Type*} (tier : σ → ℕ)
    (o : MovingSlotOccurrence σ) (ho : o.AvoidsBelow tier) (i : σ) (hi : tier i < o.level) :
    (∀ s ∈ o.path, i ∉ s.leftSlots ∧ i ∉ s.rightSlots ∧ i ∉ s.compensationSlots) ∧
      i ∉ o.current.leftSlots ∧ i ∉ o.current.rightSlots := by
  refine ⟨?_, ?_, ?_⟩
  · intro s hs
    exact ⟨fun h => (not_le.mpr hi) ((ho.1 s hs).1 i h),
      fun h => (not_le.mpr hi) ((ho.1 s hs).2.1 i h),
      fun h => (not_le.mpr hi) ((ho.1 s hs).2.2 i h)⟩
  · exact fun h => (not_le.mpr hi) (ho.2.1 i h)
  · exact fun h => (not_le.mpr hi) (ho.2.2 i h)

end Ostmann

end OAI
