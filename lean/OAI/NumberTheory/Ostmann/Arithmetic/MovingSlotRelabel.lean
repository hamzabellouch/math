import OAI.NumberTheory.Ostmann.Arithmetic.MovingModularSpectator
import OAI.NumberTheory.Ostmann.Arithmetic.MovingSampleSizes

namespace OAI

/-! # Relabelling repeated sampled slots by their equality-pattern classes -/

namespace Ostmann
open scoped Classical

def MovingSlotReversal.map {σ τ : Type*} (f : σ → τ) (s : MovingSlotReversal σ) :
    MovingSlotReversal τ where
  left := s.left
  rootFrequency := s.rootFrequency
  leftFrequency := s.leftFrequency
  rightFrequency := s.rightFrequency
  leftSlots := s.leftSlots.map f
  rightSlots := s.rightSlots.map f
  compensationSlots := s.compensationSlots.map f

def MovingSlotData.map {σ τ : Type*} (f : σ → τ) :
    {n : ℕ} → MovingSlotData σ n → MovingSlotData τ n
  | _, .leaf s regular => .leaf s (regular.map f)
  | _, .node s CL CR u left right =>
      .node s (CL.map f) (CR.map f) (u.map f) (left.map f) (right.map f)

@[simp] theorem MovingSlotData.frequency_map {σ τ : Type*} (f : σ → τ)
    {n : ℕ} (T : MovingSlotData σ n) : (T.map f).frequency = T.frequency := by
  cases T <;> rfl

theorem MovingSlotData.frequencies_map {σ τ : Type*} (f : σ → τ)
    (P : ℤ → Prop) {n : ℕ} (T : MovingSlotData σ n) :
    (T.map f).Frequencies P ↔ T.Frequencies P := by
  induction T with
  | leaf => rfl
  | node s CL CR u left right ihL ihR =>
    simp only [MovingSlotData.map, MovingSlotData.Frequencies, ihL, ihR]

theorem MovingSlotData.size_map {σ τ : Type*} (f : σ → τ)
    (d : ℕ) {n : ℕ} (T : MovingSlotData σ n) : (T.map f).SizeLE d ↔ T.SizeLE d := by
  induction T with
  | leaf => rfl
  | node s CL CR u left right ihL ihR =>
    simp only [MovingSlotData.map, MovingSlotData.SizeLE, List.length_map, ihL, ihR]

theorem MovingSlotData.levels_map {σ τ : Type*} (f : σ → τ) (tier : σ → ℕ) (tier' : τ → ℕ)
    (htier : ∀ i, tier' (f i) = tier i) {n : ℕ} (T : MovingSlotData σ n) :
    (T.map f).Levels tier' ↔ T.Levels tier := by
  induction T with
  | leaf => rfl
  | node s CL CR u left right ihL ihR =>
    simp only [MovingSlotData.map, MovingSlotData.Levels, List.forall_mem_map, htier, ihL, ihR]

theorem MovingSlotReversal.naturalProduct_map {σ τ : Type*}
    (f : σ → τ) (value : τ → ℕ) (slots : List σ) :
    naturalProduct value (slots.map f) = naturalProduct (value ∘ f) slots := by
  simp only [naturalProduct, List.map_map]

theorem MovingSlotReversal.modularPivot_map {σ τ : Type*} (f : σ → τ)
    (value : τ → ℕ) (q : ℕ) [Fact q.Prime] (s : MovingSlotReversal σ) (x y : ZMod q) :
    (s.map f).modularPivot value q x y = s.modularPivot (value ∘ f) q x y := by
  simp only [modularPivot, map, naturalProduct_map]

theorem MovingSlotData.step_map {σ τ : Type*} (f : σ → τ)
    {n : ℕ} (s : ℤ) (CL CR u : List σ) (left right : MovingSlotData σ n) (b : Bool) :
    step s (CL.map f) (CR.map f) (u.map f) (left.map f) (right.map f) b =
      (step s CL CR u left right b).map f := by
  simp only [step, MovingSlotReversal.map, frequency_map]

/-- Evaluation after identifying two labels is precisely evaluation at the
corresponding repeated prime value; no independence is asserted here. -/
theorem movingModularSpectator_map {σ τ : Type*} (f : σ → τ)
    (value : τ → ℕ) (q : ℕ) [Fact q.Prime] (g : ZMod q → ℂ) (D : (ZMod q)ˣ)
    {n : ℕ} (T : MovingSlotData σ n) (x y : ZMod q) :
    movingModularSpectator value q g D (T.map f) x y =
      movingModularSpectator (value ∘ f) q g D T x y := by
  induction T generalizing x y with
  | leaf => simp only [MovingSlotData.map, movingModularSpectator, MovingSlotReversal.naturalProduct_map]
  | node s CL CR u left right ihL ihR =>
    simp only [MovingSlotData.map, movingModularSpectator, MovingSlotData.step_map,
      MovingSlotReversal.modularPivot_map, ihL, ihR]

end Ostmann

end OAI
