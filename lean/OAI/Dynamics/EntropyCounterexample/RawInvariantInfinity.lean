import OAI.Dynamics.EntropyCounterexample.SkewProduct
import OAI.Dynamics.EntropyCounterexample.ClockAtInfinity

namespace OAI

noncomputable section

open scoped OnePoint

namespace Problem340

def rawInfinityPoint (q : ℕ) (t : ClockAtInfinity.Clock) : RawState q :=
  (t, ∞, fun _ => ((0 : ℂ) : OnePoint ℂ))

def rawInfinitySet (q : ℕ) : Set (RawState q) := Set.range (rawInfinityPoint q)

@[continuity, fun_prop]
theorem continuous_rawInfinityPoint (q : ℕ) : Continuous (rawInfinityPoint q) := by
  exact continuous_id.prodMk (continuous_const.prodMk continuous_const)

theorem rawInfinityPoint_injective (q : ℕ) : Function.Injective (rawInfinityPoint q) :=
  fun _ _ h => congrArg Prod.fst h

theorem rawInfinitySet_nonempty (q : ℕ) : (rawInfinitySet q).Nonempty :=
  Set.range_nonempty _

theorem isCompact_rawInfinitySet (q : ℕ) : IsCompact (rawInfinitySet q) := by
  let : Fact (0 < (100 : ℝ)) := ⟨by norm_num⟩
  exact isCompact_range (continuous_rawInfinityPoint q)

theorem mem_rawInfinitySet_iff {q : ℕ} (x : RawState q) :
    x ∈ rawInfinitySet q ↔ x.2.1 = ∞ ∧ ∀ i, x.2.2 i = ((0 : ℂ) : OnePoint ℂ) := by
  constructor
  · rintro ⟨t, rfl⟩
    exact ⟨rfl, fun _ => rfl⟩
  · rintro ⟨hz, hv⟩
    refine ⟨x.1, ?_⟩
    apply Prod.ext
    · rfl
    · apply Prod.ext
      · exact hz.symm
      · funext i
        exact (hv i).symm

theorem rawUpdate_rawInfinityPoint {q : ℕ}
    (h : RawState q → ℝ) (C : RawState q → ℂ) (R : RawState q → Fin q → ℂ)
    (hh : ∀ t, h (rawInfinityPoint q t) = 1)
    (hR : ∀ t i, R (rawInfinityPoint q t) i = 0)
    (t : ClockAtInfinity.Clock) :
    rawUpdate h C R (rawInfinityPoint q t) =
      rawInfinityPoint q (ClockAtInfinity.step t) := by
  apply Prod.ext
  · change t + (h (rawInfinityPoint q t) : AddCircle (100 : ℝ)) =
      t + ((1 : ℝ) : AddCircle (100 : ℝ))
    rw [hh]
  · apply Prod.ext
    · rfl
    · funext i
      change ((R (rawInfinityPoint q t) i : ℂ) : OnePoint ℂ) = ((0 : ℂ) : OnePoint ℂ)
      rw [hR]

theorem rawInfinityPoint_semiconj {q : ℕ}
    (h : RawState q → ℝ) (C : RawState q → ℂ) (R : RawState q → Fin q → ℂ)
    (hh : ∀ t, h (rawInfinityPoint q t) = 1)
    (hR : ∀ t i, R (rawInfinityPoint q t) i = 0) :
    Function.Semiconj (rawInfinityPoint q) ClockAtInfinity.step (rawUpdate h C R) :=
  fun t => (rawUpdate_rawInfinityPoint h C R hh hR t).symm

theorem rawUpdate_mapsTo_infinitySet {q : ℕ}
    (h : RawState q → ℝ) (C : RawState q → ℂ) (R : RawState q → Fin q → ℂ)
    (hh : ∀ t, h (rawInfinityPoint q t) = 1)
    (hR : ∀ t i, R (rawInfinityPoint q t) i = 0) :
    Set.MapsTo (rawUpdate h C R) (rawInfinitySet q) (rawInfinitySet q) := by
  rintro x ⟨t, rfl⟩
  exact ⟨ClockAtInfinity.step t, (rawUpdate_rawInfinityPoint h C R hh hR t).symm⟩

theorem coverEntropy_realizedInfinitySet {q : ℕ}
    {X : Type*} [UniformSpace X] {T : X → X}
    (h : RawState q → ℝ) (C : RawState q → ℂ) (R : RawState q → Fin q → ℂ)
    (hh : ∀ t, h (rawInfinityPoint q t) = 1)
    (hR : ∀ t i, R (rawInfinityPoint q t) i = 0)
    {φ : RawState q → X} (hφ : Continuous φ)
    (hsem : Function.Semiconj φ (rawUpdate h C R) T) :
    Dynamics.coverEntropy T (φ '' rawInfinitySet q) = 0 := by
  rw [rawInfinitySet, ← Set.range_comp]
  apply ClockAtInfinity.coverEntropy_clockImage
    (hφ.comp (continuous_rawInfinityPoint q))
  intro t
  change φ (rawInfinityPoint q (ClockAtInfinity.step t)) = T (φ (rawInfinityPoint q t))
  rw [← rawUpdate_rawInfinityPoint h C R hh hR t]
  exact hsem (rawInfinityPoint q t)

end Problem340

end

end OAI
