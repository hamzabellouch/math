import OAI.NumberTheory.Ostmann.Construction.DiagonalRegularMultiplier
import OAI.NumberTheory.Ostmann.Arithmetic.MovingSupportedWeight

namespace OAI

/-! # The displayed regular-prime multiplier on actual natural giants -/

namespace Ostmann
open scoped BigOperators Classical

noncomputable def naturalRegularMultiplier {I : Type*} [Fintype I]
    (p : I → ℕ) [∀ i, Fact (p i).Prime] (active : I → Bool) (s : ℤ)
    (other : ∀ i, ZMod (p i)) (g : ∀ i, ZMod (p i) → ℂ) (XL XR : ℕ) : ℝ :=
  ∏ i, if active i then
    ‖g i ((s : ZMod (p i)) / (other i * (XL : ZMod (p i)) * (XR : ZMod (p i))))‖ ^ 2 else 1

noncomputable def guardedRegularMultiplier {I : Type*} [Fintype I]
    (p : I → ℕ) [∀ i, Fact (p i).Prime] (active : I → Bool) (s : ℤ)
    (other : ∀ i, ZMod (p i)) (g : ∀ i, ZMod (p i) → ℂ) (XL XR : ℕ) : ℝ :=
  if ∀ i, (XL : ZMod (p i)) ≠ 0 ∧ (XR : ZMod (p i)) ≠ 0 then
    naturalRegularMultiplier p active s other g XL XR else 0

theorem guardedRegularMultiplier_modEq {I : Type*} [Fintype I]
    (p : I → ℕ) [∀ i, Fact (p i).Prime] (active : I → Bool) (s : ℤ)
    (other : ∀ i, ZMod (p i)) (g : ∀ i, ZMod (p i) → ℂ) (XL XR YL YR M : ℕ)
    (hp : ∀ i, p i ∣ M) (hL : Nat.ModEq M XL YL) (hR : Nat.ModEq M XR YR) :
    guardedRegularMultiplier p active s other g XL XR = guardedRegularMultiplier p active s other g YL YR := by
  have hl (i : I) : (XL : ZMod (p i)) = (YL : ZMod (p i)) :=
    (ZMod.natCast_eq_natCast_iff _ _ _).mpr (hL.of_dvd (hp i))
  have hr (i : I) : (XR : ZMod (p i)) = (YR : ZMod (p i)) :=
    (ZMod.natCast_eq_natCast_iff _ _ _).mpr (hR.of_dvd (hp i))
  simp only [guardedRegularMultiplier, naturalRegularMultiplier, hl, hr]

theorem guardedRegularMultiplier_eq_diagonal {I : Type*} [Fintype I]
    (p : I → ℕ) [∀ i, Fact (p i).Prime] (active : I → Bool) (s : ℤ)
    (other : ∀ i, ZMod (p i)) (g : ∀ i, ZMod (p i) → ℂ) (XL XR : ℕ)
    (z : ∀ i, ZMod (p i) × (ZMod (p i))ˣ)
    (hL : ∀ i, (XL : ZMod (p i)) = (z i).1)
    (hR : ∀ i, (XR : ZMod (p i)) = ((z i).2 : ZMod (p i))) :
    guardedRegularMultiplier p active s other g XL XR = diagonalRegularMultiplier p active s other g z := by
  have hu (i : I) : ((z i).2 : ZMod (p i)) ≠ 0 := Units.ne_zero _
  have hguard : (∀ i, (z i).1 ≠ 0 ∧ ((z i).2 : ZMod (p i)) ≠ 0) ↔ ∀ i, (z i).1 ≠ 0 :=
    ⟨fun h i => (h i).1, fun h i => ⟨h i, hu i⟩⟩
  simp only [guardedRegularMultiplier, naturalRegularMultiplier, hL, hR, diagonalRegularMultiplier]
  simp only [hguard]

theorem guardedRegularMultiplier_bound {I : Type*} [Fintype I]
    (p : I → ℕ) [∀ i, Fact (p i).Prime] (active : I → Bool) (s : ℤ)
    (other : ∀ i, ZMod (p i)) (g : ∀ i, ZMod (p i) → ℂ)
    (B : I → ℝ) (hg : ∀ i x, ‖g i x‖ ≤ B i) (XL XR : ℕ) :
    0 ≤ guardedRegularMultiplier p active s other g XL XR ∧
      guardedRegularMultiplier p active s other g XL XR ≤ ∏ i, if active i then B i ^ 2 else 1 := by
  have hnonneg (x : I) : 0 ≤ if active x then B x ^ 2 else 1 := by split <;> positivity
  unfold guardedRegularMultiplier naturalRegularMultiplier
  split_ifs
  · constructor
    · apply Finset.prod_nonneg
      intro i _
      split <;> positivity
    · apply Finset.prod_le_prod₀
      · intro i _
        split <;> positivity
      · intro i _
        cases active i
        · exact le_rfl
        · exact pow_le_pow_left₀ (norm_nonneg _) (hg i _) 2
  · exact ⟨le_rfl, Finset.prod_nonneg (fun i _ => hnonneg i)⟩

theorem movingNaturalGiantUnits_root {σ : Type*} (value : σ → ℕ) (outside : List ℕ)
    {n : ℕ} (T : MovingSlotData σ n) (XL XR : ℕ)
    (h : movingNaturalGiantUnits value outside T XL XR) : movingLocalGiantUnits value outside T XL XR := by
  cases T with
  | leaf => exact h
  | node => exact h.1

theorem movingSupportedWeight_regular_multiplier {σ I : Type*} [Fintype I]
    (value : σ → ℕ) (outside : List ℕ) {n : ℕ} (T : MovingSlotData σ n)
    (p : I → ℕ) [∀ i, Fact (p i).Prime] (label : I → σ)
    (hp : ∀ i, value (label i) = p i) (hmem : ∀ i, label i ∈ T.regularSlots)
    (active : I → Bool) (s : ℤ) (other : ∀ i, ZMod (p i)) (g : ∀ i, ZMod (p i) → ℂ)
    (XL XR : ℕ) (z : ℂ) :
    movingSupportedWeight value outside T XL XR z * (naturalRegularMultiplier p active s other g XL XR : ℂ) =
      movingSupportedWeight value outside T XL XR z * (guardedRegularMultiplier p active s other g XL XR : ℂ) := by
  by_cases hS : movingFullSupport value outside T XL XR
  · have hloc := movingNaturalGiantUnits_root value outside T XL XR hS.2
    have hguard (i : I) : (XL : ZMod (p i)) ≠ 0 ∧ (XR : ZMod (p i)) ≠ 0 := by
      have hd : p i ∣ MovingSlotReversal.naturalProduct value T.regularSlots := by
        rw [← hp i]
        exact List.dvd_prod (List.mem_map.mpr ⟨label i, hmem i, rfl⟩)
      have hdZ : (p i : ℤ) ∣ (MovingSlotReversal.naturalProduct value T.regularSlots : ℤ) := by exact_mod_cast hd
      have hleft := hloc.2.2.1.of_isCoprime_of_dvd_right hdZ
      have hright := hloc.2.2.2.1.of_isCoprime_of_dvd_right hdZ
      constructor
      · have hu : IsUnit (XL : ZMod (p i)) := by
          apply isCoprime_zero_right.mp
          simpa only [Int.cast_natCast, ZMod.natCast_self] using hleft.intCast (R := ZMod (p i))
        exact hu.ne_zero
      · have hu : IsUnit (XR : ZMod (p i)) := by
          apply isCoprime_zero_right.mp
          simpa only [Int.cast_natCast, ZMod.natCast_self] using hright.intCast (R := ZMod (p i))
        exact hu.ne_zero
    rw [guardedRegularMultiplier, ite_eq_left hguard]
  · simp only [movingSupportedWeight, ite_eq_right hS, zero_mul]

end Ostmann

end OAI
