import OAI.NumberTheory.Ostmann.Construction.RegularGiantMultiplier

namespace OAI

/-! # The displayed natural-giant regular multiplier in the CRT average -/

namespace Ostmann
open scoped BigOperators Classical

theorem regular_unit_tests_iff {I : Type*} [Fintype I]
    (p : I → ℕ) [∀ i, Fact (p i).Prime] (XL XR : ℕ) :
    (∀ i, (XL : ZMod (p i)) ≠ 0 ∧ (XR : ZMod (p i)) ≠ 0) ↔
      XL.Coprime (∏ i, p i) ∧ XR.Coprime (∏ i, p i) := by
  simp only [← isUnit_iff_ne_zero, ZMod.isUnit_iff_coprime,
    Nat.coprime_prod_right_iff, Finset.mem_univ, forall_true_left, forall_and]

theorem guardedRegularMultiplier_eq_coprime {I : Type*} [Fintype I]
    (p : I → ℕ) [∀ i, Fact (p i).Prime] (active : I → Bool) (s : ℤ)
    (other : ∀ i, ZMod (p i)) (g : ∀ i, ZMod (p i) → ℂ) (XL XR : ℕ) :
    guardedRegularMultiplier p active s other g XL XR =
      if XL.Coprime (∏ i, p i) ∧ XR.Coprime (∏ i, p i) then
        naturalRegularMultiplier p active s other g XL XR else 0 := by
  simp only [guardedRegularMultiplier, regular_unit_tests_iff]

theorem multiply_regular_after_support {I : Type*} [Fintype I]
    (p : I → ℕ) [∀ i, Fact (p i).Prime] (active : I → Bool) (s : ℤ)
    (other : ∀ i, ZMod (p i)) (g : ∀ i, ZMod (p i) → ℂ) (XL XR : ℕ)
    (w c k : ℂ)
    (hw : w = if XL.Coprime XR ∧ XL.Coprime (∏ i, p i) ∧ XR.Coprime (∏ i, p i)
      then c * k else 0) :
    w * (naturalRegularMultiplier p active s other g XL XR : ℂ) =
      if XL.Coprime XR then (c * (guardedRegularMultiplier p active s other g XL XR : ℂ)) * k else 0 := by
  rw [hw, guardedRegularMultiplier_eq_coprime]
  by_cases hpair : XL.Coprime XR <;>
    by_cases hreg : XL.Coprime (∏ i, p i) ∧ XR.Coprime (∏ i, p i)
  · rw [ite_eq_left ⟨hpair, hreg⟩, ite_eq_left hreg, ite_eq_left hpair]
    ring
  · rw [ite_eq_right (fun h => hreg h.2), ite_eq_right hreg, ite_eq_left hpair]
    simp
  · rw [ite_eq_right (fun h => hpair h.1), ite_eq_right hpair]
    simp
  · rw [ite_eq_right (fun h => hpair h.1), ite_eq_right hpair]
    simp

theorem guardedRegularMultiplier_crt {I : Type*} [Fintype I] [DecidableEq I]
    (p : I → ℕ) [∀ i, Fact (p i).Prime] [∀ i, NeZero (p i)] [NeZero (∏ i, p i)]
    (hc : Pairwise (fun i j => (p i).Coprime (p j)))
    (r : ℕ) [NeZero r] [NeZero ((∏ i, p i) * r)] (hcop : (∏ i, p i).Coprime r)
    (active : I → Bool) (s : ℤ) (other : ∀ i, ZMod (p i)) (g : ∀ i, ZMod (p i) → ℂ)
    (z : ZMod ((∏ i, p i) * r) × (ZMod ((∏ i, p i) * r))ˣ) :
    guardedRegularMultiplier p active s other g z.1.val (z.2 : ZMod ((∏ i, p i) * r)).val =
      diagonalRegularMultiplier p active s other g
        (crtExternalPairEquiv p hc (crtSplitExternalEquiv (∏ i, p i) r hcop z).1) := by
  apply guardedRegularMultiplier_eq_diagonal
  · intro i
    change (z.1.val : ZMod (p i)) =
      ZMod.prodEquivPi p hc ((ZMod.chineseRemainder hcop) z.1).1 i
    have h := congrArg (fun x : ZMod ((∏ i, p i) * r) =>
      ZMod.prodEquivPi p hc ((ZMod.chineseRemainder hcop) x).1 i)
      (ZMod.natCast_zmod_val z.1)
    simpa only [map_natCast, Prod.fst_natCast, Pi.natCast_apply] using h
  · intro i
    change ((z.2 : ZMod ((∏ i, p i) * r)).val : ZMod (p i)) =
      ZMod.prodEquivPi p hc ((ZMod.chineseRemainder hcop) (z.2 : ZMod ((∏ i, p i) * r))).1 i
    have h := congrArg (fun x : ZMod ((∏ i, p i) * r) =>
      ZMod.prodEquivPi p hc ((ZMod.chineseRemainder hcop) x).1 i)
      (ZMod.natCast_zmod_val (z.2 : ZMod ((∏ i, p i) * r)))
    simpa only [map_natCast, Prod.fst_natCast, Pi.natCast_apply] using h

/-- This is the actual natural-coordinate multiplier, not an auxiliary copy
of its transform. The remainder stays complex and may contain the Page factor. -/
theorem guardedRegularMultiplier_average {I : Type*} [Fintype I] [DecidableEq I]
    (p : I → ℕ) [∀ i, Fact (p i).Prime] [∀ i, NeZero (p i)] [NeZero (∏ i, p i)]
    (hc : Pairwise (fun i j => (p i).Coprime (p j)))
    (r : ℕ) [NeZero r] [NeZero ((∏ i, p i) * r)] (hcop : (∏ i, p i).Coprime r)
    (active : I → Bool) (s : ℤ) (other : ∀ i, ZMod (p i))
    (hs : ∀ i, (s : ZMod (p i)) ≠ 0) (ho : ∀ i, other i ≠ 0)
    (g : ∀ i, ZMod (p i) → ℂ) (hg : ∀ i, g i 0 = 0)
    (henergy : ∀ i, (∑ x : ZMod (p i), ‖g i x‖ ^ 2) = p i)
    (F : ZMod r × (ZMod r)ˣ → ℂ) :
    (Fintype.card (ZMod ((∏ i, p i) * r) × (ZMod ((∏ i, p i) * r))ˣ) : ℂ)⁻¹ *
      (∑ z, (guardedRegularMultiplier p active s other g z.1.val
        (z.2 : ZMod ((∏ i, p i) * r)).val : ℂ) *
          F (crtSplitExternalEquiv (∏ i, p i) r hcop z).2) =
      ((∏ i, if active i then (1 : ℝ) else 1 - (p i : ℝ)⁻¹ : ℝ) : ℂ) *
        ((Fintype.card (ZMod r × (ZMod r)ˣ) : ℂ)⁻¹ * ∑ z, F z) := by
  simp_rw [guardedRegularMultiplier_crt p hc r hcop active s other g]
  exact diagonalRegularMultiplier_crt p hc r hcop active s other hs ho g hg henergy F

end Ostmann

end OAI
