import OAI.NumberTheory.Ostmann.Arithmetic.ArithmeticCRTSeparation

namespace OAI

/-! # The actual squared regular transform in the diagonal CRT average -/

namespace Ostmann
open scoped BigOperators Classical

/-- `other i` is the fixed denominator consisting of the outside and all
small slots other than the regular prime `i`. The two giants are retained. -/
noncomputable def diagonalRegularMultiplier {I : Type*} [Fintype I]
    (p : I → ℕ) [∀ i, Fact (p i).Prime] (active : I → Bool)
    (s : ℤ) (other : ∀ i, ZMod (p i)) (g : ∀ i, ZMod (p i) → ℂ)
    (z : ∀ i, ZMod (p i) × (ZMod (p i))ˣ) : ℝ :=
  if ∀ i, (z i).1 ≠ 0 then
    ∏ i, if active i then
      ‖g i ((s : ZMod (p i)) / (other i * (z i).1 * ((z i).2 : ZMod (p i))))‖ ^ 2 else 1
  else 0

noncomputable def diagonalRegularCoefficient {I : Type*} (p : I → ℕ) [∀ i, Fact (p i).Prime]
    (s : ℤ) (other : ∀ i, ZMod (p i)) (hs : ∀ i, (s : ZMod (p i)) ≠ 0)
    (ho : ∀ i, other i ≠ 0) (i : I) : (ZMod (p i))ˣ :=
  Units.mk0 ((s : ZMod (p i)) / other i) (div_ne_zero (hs i) (ho i))

theorem diagonalRegularMultiplier_local {I : Type*} [Fintype I]
    (p : I → ℕ) [∀ i, Fact (p i).Prime] (active : I → Bool)
    (s : ℤ) (other : ∀ i, ZMod (p i)) (hs : ∀ i, (s : ZMod (p i)) ≠ 0)
    (ho : ∀ i, other i ≠ 0) (g : ∀ i, ZMod (p i) → ℂ)
    (z : ∀ i, ZMod (p i) × (ZMod (p i))ˣ) :
    diagonalRegularMultiplier p active s other g z =
      ∏ i, externalRegularLocal (active i) (diagonalRegularCoefficient p s other hs ho i) (g i) (z i) := by
  by_cases hz : ∀ i, (z i).1 ≠ 0
  · rw [diagonalRegularMultiplier, ite_eq_left hz]
    apply Finset.prod_congr rfl
    intro i _
    rw [externalRegularLocal, ite_eq_right (hz i)]
    cases active i
    · rfl
    · simp only [ite_true, diagonalRegularCoefficient, Units.val_mk0,
        div_eq_mul_inv, mul_inv_rev]
      apply congrArg (fun x : ZMod (p i) => ‖g i x‖ ^ 2)
      ring
  · rw [diagonalRegularMultiplier, ite_eq_right hz]
    obtain ⟨i, hi⟩ := not_forall.mp hz
    have hiz : (z i).1 = 0 := not_ne_iff.mp hi
    symm
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    simp only [externalRegularLocal, hiz, ite_true]

/-- The manuscript's regular multiplier is integrated before taking any
absolute value of the signed remainder, which may include Page factors. -/
theorem diagonalRegularMultiplier_crt {I : Type*} [Fintype I] [DecidableEq I]
    (p : I → ℕ) [∀ i, Fact (p i).Prime] [∀ i, NeZero (p i)] [NeZero (∏ i, p i)]
    (hc : Pairwise (fun i j => (p i).Coprime (p j)))
    (r : ℕ) [NeZero r] [NeZero ((∏ i, p i) * r)] (hcop : (∏ i, p i).Coprime r)
    (active : I → Bool) (s : ℤ) (other : ∀ i, ZMod (p i))
    (hs : ∀ i, (s : ZMod (p i)) ≠ 0) (ho : ∀ i, other i ≠ 0)
    (g : ∀ i, ZMod (p i) → ℂ) (hg : ∀ i, g i 0 = 0)
    (henergy : ∀ i, (∑ x : ZMod (p i), ‖g i x‖ ^ 2) = p i)
    (F : ZMod r × (ZMod r)ˣ → ℂ) :
    (Fintype.card (ZMod ((∏ i, p i) * r) × (ZMod ((∏ i, p i) * r))ˣ) : ℂ)⁻¹ *
      (∑ z, (diagonalRegularMultiplier p active s other g
        (crtExternalPairEquiv p hc (crtSplitExternalEquiv (∏ i, p i) r hcop z).1) : ℂ) *
          F (crtSplitExternalEquiv (∏ i, p i) r hcop z).2) =
      ((∏ i, if active i then (1 : ℝ) else 1 - (p i : ℝ)⁻¹ : ℝ) : ℂ) *
        ((Fintype.card (ZMod r × (ZMod r)ˣ) : ℂ)⁻¹ * ∑ z, F z) := by
  simp_rw [diagonalRegularMultiplier_local p active s other hs ho g]
  exact crt_external_regular_with_remainder p hc r hcop active
    (diagonalRegularCoefficient p s other hs ho) g hg henergy F

end Ostmann

end OAI
