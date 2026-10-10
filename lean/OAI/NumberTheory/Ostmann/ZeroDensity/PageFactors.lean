import Mathlib.Analysis.SpecialFunctions.Exp
import OAI.NumberTheory.Ostmann.Construction.FinitePriorComparison
import OAI.NumberTheory.Ostmann.Arithmetic.CRTResidueAverage

namespace OAI

/-! # Keeping the exceptional-character density in the arithmetic measures

The correction is retained, including when it correlates with the amplitude.
Once its conductor is supported on the frequency modulus, CRT places it in
that coordinate and the other residue averages factor exactly.
-/

namespace Ostmann

open scoped BigOperators

noncomputable def pageMultiplier {A : Type*} (χ : A → ℝ) (β t : ℝ) (a : A) : ℝ :=
  1 - χ a * Real.exp ((β - 1) * t)

theorem pageMultiplier_bounds {A : Type*} (χ : A → ℝ) (β t : ℝ)
    (hχ : ∀ a, |χ a| ≤ 1) (hβ : β ≤ 1) (ht : 0 ≤ t) (a : A) :
    0 ≤ pageMultiplier χ β t a ∧ pageMultiplier χ β t a ≤ 2 := by
  have he0 := (Real.exp_pos ((β - 1) * t)).le
  have he1 : Real.exp ((β - 1) * t) ≤ 1 := Real.exp_le_one_iff.mpr
    (mul_nonpos_of_nonpos_of_nonneg (by linarith) ht)
  have hχa := abs_le.mp (hχ a)
  have hprod := mul_le_mul_of_nonneg_right hχa.2 he0
  have hprod' := mul_le_mul_of_nonneg_right hχa.1 he0
  dsimp [pageMultiplier]
  constructor <;> nlinarith

theorem pageMultiplier_zero {A : Type*} (β t : ℝ) (a : A) :
    pageMultiplier (fun _ : A => 0) β t a = 1 := by simp [pageMultiplier]

/-- The corrected coordinate prior has mass at most two, even if its
exceptional character has nonzero mean under the original prior. -/
theorem page_prior_mass_le_two {A : Type*} [Fintype A]
    (μ : A → ℝ) (hμ : ∀ a, 0 ≤ μ a) (hmass : ∑ a, μ a ≤ 1)
    (χ : A → ℝ) (β t : ℝ) (hχ : ∀ a, |χ a| ≤ 1) (hβ : β ≤ 1) (ht : 0 ≤ t) :
    (∀ a, 0 ≤ μ a * pageMultiplier χ β t a) ∧
      (∑ a, μ a * pageMultiplier χ β t a) ≤ 2 := by
  constructor
  · intro a
    exact mul_nonneg (hμ a) (pageMultiplier_bounds χ β t hχ hβ ht a).1
  · calc
      _ ≤ ∑ a, μ a * 2 := Finset.sum_le_sum fun a _ =>
        mul_le_mul_of_nonneg_left (pageMultiplier_bounds χ β t hχ hβ ht a).2 (hμ a)
      _ = (∑ a, μ a) * 2 := (Finset.sum_mul _ _ _).symm
      _ ≤ 2 := by linarith

/-- Exact separation of a retained density and all remaining coordinates.
This also applies to signed and complex amplitudes. -/
theorem uniform_equiv_product_average {A B C : Type*}
    [Fintype A] [Fintype B] [Fintype C]
    (e : A ≃ B × C) (f : B → ℂ) (g : C → ℂ) :
    (Fintype.card A : ℂ)⁻¹ * (∑ a, f (e a).1 * g (e a).2) =
      ((Fintype.card B : ℂ)⁻¹ * ∑ b, f b) *
        ((Fintype.card C : ℂ)⁻¹ * ∑ c, g c) := by
  rw [e.sum_comp (fun z => f z.1 * g z.2), Fintype.card_congr e,
    Fintype.card_prod, Nat.cast_mul, mul_inv_rev, Fintype.sum_prod_type]
  simp_rw [← Finset.mul_sum]
  rw [← Finset.sum_mul]
  ring

/-- In the finite box decomposition, the Page factor remains inside the
frequency-coordinate integral; it is never replaced by its mean. -/
theorem retained_page_average {A B C : Type*}
    [Fintype A] [Fintype B] [Fintype C]
    (e : A ≃ B × C) (χ : B → ℝ) (β t : ℝ) (f : B → ℂ) (g : C → ℂ) :
    (Fintype.card A : ℂ)⁻¹ *
        (∑ a, (pageMultiplier χ β t (e a).1 : ℂ) * f (e a).1 * g (e a).2) =
      ((Fintype.card B : ℂ)⁻¹ * ∑ b, (pageMultiplier χ β t b : ℂ) * f b) *
        ((Fintype.card C : ℂ)⁻¹ * ∑ c, g c) :=
  uniform_equiv_product_average e (fun b => (pageMultiplier χ β t b : ℂ) * f b) g

/-- The retained frequency block and all other unit residues in the actual
modulus. -/
noncomputable def crtSplitUnitEquiv (q r : ℕ) (h : q.Coprime r) :
    (ZMod (q * r))ˣ ≃ (ZMod q)ˣ × (ZMod r)ˣ :=
  ((Units.mapEquiv (ZMod.chineseRemainder h).toMulEquiv).trans
    MulEquiv.prodUnits).toEquiv

theorem crt_retained_page_average (q r : ℕ) [NeZero q] [NeZero r]
    [NeZero (q * r)] (h : q.Coprime r)
    (χ : (ZMod q)ˣ → ℝ) (β t : ℝ) (f : (ZMod q)ˣ → ℂ) (g : (ZMod r)ˣ → ℂ) :
    (Fintype.card (ZMod (q * r))ˣ : ℂ)⁻¹ *
      (∑ a, (pageMultiplier χ β t (crtSplitUnitEquiv q r h a).1 : ℂ) *
        f (crtSplitUnitEquiv q r h a).1 * g (crtSplitUnitEquiv q r h a).2) =
      ((Fintype.card (ZMod q)ˣ : ℂ)⁻¹ * ∑ b, (pageMultiplier χ β t b : ℂ) * f b) *
        ((Fintype.card (ZMod r)ˣ : ℂ)⁻¹ * ∑ c, g c) :=
  retained_page_average (crtSplitUnitEquiv q r h) χ β t f g

end Ostmann

end OAI
