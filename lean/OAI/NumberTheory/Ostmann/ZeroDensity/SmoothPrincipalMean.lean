import OAI.NumberTheory.Ostmann.ZeroDensity.SmoothNonprincipalDecay

namespace OAI

/-! # The principal term of the smooth character estimate

Published input: the conductor-one case of Montgomery–Vaughan (2007),
Corollary 11.20, equations (11.32)/(11.34), p.381, with the usual smooth
partial summation. This is the classical prime number theorem with its
zero-free-region error, specialized to our single fixed compactly supported
smooth function. It makes no assertion about a growing character family.
-/
namespace Ostmann
open Filter MeasureTheory
open scoped Classical BigOperators

noncomputable def smoothPrincipalMain (X : ℝ) : ℂ :=
  ((X * ∫ t : ℝ, primeMeanTest t : ℝ) : ℂ)

noncomputable def smoothPrincipalError (X : ℝ) : ℝ :=
  ‖smoothMangoldtMean 1 1 X - smoothPrincipalMain X‖

/-- The fixed-test, conductor-one consequence of the classical PNT. -/
def PublishedSmoothPrincipalPNT : Prop :=
  ∃ C c : ℝ, 0 < C ∧ 0 < c ∧ ∀ X : ℝ, 2 ≤ X →
    smoothPrincipalError X ≤ C * X * Real.exp (-c * Real.sqrt (Real.log X))

theorem smooth_principal_decay (hPNT : PublishedSmoothPrincipalPNT) (D : ℝ) :
    ∀ᶠ L : ℝ in atTop, smoothPrincipalError (Real.exp (Real.exp L)) ≤
      Real.exp (Real.exp L) * Real.exp (-D * L) := by
  obtain ⟨C, c, _, hc, hPNT⟩ := hPNT
  have hsmall := ((isLittleO_pow_exp_pos_mul_atTop 1
    (show (0 : ℝ) < 1 / 2 by norm_num)).const_mul_left |D + 1|).bound hc
  filter_upwards [hsmall, Real.tendsto_exp_atTop.eventually_ge_atTop C,
    eventually_ge_atTop (1 : ℝ)] with L hs hC hL
  have hL0 : 0 ≤ L := by linarith
  have hX : 2 ≤ Real.exp (Real.exp L) := by
    have hh := Real.add_one_le_exp (Real.exp L)
    have hh' := Real.one_le_exp hL0
    linarith
  have hs' : |D + 1| * L ≤ c * Real.exp (L / 2) := by
    simpa only [pow_one, Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (abs_nonneg _) hL0),
      abs_of_pos (Real.exp_pos _), show (1 / 2 : ℝ) * L = L / 2 by ring] using hs
  have hr : C * Real.exp (-c * Real.sqrt (Real.log (Real.exp (Real.exp L)))) ≤
      Real.exp (-D * L) := by
    rw [Real.log_exp, ← Real.exp_half]
    calc
      _ ≤ Real.exp L * Real.exp (-c * Real.exp (L / 2)) :=
        mul_le_mul_of_nonneg_right hC (Real.exp_nonneg _)
      _ = Real.exp (L - c * Real.exp (L / 2)) := by rw [← Real.exp_add]; congr 1; ring
      _ ≤ _ := Real.exp_le_exp.mpr (by
        have hh := mul_le_mul_of_nonneg_right (le_abs_self (D + 1)) hL0
        linarith)
  calc
    _ ≤ C * Real.exp (Real.exp L) *
        Real.exp (-c * Real.sqrt (Real.log (Real.exp (Real.exp L)))) := hPNT _ hX
    _ = Real.exp (Real.exp L) *
        (C * Real.exp (-c * Real.sqrt (Real.log (Real.exp (Real.exp L))))) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hr (Real.exp_nonneg _)

/-- Lemma 5.3, including the conductor-one term. -/
theorem smooth_primitive_family_decay (Z : ∀ χ, ComplexZeroEnumeration χ)
    (hD : PublishedComplexZeroDensity Z) (hR : PublishedComplexZeroRegion Z)
    (P : PublishedSmoothExplicitFormula Z) (hPNT : PublishedSmoothPrincipalPNT)
    (a D : ℝ) (ha : 0 < a) :
    ∀ᶠ L : ℝ in atTop, ∀ Q : ℕ, 101 ≤ Q →
      L ^ 2 ≤ Real.log Q → Real.log Q ≤ a * L * Real.exp ((9 / 10 : ℝ) * L) →
      ∃ exception : Option PrimitiveComplexCharacter,
      ∀ F : Finset PrimitiveComplexCharacter,
        (∀ χ ∈ F, χ.modulus ≤ Q) → (∀ χ ∈ F, some χ ≠ exception) →
        smoothPrincipalError (Real.exp (Real.exp L)) +
          (∑ χ ∈ F, ‖smoothMangoldtMean χ.modulus χ.character (Real.exp (Real.exp L))‖) ≤
          Real.exp (Real.exp L) * Real.exp (-D * L) := by
  filter_upwards [smooth_nonprincipal_decay Z hD hR P a (D + 1) ha,
    smooth_principal_decay hPNT (D + 1), eventually_ge_atTop (1 : ℝ)] with L hn hp hL
  intro Q hQ hl hu
  obtain ⟨exception, hn⟩ := hn Q hQ hl hu
  refine ⟨exception, ?_⟩
  intro F hF he
  have htwo : 2 ≤ Real.exp L := by linarith [Real.add_one_le_exp L]
  calc
    _ ≤ Real.exp (Real.exp L) * (2 * Real.exp (-(D + 1) * L)) := by
      linarith [hn F hF he]
    _ ≤ Real.exp (Real.exp L) * (Real.exp L * Real.exp (-(D + 1) * L)) := by gcongr
    _ = _ := by rw [← Real.exp_add]; congr 2; ring

end Ostmann

end OAI
