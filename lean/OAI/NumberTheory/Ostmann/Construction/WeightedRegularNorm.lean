import OAI.NumberTheory.Ostmann.Construction.RegularResidueNorm
import OAI.NumberTheory.Ostmann.Construction.PrimeCellPriors

namespace OAI

/-! # The regular-transform norm under the actual prime sampling law -/

namespace Ostmann

open scoped BigOperators
open MeasureTheory

theorem weightedPageIntegral_le (φ χ β : ℝ) (hφ : 0 ≤ φ)
    (hχ : |χ| ≤ 1) (hβ : β ≤ 1) {s t : ℝ} (hs : 0 < s)
    (w : ℝ → ℝ) (hwc : ContinuousOn w (Set.Icc s t))
    (hw : ∀ y ∈ Set.Ioc s t, 0 ≤ w y) :
    (∫ y in Set.Ioc s t, w y * primeLogDensity φ χ β y) ≤
      (2 / φ) * ∫ y in Set.Ioc s t, w y / y := by
  have hc := continuousOn_primeLogDensity φ χ β (t := t) hs
  have hc' : ContinuousOn (fun y => (2 / φ) * (w y / y)) (Set.Icc s t) := by
    apply ContinuousOn.const_mul
    exact hwc.div continuousOn_id (fun y hy => ne_of_gt (hs.trans_le hy.1))
  have hf : IntegrableOn (fun y => w y * primeLogDensity φ χ β y) (Set.Ioc s t) :=
    (hwc.mul hc).integrableOn_Icc.mono_set Set.Ioc_subset_Icc_self
  have hg : IntegrableOn (fun y => (2 / φ) * (w y / y)) (Set.Ioc s t) :=
    hc'.integrableOn_Icc.mono_set Set.Ioc_subset_Icc_self
  rw [← integral_const_mul]
  apply setIntegral_mono_on hf hg measurableSet_Ioc
  intro y hy
  have hy0 := hs.trans hy.1
  calc
    _ ≤ w y * (2 / (φ * y)) := mul_le_mul_of_nonneg_left
      (primeLogDensity_bounds φ χ β hφ hχ hβ hy0.le).2 (hw y hy)
    _ = _ := by ring

/-- The exact CRT test mass turns per-residue prime progression errors
into an averaged regular-transform bound. The prime sampling weights and
the retained exceptional term are both explicit in this statement. -/
theorem PublishedProgressionInput.actual_regular_prime_norm_le
    (P : PublishedProgressionInput) {I : Type*} [Fintype I] [DecidableEq I]
    (p : I → ℕ) [∀ i, Fact (p i).Prime] [NeZero (∏ i, p i)]
    (hc : Pairwise (fun i j => (p i).Coprime (p j)))
    (a : ∀ i, (ZMod (p i))ˣ) (g : ∀ i, ZMod (p i) → ℂ)
    (hg : ∀ i, g i 0 = 0) (henergy : ∀ i, (∑ x : ZMod (p i), ‖g i x‖ ^ 2) = p i)
    (Q : ℕ) (hQ : 2 ≤ Q) (hmod : (∏ i, p i) ≤ Q)
    {s t : ℝ} (hs : 1 ≤ s) (hst : s ≤ t) (hshort : t ≤ s + 1)
    (w : ℝ → ℝ) (hwc : ContinuousOn w (Set.Icc s t))
    (hw : ∀ y ∈ Set.Ioc s t, 0 ≤ w y)
    (w₀ η Z : ℝ) (hη : 0 ≤ η) (hZ : 0 ≤ Z)
    (hvar : ∀ y ∈ Set.Ioc s t, |w y - w₀| ≤ η) :
    (∑ u : (ZMod (∏ i, p i))ˣ,
      (Z * weightedReciprocalPrimeInterval (∏ i, p i) (u : ZMod (∏ i, p i)).val s t w) *
        regularResidueTest p hc a g u) ≤
      (2 * (Z * ∫ y in Set.Ioc s t, w y / y) / Fintype.card (ZMod (∏ i, p i))ˣ +
        Z * ((|w₀| + η) *
          (18 * P.errorConstant * Real.exp (-P.decay * Real.sqrt s) +
            Real.exp (-P.kappa * s / Real.log (4 * (Q : ℝ)))) + 4 * η)) * (∏ i, p i : ℕ) := by
  let q := ∏ i, p i
  let R := Z * ∫ y in Set.Ioc s t, w y / y
  let E := 18 * P.errorConstant * Real.exp (-P.decay * Real.sqrt s) +
    Real.exp (-P.kappa * s / Real.log (4 * (Q : ℝ)))
  let δ := Z * ((|w₀| + η) * E + 4 * η)
  let μ : (ZMod q)ˣ → ℝ := fun u =>
    Z * weightedReciprocalPrimeInterval q (u : ZMod q).val s t w
  let ν : (ZMod q)ˣ → ℝ := fun u => Z * ∫ y in Set.Ioc s t,
    w y * primeLogDensity (Nat.totient q)
      (pageCoefficient (pageAtModulus q (selectedPageZero P Q)) (u : ZMod q).val)
      (pageBeta (pageAtModulus q (selectedPageZero P Q))) y
  have hq : 1 ≤ q := Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)
  have hdist (u : (ZMod q)ˣ) : |μ u - ν u| ≤ δ := by
    dsimp [μ, ν, δ]
    rw [← mul_sub, abs_mul, abs_of_nonneg hZ]
    apply mul_le_mul_of_nonneg_left _ hZ
    apply weighted_prime_log_interval_error q (u : ZMod q).val _ _ _
      (by exact_mod_cast Nat.totient_pos.mpr (by omega : 0 < q))
      (pageCoefficient_abs_le_one _ _) (pageBeta_le_one _)
      hs hst hshort w hwc w₀ η E hη hvar
    exact P.uniform_log_interval hQ hq hmod (ZMod.val_coe_unit_coprime u) hs hst hshort
  have hν (u : (ZMod q)ˣ) : ν u ≤ 2 * R / Fintype.card (ZMod q)ˣ := by
    dsimp [ν, R]
    rw [ZMod.card_units_eq_totient]
    have h := weightedPageIntegral_le (Nat.totient q)
      (pageCoefficient (pageAtModulus q (selectedPageZero P Q)) (u : ZMod q).val)
      (pageBeta (pageAtModulus q (selectedPageZero P Q))) (Nat.cast_nonneg _)
      (pageCoefficient_abs_le_one _ _) (pageBeta_le_one _)
      (lt_of_lt_of_le zero_lt_one hs) w hwc hw
    apply (mul_le_mul_of_nonneg_left h hZ).trans_eq
    ring
  exact regular_prime_residue_norm_le p hc a g hg henergy μ ν δ R hdist hν

end Ostmann

end OAI
