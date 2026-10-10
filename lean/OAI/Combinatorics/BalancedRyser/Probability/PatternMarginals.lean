import Mathlib

namespace OAI

open MeasureTheory
open scoped BigOperators ENNReal

namespace Balanced.PatternMarginals

theorem weighted_lintegral_le_of_marginal_bound
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    {X : κ → Type*} [∀ c, MeasurableSpace (X c)]
    (μ : ∀ c, Measure (X c)) [∀ c, IsProbabilityMeasure (μ c)]
    (K : Finset κ) (f Z : (∀ c, X c) → ℝ≥0∞) (C : ℝ≥0∞)
    (hf : Measurable f) (hZ : Measurable Z)
    (hdepends : ∀ x y, (∀ c ∈ K, x c = y c) → f x = f y)
    (hbound : ∀ x, lmarginal μ (Finset.univ \ K) Z x ≤ C) :
    (∫⁻ x, f x * Z x ∂Measure.pi μ) ≤ C * ∫⁻ x, f x ∂Measure.pi μ := by
  classical
  rw [← lintegral_const_mul C hf]
  apply lintegral_le_of_lmarginal_le (Finset.univ \ K) (hf.mul hZ)
    (measurable_const.mul hf)
  intro x
  have hfx (y : (c : ↥(Finset.univ \ K)) → X c) :
      f (Function.updateFinset x (Finset.univ \ K) y) = f x := by
    apply hdepends
    intro c hc
    simp [Function.updateFinset_def, hc]
  change (∫⁻ y, f (Function.updateFinset x (Finset.univ \ K) y) *
      Z (Function.updateFinset x (Finset.univ \ K) y)
        ∂Measure.pi (fun c : ↥(Finset.univ \ K) => μ c)) ≤
    ∫⁻ y, C * f (Function.updateFinset x (Finset.univ \ K) y)
      ∂Measure.pi (fun c : ↥(Finset.univ \ K) => μ c)
  simp_rw [hfx]
  have hZup : Measurable (fun y : (c : ↥(Finset.univ \ K)) → X c =>
      Z (Function.updateFinset x (Finset.univ \ K) y)) := hZ.comp measurable_updateFinset
  rw [lintegral_const_mul (f x) hZup]
  simpa only [lmarginal, lintegral_const, measure_univ, mul_one, mul_comm C] using
    mul_le_mul' (le_refl (f x)) (hbound x)

theorem lintegral_moment_le_pow_of_marginal_bound
    {κ A : Type*} [Fintype κ] [DecidableEq κ] [Fintype A]
    {X : κ → Type*} [∀ c, MeasurableSpace (X c)]
    (μ : ∀ c, Measure (X c)) [∀ c, IsProbabilityMeasure (μ c)]
    (I : A → (∀ c, X c) → ℝ≥0∞) (support : A → Finset κ)
    (r s : ℕ) (C : ℝ≥0∞)
    (hI : ∀ a, Measurable (I a))
    (hsupport : ∀ a, (support a).card ≤ r)
    (hdepends : ∀ a x y,
      (∀ c ∈ support a, x c = y c) → I a x = I a y)
    (hbound : ∀ K : Finset κ, K.card ≤ (s - 1) * r → ∀ x,
      lmarginal μ (Finset.univ \ K) (fun y => ∑ a, I a y) x ≤ C) :
    (∫⁻ x, (∑ a, I a x) ^ s ∂Measure.pi μ) ≤ C ^ s := by
  classical
  have hsum : Measurable (fun x => ∑ a, I a x) :=
    Finset.measurable_sum _ (fun a _ => hI a)
  have hprod (n : ℕ) (t : Fin n → A) : Measurable (fun x => ∏ j, I (t j) x) :=
    Finset.measurable_prod _ (fun j _ => hI (t j))
  have hexpand (n : ℕ) :
      (∫⁻ x, (∑ a, I a x) ^ n ∂Measure.pi μ) =
        ∑ t : Fin n → A, ∫⁻ x, ∏ j, I (t j) x ∂Measure.pi μ := by
    simp_rw [Fintype.sum_pow]
    exact lintegral_finsetSum _ (fun t _ => hprod n t)
  have htuple (n : ℕ) (hn : n < s) (t : Fin n → A) :
      (∫⁻ x, (∏ j, I (t j) x) * (∑ a, I a x) ∂Measure.pi μ) ≤
        C * ∫⁻ x, ∏ j, I (t j) x ∂Measure.pi μ := by
    let K : Finset κ := Finset.univ.biUnion (fun j => support (t j))
    have hK : K.card ≤ (s - 1) * r := by
      calc
        K.card ≤ ∑ j : Fin n, (support (t j)).card := Finset.card_biUnion_le
        _ ≤ ∑ _j : Fin n, r := Finset.sum_le_sum (fun j _ => hsupport (t j))
        _ = n * r := by simp
        _ ≤ (s - 1) * r := Nat.mul_le_mul_right r (by omega)
    apply weighted_lintegral_le_of_marginal_bound μ K
      (fun x => ∏ j, I (t j) x) (fun x => ∑ a, I a x) C (hprod n t) hsum
    · intro x y hxy
      apply Finset.prod_congr rfl
      intro j _
      apply hdepends (t j) x y
      intro c hc
      exact hxy c (Finset.mem_biUnion.mpr ⟨j, Finset.mem_univ j, hc⟩)
    · exact hbound K hK
  have hstep (n : ℕ) (hn : n < s) :
      (∫⁻ x, (∑ a, I a x) ^ (n + 1) ∂Measure.pi μ) ≤
        C * ∫⁻ x, (∑ a, I a x) ^ n ∂Measure.pi μ := by
    calc
      (∫⁻ x, (∑ a, I a x) ^ (n + 1) ∂Measure.pi μ) =
          ∑ t : Fin n → A,
            ∫⁻ x, (∏ j, I (t j) x) * (∑ a, I a x) ∂Measure.pi μ := by
        simp_rw [pow_succ, Fintype.sum_pow, Finset.sum_mul]
        exact lintegral_finsetSum _ (fun t _ => (hprod n t).mul hsum)
      _ ≤ ∑ t : Fin n → A, C * ∫⁻ x, ∏ j, I (t j) x ∂Measure.pi μ :=
        Finset.sum_le_sum (fun t _ => htuple n hn t)
      _ = C * ∫⁻ x, (∑ a, I a x) ^ n ∂Measure.pi μ := by
        rw [← Finset.mul_sum, hexpand]
  have hmoment : ∀ n ≤ s,
      (∫⁻ x, (∑ a, I a x) ^ n ∂Measure.pi μ) ≤ C ^ n := by
    intro n
    induction n with
    | zero =>
        intro _
        simp
    | succ n ih =>
        intro hn
        calc
          (∫⁻ x, (∑ a, I a x) ^ (n + 1) ∂Measure.pi μ) ≤
              C * ∫⁻ x, (∑ a, I a x) ^ n ∂Measure.pi μ := hstep n (by omega)
          _ ≤ C * C ^ n := mul_le_mul' le_rfl (ih (by omega))
          _ = C ^ (n + 1) := by rw [pow_succ, mul_comm]
  exact hmoment s le_rfl

theorem integral_moment_le_pow_of_marginal_bound
    {κ A : Type*} [Fintype κ] [DecidableEq κ] [Fintype A]
    {X : κ → Type*} [∀ c, MeasurableSpace (X c)]
    (μ : ∀ c, Measure (X c)) [∀ c, IsProbabilityMeasure (μ c)]
    (I : A → (∀ c, X c) → ℝ) (support : A → Finset κ)
    (r s : ℕ) (C : ℝ) (hC : 0 ≤ C)
    (hI : ∀ a, Measurable (I a)) (hnonneg : ∀ a x, 0 ≤ I a x)
    (hsupport : ∀ a, (support a).card ≤ r)
    (hdepends : ∀ a x y,
      (∀ c ∈ support a, x c = y c) → I a x = I a y)
    (hbound : ∀ K : Finset κ, K.card ≤ (s - 1) * r → ∀ x,
      lmarginal μ (Finset.univ \ K)
        (fun y => ENNReal.ofReal (∑ a, I a y)) x ≤ ENNReal.ofReal C) :
    (∫ x, (∑ a, I a x) ^ s ∂Measure.pi μ) ≤ C ^ s := by
  classical
  have hsum (x : ∀ c, X c) : 0 ≤ ∑ a, I a x :=
    Finset.sum_nonneg (fun a _ => hnonneg a x)
  have hsum_meas : Measurable (fun x => ∑ a, I a x) :=
    Finset.measurable_sum _ (fun a _ => hI a)
  have hsum_ofReal (x : ∀ c, X c) :
      (∑ a, ENNReal.ofReal (I a x)) = ENNReal.ofReal (∑ a, I a x) :=
    (ENNReal.ofReal_sum_of_nonneg (fun a _ => hnonneg a x)).symm
  have hE := lintegral_moment_le_pow_of_marginal_bound μ
    (fun a x => ENNReal.ofReal (I a x)) support r s (ENNReal.ofReal C)
    (fun a => (hI a).ennreal_ofReal) hsupport
    (by
      intro a x y hxy
      rw [hdepends a x y hxy])
    (by
      intro K hK x
      simpa only [hsum_ofReal] using hbound K hK x)
  simp_rw [hsum_ofReal] at hE
  have hreal := ENNReal.toReal_mono (ENNReal.pow_ne_top ENNReal.ofReal_ne_top) hE
  rw [integral_eq_lintegral_of_nonneg_ae
    (Filter.Eventually.of_forall (fun x => pow_nonneg (hsum x) s))
    (hsum_meas.pow_const s).aestronglyMeasurable]
  simp_rw [ENNReal.ofReal_pow (hsum _) s]
  simpa only [ENNReal.toReal_pow, ENNReal.toReal_ofReal hC] using hreal

theorem weighted_integral_le_of_marginal_bound
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    {X : κ → Type*} [∀ c, MeasurableSpace (X c)]
    (μ : ∀ c, Measure (X c)) [∀ c, IsProbabilityMeasure (μ c)]
    (K : Finset κ) (F Z : (∀ c, X c) → ℝ) (C : ℝ) (hC : 0 ≤ C)
    (hF : Measurable F) (hZ : Measurable Z)
    (hFn : ∀ x, 0 ≤ F x) (hZn : ∀ x, 0 ≤ Z x)
    (hFi : Integrable F (Measure.pi μ))
    (hdepends : ∀ x y, (∀ c ∈ K, x c = y c) → F x = F y)
    (hbound : ∀ x, lmarginal μ (Finset.univ \ K)
      (fun y => ENNReal.ofReal (Z y)) x ≤ ENNReal.ofReal C) :
    (∫ x, F x * Z x ∂Measure.pi μ) ≤ C * ∫ x, F x ∂Measure.pi μ := by
  have hE := weighted_lintegral_le_of_marginal_bound μ K
    (fun x => ENNReal.ofReal (F x)) (fun x => ENNReal.ofReal (Z x))
    (ENNReal.ofReal C) hF.ennreal_ofReal hZ.ennreal_ofReal
    (by intro x y hxy; rw [hdepends x y hxy]) hbound
  have hfinite : (∫⁻ x, ENNReal.ofReal (F x) ∂Measure.pi μ) ≠ ⊤ :=
    (lintegral_ofReal_ne_top_iff_integrable hF.aestronglyMeasurable
      (Filter.Eventually.of_forall hFn)).mpr hFi
  have hreal := ENNReal.toReal_mono
    (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hfinite) hE
  rw [integral_eq_lintegral_of_nonneg_ae
      (Filter.Eventually.of_forall (fun x => mul_nonneg (hFn x) (hZn x)))
      (hF.mul hZ).aestronglyMeasurable,
    integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall hFn)
      hF.aestronglyMeasurable]
  simp_rw [ENNReal.ofReal_mul (hFn _)]
  simpa only [ENNReal.toReal_mul, ENNReal.toReal_ofReal hC] using hreal

end Balanced.PatternMarginals

end OAI
