import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.ContactHeightEvaluation
import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.CalibratedBisectionLocation

namespace OAI

/-! The height search uses fixed rational endpoints, its concrete evaluator,
and a linear unary precision schedule. The reference height is supplied by
the already proved contact intermediate-value theorem. -/

noncomputable section
namespace ContinuumCoulomb.ContactHeightEvaluation

def tolerance (e : Environment) : ℚ := 1 / ((e.1 : ℚ) + 1)

def argument (e : Environment) (n : ℕ) : BisectionProgram.Input Environment :=
  (n, (e, (tolerance e, ((2 / 5 : ℚ), (3 / 4 : ℚ)))))

def bisect (e : Environment) (n : ℕ) : ℚ :=
  BisectionProgram.approximate value (argument e n)

def refinedEnvironment (e : Environment) : Environment := (16 * (e.1 + 1), e.2)

def iterations (e : Environment) : ℕ := 64 * (e.1 + 1)

def scheduledValue (e : Environment) : ℚ := bisect (refinedEnvironment e) (iterations e)

theorem bisect_mem (e : Environment) (n : ℕ) :
    (bisect e n : ℝ) ∈ Set.Icc (2 / 5) (3 / 4) := by
  have hm := bisection_value_mem value e (tolerance e) (2 / 5) (3 / 4)
    (by norm_num) n
  have hm' : bisect e n ∈ Set.Icc (2 / 5 : ℚ) (3 / 4) := hm
  constructor
  · simpa only [Rat.cast_div, Rat.cast_ofNat] using (Rat.cast_le (K := ℝ)).mpr hm'.1
  · simpa only [Rat.cast_div, Rat.cast_ofNat] using (Rat.cast_le (K := ℝ)).mpr hm'.2

theorem endpoint_signs (e : Environment) (h₀ : ℝ)
    (hl : ∀ k < 9, 1 - contactLengthTolerance ≤ (lengthAt e k : ℝ))
    (hl' : ∀ k < 9, (lengthAt e k : ℝ) ≤ 1 + contactLengthTolerance)
    (hh₀ : h₀ ∈ Set.Icc (2 / 5) (3 / 4))
    (hroot : adjustedContactSpan (fun k => (lengthAt e k : ℝ)) h₀ = (e.2.2 : ℝ)) :
    0 ≤ residual e (2 / 5) ∧ residual e (3 / 4) ≤ 0 := by
  have ha := (adjustedContactSpan_broad_slope (by norm_num) hh₀.1 hh₀.2
    (fun k => (lengthAt e k : ℝ)) hl hl').1
  have hb := (adjustedContactSpan_broad_slope hh₀.1 hh₀.2 (by norm_num)
    (fun k => (lengthAt e k : ℝ)) hl hl').1
  rw [hroot] at ha hb
  constructor <;> unfold residual <;> linarith [hh₀.1, hh₀.2]

theorem bisect_residual (e : Environment)
    (hl : ∀ k < 9, 1 - contactLengthTolerance ≤ (lengthAt e k : ℝ))
    (hl' : ∀ k < 9, (lengthAt e k : ℝ) ≤ 1 + contactLengthTolerance)
    (ha : 0 ≤ residual e (2 / 5)) (hb : residual e (3 / 4) ≤ 0) (n : ℕ) :
    |residual e (bisect e n)| ≤ 2 * ((e.1 : ℝ) + 1)⁻¹ +
      8 * (((3 / 4 : ℝ) - 2 / 5) / 2 ^ n) := by
  have heval (q : ℚ) (hq : q ∈ Set.Icc (2 / 5 : ℚ) (3 / 4)) :
      |(value e q : ℝ) - residual e q| ≤ (tolerance e : ℝ) := by
    have hq' : (q : ℝ) ∈ Set.Icc (2 / 5) (3 / 4) := by
      constructor
      · simpa only [Rat.cast_div, Rat.cast_ofNat] using (Rat.cast_le (K := ℝ)).mpr hq.1
      · simpa only [Rat.cast_div, Rat.cast_ofNat] using (Rat.cast_le (K := ℝ)).mpr hq.2
    simpa only [tolerance, Rat.cast_div, Rat.cast_one, Rat.cast_add,
      Rat.cast_natCast, one_div, Rat.cast_inv] using approximation_error e q hl hq'
  have hLip (r : ℝ) (hr : r ∈ Set.Icc (2 / 5) (3 / 4))
      (s : ℝ) (hs : s ∈ Set.Icc (2 / 5) (3 / 4)) :
      |residual e r - residual e s| ≤ 8 * |r - s| := by
    simpa only [residual, sub_sub_sub_cancel_right] using
      adjustedContactSpan_broad_lipschitz hr hs (fun k => (lengthAt e k : ℝ)) hl hl'
  have ha' : 0 ≤ residual e ((2 / 5 : ℚ) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat] using ha
  have hb' : residual e ((3 / 4 : ℚ) : ℝ) ≤ 0 := by
    simpa only [Rat.cast_div, Rat.cast_ofNat] using hb
  have hLip' (r : ℝ) (hr : r ∈ Set.Icc ((2 / 5 : ℚ) : ℝ) ((3 / 4 : ℚ) : ℝ))
      (s : ℝ) (hs : s ∈ Set.Icc ((2 / 5 : ℚ) : ℝ) ((3 / 4 : ℚ) : ℝ)) :
      |residual e r - residual e s| ≤ 8 * |r - s| :=
    hLip r (by simpa only [Rat.cast_div, Rat.cast_ofNat] using hr)
      s (by simpa only [Rat.cast_div, Rat.cast_ofNat] using hs)
  have he := BisectionProgram.residual value e
    (show 0 ≤ tolerance e by unfold tolerance; positivity)
    (show (2 / 5 : ℚ) ≤ 3 / 4 by norm_num) ha' hb'
    (show (0 : ℝ) ≤ 8 by norm_num) heval hLip' n
  simpa only [bisect, argument, tolerance, Rat.cast_div, Rat.cast_one,
    Rat.cast_add, Rat.cast_natCast, Rat.cast_ofNat, one_div, Rat.cast_inv] using he

theorem scheduled_residual (e : Environment)
    (hl : ∀ k < 9, 1 - contactLengthTolerance ≤ (lengthAt e k : ℝ))
    (hl' : ∀ k < 9, (lengthAt e k : ℝ) ≤ 1 + contactLengthTolerance)
    (ha : 0 ≤ residual e (2 / 5)) (hb : residual e (3 / 4) ≤ 0) :
    |residual e (scheduledValue e)| ≤ (2 * ((e.1 : ℝ) + 1))⁻¹ := by
  have he := bisect_residual (refinedEnvironment e) hl hl' ha hb (iterations e)
  have he' : |residual e (scheduledValue e)| ≤
      2 * (16 * ((e.1 : ℝ) + 1) + 1)⁻¹ +
        8 * (((3 / 4 : ℝ) - 2 / 5) / 2 ^ iterations e) := by
    simpa only [scheduledValue, refinedEnvironment, residual, lengthAt, Nat.cast_mul,
      Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] using he
  have hS : (0 : ℝ) < (e.1 : ℝ) + 1 := by positivity
  have hn : (iterations e : ℝ) = 64 * ((e.1 : ℝ) + 1) := by
    simp only [iterations, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_add, Nat.cast_one]
  have hn0 : (0 : ℝ) < iterations e := by rw [hn]; positivity
  have hfirst : 2 * (16 * ((e.1 : ℝ) + 1) + 1)⁻¹ ≤
      (8 * ((e.1 : ℝ) + 1))⁻¹ := by
    apply (mul_inv_le_iff₀ (by positivity)).mpr
    apply (le_inv_mul_iff₀ (by positivity : (0 : ℝ) < 8 * ((e.1 : ℝ) + 1))).mpr
    linarith
  have hsecond : 8 * (((3 / 4 : ℝ) - 2 / 5) / 2 ^ iterations e) ≤
      (8 * ((e.1 : ℝ) + 1))⁻¹ := by
    calc
      _ ≤ 8 * (2 : ℝ)⁻¹ ^ iterations e := by
        rw [div_eq_mul_inv, inv_pow]
        gcongr
        norm_num
      _ ≤ 8 * ((iterations e : ℝ) + 1)⁻¹ :=
        mul_le_mul_of_nonneg_left (CoulombQuadratureSchedule.dyadic_le_inverse _) (by norm_num)
      _ ≤ 8 * (iterations e : ℝ)⁻¹ :=
        mul_le_mul_of_nonneg_left (inv_anti₀ hn0 (by linarith)) (by norm_num)
      _ = (8 * ((e.1 : ℝ) + 1))⁻¹ := by
        rw [hn]
        field_simp [ne_of_gt hS]
        ring
  apply he'.trans ((add_le_add hfirst hsecond).trans _)
  simp only [mul_inv_rev]
  norm_num
  nlinarith [inv_pos.mpr hS]

theorem scheduled_height_error (e : Environment) (h₀ : ℝ)
    (hl : ∀ k < 9, 1 - contactLengthTolerance ≤ (lengthAt e k : ℝ))
    (hl' : ∀ k < 9, (lengthAt e k : ℝ) ≤ 1 + contactLengthTolerance)
    (hh₀ : h₀ ∈ Set.Icc (2 / 5) (3 / 4))
    (hroot : adjustedContactSpan (fun k => (lengthAt e k : ℝ)) h₀ = (e.2.2 : ℝ)) :
    |(scheduledValue e : ℝ) - h₀| ≤ ((e.1 : ℝ) + 1)⁻¹ := by
  have hs := endpoint_signs e h₀ hl hl' hh₀ hroot
  have he := scheduled_residual e hl hl' hs.1 hs.2
  have hi := adjustedContactSpan_broad_inverse_error
    (bisect_mem (refinedEnvironment e) (iterations e)) hh₀
    (fun k => (lengthAt e k : ℝ)) hl hl' hroot
  have h := hi.trans (mul_le_mul_of_nonneg_left he (by norm_num : (0 : ℝ) ≤ 2))
  calc
    _ ≤ 2 * (2 * ((e.1 : ℝ) + 1))⁻¹ := h
    _ = _ := by field_simp

theorem exists_scheduled_height_error (e : Environment) {c : ℝ}
    (hc : 3 / 4 ≤ c) (hc' : c ≤ 7 / 8)
    (hl : ∀ k < 9, 1 - contactLengthTolerance ≤ (lengthAt e k : ℝ))
    (hl' : ∀ k < 9, (lengthAt e k : ℝ) ≤ 1 + contactLengthTolerance)
    (hspan : 5 + 4 * c - contactLengthTolerance ≤ (e.2.2 : ℝ))
    (hspan' : (e.2.2 : ℝ) ≤ 5 + 4 * c + contactLengthTolerance) :
    ∃ h₀ ∈ Set.Icc (contactHeightLow c) (contactHeightHigh c),
      adjustedContactSpan (fun k => (lengthAt e k : ℝ)) h₀ = (e.2.2 : ℝ) ∧
      |(scheduledValue e : ℝ) - h₀| ≤ ((e.1 : ℝ) + 1)⁻¹ := by
  obtain ⟨h₀, hh₀, hroot⟩ := adjustedContactSpan_exists hc hc'
    (fun k => (lengthAt e k : ℝ)) hl hl' hspan hspan'
  exact ⟨h₀, hh₀, hroot, scheduled_height_error e h₀ hl hl'
    (contactHeight_interval_bounds hc hc' hh₀) hroot⟩

end ContinuumCoulomb.ContactHeightEvaluation

end

end OAI
