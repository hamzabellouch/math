import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.ContactHeightBisection

namespace OAI

/-! Rational contact vertices approximate the same exact height witness as
the deterministic height solve. This estimate preserves separation margins
when the requested precision is increased. -/

noncomputable section
open scoped BigOperators
namespace ContinuumCoulomb.ContactHeightEvaluation

def stepX (e : Environment) (h : ℚ) (k : ℕ) : ℚ :=
  if k = 2 ∨ k = 3 ∨ k = 5 ∨ k = 6 then rootSample e h k else lengthAt e k

def stepY (h : ℚ) (k : ℕ) : ℚ :=
  if k = 2 ∨ k = 3 then h else if k = 5 ∨ k = 6 then -h else 0

def vertex (e : Environment) (k : ℕ) : ℚ × ℚ :=
  (∑ j ∈ Finset.range k, stepX e (scheduledValue e) j,
    ∑ j ∈ Finset.range k, stepY (scheduledValue e) j)

def vertexPoint (e : Environment) (k : ℕ) : ContactPoint :=
  contactPoint (vertex e k).1 (vertex e k).2

theorem forward_lipschitz {length h h' : ℝ}
    (hl : 99 / 100 ≤ length) (hl' : length ≤ 101 / 100)
    (hh : h ∈ Set.Icc (2 / 5) (3 / 4)) (hh' : h' ∈ Set.Icc (2 / 5) (3 / 4)) :
    |adjustedContactForward length h - adjustedContactForward length h'| ≤ 2 * |h - h'| := by
  rcases le_total h h' with hle | hle
  · obtain ⟨hlo, hhi⟩ := adjustedContactForward_slope hl hl' hh.1 hle hh'.2
    have hs : 0 ≤ adjustedContactForward length h - adjustedContactForward length h' := by linarith
    rw [abs_of_nonneg hs, abs_of_nonpos (sub_nonpos.mpr hle)]
    linarith
  · obtain ⟨hlo, hhi⟩ := adjustedContactForward_slope hl hl' hh'.1 hle hh.2
    have hs : adjustedContactForward length h - adjustedContactForward length h' ≤ 0 := by linarith
    rw [abs_of_nonpos hs, abs_of_nonneg (sub_nonneg.mpr hle)]
    linarith

theorem stepX_error (e : Environment) (h₀ : ℝ)
    (hl : ∀ k < 9, 1 - contactLengthTolerance ≤ (lengthAt e k : ℝ))
    (hl' : ∀ k < 9, (lengthAt e k : ℝ) ≤ 1 + contactLengthTolerance)
    (hh₀ : h₀ ∈ Set.Icc (2 / 5) (3 / 4))
    (he : |(scheduledValue e : ℝ) - h₀| ≤ ((e.1 : ℝ) + 1)⁻¹)
    {k : ℕ} (hk : k < 9) :
    |(stepX e (scheduledValue e) k : ℝ) -
      adjustedContactStepX (fun j => (lengthAt e j : ℝ)) h₀ k| ≤
        3 * ((e.1 : ℝ) + 1)⁻¹ := by
  by_cases hs : k = 2 ∨ k = 3 ∨ k = 5 ∨ k = 6
  · have hh := bisect_mem (refinedEnvironment e) (iterations e)
    have hlower : (99 / 100 : ℝ) ≤ lengthAt e k := by
      have := hl k hk
      norm_num [contactLengthTolerance] at this ⊢
      linarith
    have hupper : (lengthAt e k : ℝ) ≤ 101 / 100 := by
      have := hl' k hk
      norm_num [contactLengthTolerance] at this ⊢
      linarith
    have hsample := rootSample_error e (scheduledValue e) k (hl k hk) hh
    have hforward := forward_lipschitz hlower hupper hh hh₀
    have hdyadic : (2 : ℝ)⁻¹ ^ CalibratedEvaluation.rootPrecision e.1 ≤
        ((e.1 : ℝ) + 1)⁻¹ := (CalibratedEvaluation.root_budget e.1).trans (by
      apply inv_anti₀ (by positivity)
      nlinarith [show (0 : ℝ) ≤ e.1 from Nat.cast_nonneg e.1])
    have h := (abs_sub_le (rootSample e (scheduledValue e) k : ℝ)
      (adjustedContactForward (lengthAt e k) (scheduledValue e))
      (adjustedContactForward (lengthAt e k) h₀)).trans
        (add_le_add (hsample.trans hdyadic) (hforward.trans (mul_le_mul_of_nonneg_left he (by norm_num))))
    have h' : |(rootSample e (scheduledValue e) k : ℝ) -
        adjustedContactForward (lengthAt e k) h₀| ≤ 3 * ((e.1 : ℝ) + 1)⁻¹ := by
      calc
        _ ≤ ((e.1 : ℝ) + 1)⁻¹ + 2 * ((e.1 : ℝ) + 1)⁻¹ := h
        _ = _ := by ring
    simpa only [stepX, adjustedContactStepX, ite_eq_left hs] using h'
  · simp only [stepX, adjustedContactStepX, ite_eq_right hs, sub_self, abs_zero]
    positivity

theorem stepY_error (e : Environment) (h₀ : ℝ)
    (he : |(scheduledValue e : ℝ) - h₀| ≤ ((e.1 : ℝ) + 1)⁻¹) (k : ℕ) :
    |(stepY (scheduledValue e) k : ℝ) - adjustedContactStepY h₀ k| ≤
      ((e.1 : ℝ) + 1)⁻¹ := by
  by_cases h₁ : k = 2 ∨ k = 3
  · simpa only [stepY, adjustedContactStepY, ite_eq_left h₁] using he
  · by_cases h₂ : k = 5 ∨ k = 6
    · simpa only [stepY, adjustedContactStepY, ite_eq_right h₁, ite_eq_left h₂,
        Rat.cast_neg, neg_sub_neg, abs_sub_comm] using he
    · simp only [stepY, adjustedContactStepY, ite_eq_right h₁, ite_eq_right h₂, Rat.cast_zero,
        sub_zero, abs_zero]
      positivity

private theorem contactPoint_dist_le_abs (x y x' y' : ℝ) :
    dist (contactPoint x y) (contactPoint x' y') ≤ |x - x'| + |y - y'| := by
  have hsq := contactPoint_dist_sq x y x' y'
  nlinarith [sq_abs (x - x'), sq_abs (y - y'),
    mul_nonneg (abs_nonneg (x - x')) (abs_nonneg (y - y')),
    show 0 ≤ dist (contactPoint x y) (contactPoint x' y') from dist_nonneg,
    abs_nonneg (x - x'), abs_nonneg (y - y')]

theorem vertex_error (e : Environment) (h₀ : ℝ)
    (hl : ∀ k < 9, 1 - contactLengthTolerance ≤ (lengthAt e k : ℝ))
    (hl' : ∀ k < 9, (lengthAt e k : ℝ) ≤ 1 + contactLengthTolerance)
    (hh₀ : h₀ ∈ Set.Icc (2 / 5) (3 / 4))
    (hroot : adjustedContactSpan (fun k => (lengthAt e k : ℝ)) h₀ = (e.2.2 : ℝ))
    {k : ℕ} (hk : k ≤ 9) :
    dist (vertexPoint e k) (adjustedContactVertex (fun j => (lengthAt e j : ℝ)) h₀ k) ≤
      36 * ((e.1 : ℝ) + 1)⁻¹ := by
  have he := scheduled_height_error e h₀ hl hl' hh₀ hroot
  have hx : |(∑ j ∈ Finset.range k, (stepX e (scheduledValue e) j : ℝ)) -
      ∑ j ∈ Finset.range k, adjustedContactStepX (fun j => (lengthAt e j : ℝ)) h₀ j| ≤
        (k : ℝ) * (3 * ((e.1 : ℝ) + 1)⁻¹) := by
    rw [← Finset.sum_sub_distrib]
    apply (Finset.abs_sum_le_sum_abs _ _).trans
    calc
      _ ≤ ∑ _j ∈ Finset.range k, 3 * ((e.1 : ℝ) + 1)⁻¹ := by
        apply Finset.sum_le_sum
        intro j hj
        exact stepX_error e h₀ hl hl' hh₀ he (lt_of_lt_of_le (Finset.mem_range.mp hj) hk)
      _ = _ := by simp
  have hy : |(∑ j ∈ Finset.range k, (stepY (scheduledValue e) j : ℝ)) -
      ∑ j ∈ Finset.range k, adjustedContactStepY h₀ j| ≤
        (k : ℝ) * ((e.1 : ℝ) + 1)⁻¹ := by
    rw [← Finset.sum_sub_distrib]
    apply (Finset.abs_sum_le_sum_abs _ _).trans
    calc
      _ ≤ ∑ _j ∈ Finset.range k, ((e.1 : ℝ) + 1)⁻¹ := by
        exact Finset.sum_le_sum (fun j _ => stepY_error e h₀ he j)
      _ = _ := by simp
  have hd := contactPoint_dist_le_abs
    (∑ j ∈ Finset.range k, (stepX e (scheduledValue e) j : ℝ))
    (∑ j ∈ Finset.range k, (stepY (scheduledValue e) j : ℝ))
    (∑ j ∈ Finset.range k, adjustedContactStepX (fun j => (lengthAt e j : ℝ)) h₀ j)
    (∑ j ∈ Finset.range k, adjustedContactStepY h₀ j)
  have hk' : (k : ℝ) ≤ 9 := by exact_mod_cast hk
  have hb : (k : ℝ) * (3 * ((e.1 : ℝ) + 1)⁻¹) + (k : ℝ) * ((e.1 : ℝ) + 1)⁻¹ ≤
      36 * ((e.1 : ℝ) + 1)⁻¹ := by
    nlinarith [mul_le_mul_of_nonneg_right hk' (inv_nonneg.mpr
      (show (0 : ℝ) ≤ e.1 + 1 by positivity))]
  simpa only [vertexPoint, vertex, adjustedContactVertex, Rat.cast_sum] using
    hd.trans ((add_le_add hx hy).trans hb)

end ContinuumCoulomb.ContactHeightEvaluation

end

end OAI
