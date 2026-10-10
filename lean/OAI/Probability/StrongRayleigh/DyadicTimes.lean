import OAI.Probability.StrongRayleigh.BrownianKolmogorov

namespace OAI

universe u_1 u_2

noncomputable section

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal Topology

namespace Problem336AdditiveD139.BrownianConstruction

def dyadicTime (p : ℕ × ℕ) : ℝ≥0 := p.2 / (2 : ℝ≥0) ^ p.1

def rationalDyadicTime (p : ℕ × ℕ) : ℚ≥0 := p.2 / (2 : ℚ≥0) ^ p.1

@[simp] theorem coe_rationalDyadicTime (p : ℕ × ℕ) :
    (rationalDyadicTime p : ℝ≥0) = dyadicTime p := by
  simp [rationalDyadicTime, dyadicTime]

@[simp] theorem dyadicTime_parent (n k : ℕ) :
    dyadicTime (n + 1, 2 * k) = dyadicTime (n, k) := by
  simp only [dyadicTime, Nat.cast_mul, Nat.cast_ofNat, pow_succ]
  field_simp

@[simp] theorem rationalDyadicTime_parent (n k : ℕ) :
    rationalDyadicTime (n + 1, 2 * k) = rationalDyadicTime (n, k) := by
  simp only [rationalDyadicTime, Nat.cast_mul, Nat.cast_ofNat, pow_succ]
  field_simp

theorem tendsto_dyadicTime_floor (t : ℝ≥0) :
    Tendsto (fun n : ℕ => dyadicTime (n, ⌊(t : ℝ) * (2 : ℝ)^n⌋₊))
      atTop (𝓝 t) := by
  apply NNReal.tendsto_coe.mp
  simpa only [dyadicTime, NNReal.coe_div, NNReal.coe_natCast, NNReal.coe_pow,
    NNReal.coe_ofNat, Function.comp_def] using
    (tendsto_nat_floor_mul_div_atTop t.coe_nonneg).comp
      (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1 : ℝ) < 2))

theorem denseRange_dyadicTime : DenseRange dyadicTime := by
  intro t
  apply mem_closure_of_tendsto (tendsto_dyadicTime_floor t)
  exact Eventually.of_forall (fun n => ⟨(n, ⌊(t : ℝ) * (2 : ℝ)^n⌋₊), rfl⟩)

theorem dist_dyadicTime_succ (n k : ℕ) :
    dist (dyadicTime (n, k + 1)) (dyadicTime (n, k)) = (1 / 2 : ℝ)^n := by
  rw [NNReal.dist_eq]
  simp only [dyadicTime, NNReal.coe_div, NNReal.coe_natCast, NNReal.coe_pow,
    NNReal.coe_ofNat, Nat.cast_add, Nat.cast_one, NNReal.coe_add, NNReal.coe_one]
  have heq : ((k : ℝ) + 1) / 2^n - (k : ℝ) / 2^n = (1 / 2 : ℝ)^n := by
    rw [div_pow, one_pow]
    ring
  rw [heq, abs_of_nonneg (by positivity)]

theorem nndist_dyadicTime_succ (n k : ℕ) :
    nndist (dyadicTime (n, k + 1)) (dyadicTime (n, k)) = (1 / 2 : ℝ≥0)^n := by
  apply NNReal.coe_injective
  simpa only [coe_nndist, NNReal.coe_pow, NNReal.coe_div, NNReal.coe_one,
    NNReal.coe_ofNat] using dist_dyadicTime_succ n k

theorem dyadic_increment_fourth_moment {Ω : Type u_1} [MeasurableSpace Ω]
    {P : Measure Ω} {X : ℝ≥0 → Ω → ℝ}
    (hX : ∀ s t, HasLaw (X s - X t) (gaussianReal 0 (nndist s t)) P)
    (n k : ℕ) :
    (∫ ω, |X (dyadicTime (n, k + 1)) ω - X (dyadicTime (n, k)) ω|^4 ∂P) =
      3 * (1 / 4 : ℝ)^n := by
  have h := integral_abs_pow_four_of_hasLaw
    (hX (dyadicTime (n, k + 1)) (dyadicTime (n, k)))
  rw [nndist_dyadicTime_succ] at h
  convert! h using 1
  simp only [NNReal.coe_pow, NNReal.coe_div, NNReal.coe_one, NNReal.coe_ofNat]
  rw [← pow_mul, Nat.mul_comm n 2, pow_mul]
  norm_num

theorem rationalDyadic_increment_fourth_moment {Ω : Type u_2} [MeasurableSpace Ω]
    {P : Measure Ω} {X : ℚ≥0 → Ω → ℝ}
    (hX : ∀ s t, HasLaw (X s - X t)
      (gaussianReal 0 (nndist (s : ℝ≥0) (t : ℝ≥0))) P)
    (n k : ℕ) :
    (∫ ω, |X (rationalDyadicTime (n, k + 1)) ω -
      X (rationalDyadicTime (n, k)) ω|^4 ∂P) = 3 * (1 / 4 : ℝ)^n := by
  have h := integral_abs_pow_four_of_hasLaw
    (hX (rationalDyadicTime (n, k + 1)) (rationalDyadicTime (n, k)))
  rw [coe_rationalDyadicTime, coe_rationalDyadicTime, nndist_dyadicTime_succ] at h
  convert! h using 1
  simp only [NNReal.coe_pow, NNReal.coe_div, NNReal.coe_one, NNReal.coe_ofNat]
  rw [← pow_mul, Nat.mul_comm n 2, pow_mul]
  norm_num

end Problem336AdditiveD139.BrownianConstruction

end

end OAI
