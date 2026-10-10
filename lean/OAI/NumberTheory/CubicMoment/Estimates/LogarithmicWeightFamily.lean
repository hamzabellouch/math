import OAI.NumberTheory.CubicMoment.Estimates.UniformWeightMultiplier

namespace OAI

/-! A polynomial logarithmic derivative cost can be normalized by any
fixed positive power of the outer length. This gives a uniform smooth
family without discarding the original, varying test functions. -/
noncomputable section
open Set
open scoped ContDiff
namespace CubicFirstMoment

lemma log_power_normalization_bound (A : ℕ) {s : ℝ} (hs : 0 < s) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ Y : ℝ, 1 ≤ Y → Y^(-s)*(1+Real.log Y)^A ≤ K := by
  let d := s/((A:ℝ)+1)
  have hd : 0 < d := by dsimp [d]; positivity
  refine ⟨(1+1/d)^A,by positivity,?_⟩
  intro Y hY
  have hYp : 0 < Y := zero_lt_one.trans_le hY
  have hl : 1+Real.log Y ≤ (1+1/d)*Y^d := by
    have hlog := Real.log_le_rpow_div hYp.le hd
    have hone := Real.one_le_rpow hY hd.le
    calc
      _ ≤ Y^d+Y^d/d := add_le_add hone hlog
      _ = _ := by ring
  have hexp : d*(A:ℝ) ≤ s := by
    dsimp [d]
    rw [div_mul_eq_mul_div]
    apply (div_le_iff₀ (by positivity : (0:ℝ) < (A:ℝ)+1)).mpr
    nlinarith
  calc
    _ ≤ Y^(-s)*((1+1/d)*Y^d)^A := mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (by linarith [Real.log_nonneg hY]) hl A) (Real.rpow_nonneg hYp.le _)
    _ = (1+1/d)^A*Y^(-s+d*(A:ℝ)) := by
      rw [mul_pow,← Real.rpow_natCast (Y^d) A,← Real.rpow_mul hYp.le,Real.rpow_add hYp]
      ring
    _ ≤ (1+1/d)^A*Y^(0:ℝ) := mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hY (by linarith)) (by positivity)
    _ = _ := by rw [Real.rpow_zero,mul_one]

structure LogarithmicWeightFamily {γ : Type*} (Y : γ → ℝ) (W : γ → ℝ → ℂ) where
  length_one : ∀ i, 1 ≤ Y i
  compact : ∀ i, HasCompactSupport (W i)
  positive : ∀ i, tsupport (W i) ⊆ Ioi 0
  smooth : ∀ i, ContDiff ℝ ∞ (W i)
  radius : ℝ
  radius_nonneg : 0 ≤ radius
  support_bound : ∀ i u, u ∈ tsupport (fun v => W i (Real.exp (-v))) → |u| ≤ radius
  derivative_bound : ∀ n : ℕ, ∃ (C : ℝ) (A : ℕ), 0 ≤ C ∧ ∀ i u,
    ‖iteratedFDeriv ℝ n (fun v => W i (Real.exp (-v))) u‖ ≤ C*(1+Real.log (Y i))^A

def normalizedLogWeight {γ : Type*} (Y : γ → ℝ) (W : γ → ℝ → ℂ) (s : ℝ)
    (i : γ) (x : ℝ) : ℂ := (Y i^(-s):ℝ) • W i x

 def LogarithmicWeightFamily.normalize {γ : Type*} {Y : γ → ℝ} {W : γ → ℝ → ℂ}
    (h : LogarithmicWeightFamily Y W) {s : ℝ} (hs : 0 < s) :
    UniformLogWeights (normalizedLogWeight Y W s) := by
  have hsupp (i : γ) : Function.support (normalizedLogWeight Y W s i) ⊆ Function.support (W i) := by
    intro x hx
    by_contra hz
    have he : W i x = 0 := by simpa only [Function.mem_support,not_not] using hz
    exact hx (by simp [normalizedLogWeight,he])
  refine ⟨fun i => (h.compact i).mono (hsupp i),
    fun i => (closure_mono (hsupp i)).trans (h.positive i),
    fun i => (h.smooth i).const_smul _,h.radius,h.radius_nonneg,?_,?_⟩
  · intro i u hu
    apply h.support_bound i u
    exact closure_mono (fun x hx => by
      intro hz
      exact hx (by simp [normalizedLogWeight,hz])) hu
  · intro n
    obtain ⟨C,A,hC,hbound⟩ := h.derivative_bound n
    obtain ⟨K,hK,hKbound⟩ := log_power_normalization_bound A hs
    refine ⟨C*K,mul_nonneg hC hK,?_⟩
    intro i u
    have hw : ContDiff ℝ ∞ (fun v => W i (Real.exp (-v))) :=
      (h.smooth i).comp (by fun_prop)
    have hYp : 0 < Y i := zero_lt_one.trans_le (h.length_one i)
    change ‖iteratedFDeriv ℝ n (fun v => (Y i^(-s):ℝ) • W i (Real.exp (-v))) u‖ ≤ _
    rw [iteratedFDeriv_const_smul_apply' ((hw.of_le (by exact_mod_cast le_top)).contDiffAt),
      norm_smul,Real.norm_eq_abs,abs_of_nonneg (Real.rpow_nonneg hYp.le _)]
    calc
      _ ≤ Y i^(-s)*(C*(1+Real.log (Y i))^A) :=
        mul_le_mul_of_nonneg_left (hbound i u) (Real.rpow_nonneg hYp.le _)
      _ = C*(Y i^(-s)*(1+Real.log (Y i))^A) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (hKbound (Y i) (h.length_one i)) hC

end CubicFirstMoment

end

end OAI
