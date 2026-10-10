import OAI.MathematicalPhysics.Boltzmann.Approximation.PositiveSourceFormula
import OAI.MathematicalPhysics.Boltzmann.Branching.MomentAverageBound
import OAI.MathematicalPhysics.Boltzmann.Compactness.WeakTimeBalance

namespace OAI

section

/-! # Recovering the half-Gaussian moment from bounded velocity weights -/

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace BoltzmannNonuniqueness.VelocityMoment

def truncatedWeight (n : ℕ) (v : Velocity) : ℝ := min (weight v) (n : ℝ)

theorem truncatedWeight_measurable (n : ℕ) : Measurable (truncatedWeight n) := by
  unfold truncatedWeight weight
  fun_prop

theorem truncatedWeight_nonneg (n : ℕ) (v : Velocity) : 0 ≤ truncatedWeight n v :=
  le_min (weight_pos v).le (Nat.cast_nonneg n)

theorem truncatedWeight_abs_le (n : ℕ) (v : Velocity) : |truncatedWeight n v| ≤ n := by
  rw [abs_of_nonneg (truncatedWeight_nonneg n v)]
  exact min_le_right _ _

theorem truncatedMoment_integrable {f : Velocity → ℝ} (hf : Integrable f) (n : ℕ) :
    Integrable (fun v => truncatedWeight n v*f v) :=
  hf.bdd_mul (truncatedWeight_measurable n).aestronglyMeasurable
    (ae_of_all _ (truncatedWeight_abs_le n))

theorem truncatedMoment_le {f : Velocity → ℝ} {M : ℝ}
    (hfm : Measurable f) (hf : ∀ v, 0 ≤ f v) (hM : 0 ≤ M)
    (hb : moment f ≤ ENNReal.ofReal M) (n : ℕ) :
    (∫ v, truncatedWeight n v*f v) ≤ M := by
  have hi := truncatedMoment_integrable (integrable_of_moment_bound hfm hf hb) n
  apply (ENNReal.ofReal_le_ofReal_iff hM).mp
  rw [ofReal_integral_eq_lintegral_ofReal hi
    (ae_of_all _ (fun v => mul_nonneg (truncatedWeight_nonneg n v) (hf v)))]
  apply le_trans (lintegral_mono (fun v => ENNReal.ofReal_le_ofReal
    (mul_le_mul_of_nonneg_right (min_le_left _ _) (hf v)))) hb

theorem moment_le_of_truncated {f : Velocity → ℝ} {M : ℝ}
    (hfm : Measurable f) (hfi : Integrable f) (hf : ∀ v, 0 ≤ f v)
    (hb : ∀ n, (∫ v, truncatedWeight n v*f v) ≤ M) :
    moment f ≤ ENNReal.ofReal M := by
  let u : ℕ → Velocity → ℝ≥0∞ := fun n v => ENNReal.ofReal (truncatedWeight n v*f v)
  have hm n : Measurable (u n) := ((truncatedWeight_measurable n).mul hfm).ennreal_ofReal
  have hmono : Monotone u := by
    intro i j hij v
    exact ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right
      (min_le_min_left _ (Nat.cast_le.mpr hij)) (hf v))
  have he v : (⨆ n, u n v) = ENNReal.ofReal (weight v*f v) := by
    apply le_antisymm
    · exact iSup_le (fun n => ENNReal.ofReal_le_ofReal
        (mul_le_mul_of_nonneg_right (min_le_left _ _) (hf v)))
    · obtain ⟨n,hn⟩ := exists_nat_ge (weight v)
      have hu : u n v = ENNReal.ofReal (weight v*f v) := by
        simp only [u,truncatedWeight,min_eq_left hn]
      exact hu ▸ le_iSup (fun n => u n v) n
  change (∫⁻ v, ENNReal.ofReal (weight v*f v)) ≤ _
  simp_rw [← he]
  rw [lintegral_iSup hm hmono]
  apply iSup_le
  intro n
  rw [← ofReal_integral_eq_lintegral_ofReal (truncatedMoment_integrable hfi n)
    (ae_of_all _ (fun v => mul_nonneg (truncatedWeight_nonneg n v) (hf v)))]
  exact ENNReal.ofReal_le_ofReal (hb n)

end BoltzmannNonuniqueness.VelocityMoment

end

end

section

/-! # Bounded exponential weights on a time slab -/

noncomputable section

open MeasureTheory Set

namespace BoltzmannNonuniqueness.WeakTime

def slabExponential (a b C : ℝ) : ℝ → ℝ :=
  (Ioo a b).indicator (fun t => Real.exp (C*t))

theorem slabExponential_measurable (a b C : ℝ) : Measurable (slabExponential a b C) :=
  (by fun_prop : Measurable (fun t : ℝ => Real.exp (C*t))).indicator measurableSet_Ioo

theorem slabExponential_nonneg (a b C t : ℝ) : 0 ≤ slabExponential a b C t :=
  indicator_nonneg (fun _ _ => (Real.exp_pos _).le) _

theorem slabExponential_bound (a b : ℝ) {C : ℝ} (hC : 0 ≤ C) (t : ℝ) :
    |slabExponential a b C t| ≤ Real.exp (C*b) := by
  by_cases ht : t ∈ Ioo a b
  · rw [slabExponential,indicator_of_mem ht,abs_of_pos (Real.exp_pos _)]
    exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left ht.2.le hC)
  · rw [slabExponential,indicator_of_notMem ht,abs_zero]
    exact (Real.exp_pos _).le

theorem slabExponential_test {a b C : ℝ} {ψ : ℝ → ℝ}
    (hs : tsupport ψ ⊆ Ioo a b) (t : ℝ) :
    Real.exp (C*t)*ψ t = ψ t*slabExponential a b C t := by
  by_cases ht : t ∈ Ioo a b
  · rw [slabExponential,indicator_of_mem ht,mul_comm]
  · have hz : ψ t = 0 := image_eq_zero_of_notMem_tsupport (fun h => ht (hs h))
    rw [hz,mul_zero,zero_mul]

theorem slabExponential_test_derivative {a b C : ℝ} {ψ : ℝ → ℝ}
    (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hs : tsupport ψ ⊆ Ioo a b) (t : ℝ) :
    deriv (fun r => Real.exp (C*r)*ψ r) t =
      deriv ψ t*slabExponential a b C t+C*(ψ t*slabExponential a b C t) := by
  have hd := (((hasDerivAt_id t).const_mul C).exp.mul
    (hψ.differentiable (by simp) t).hasDerivAt).deriv
  change deriv (fun r => Real.exp (C*r)*ψ r) t =
    Real.exp (C*t)*(C*1)*ψ t+Real.exp (C*t)*deriv ψ t at hd
  rw [hd]
  have h₁ := slabExponential_test hs (C := C) t
  have h₂ := slabExponential_test (tsupport_deriv_subset.trans hs) (C := C) t
  nlinarith only [congrArg (fun x : ℝ => C*x) h₁,h₂]

end BoltzmannNonuniqueness.WeakTime

end

end

end OAI
