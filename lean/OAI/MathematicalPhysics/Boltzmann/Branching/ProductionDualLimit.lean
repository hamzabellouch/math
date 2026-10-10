import OAI.MathematicalPhysics.Boltzmann.Compactness.EntropyIntegralBalance
import OAI.MathematicalPhysics.Boltzmann.Compactness.EntropyRegularizationLimit

namespace OAI

section

/-! # Bounded linear tests for the extended entropy production -/

noncomputable section

open MeasureTheory Filter
open scoped ENNReal Topology

namespace BoltzmannNonuniqueness

def productionDual (a b s : ℝ) : ℝ :=
  entropyDual b a s+entropyDual a b (-s)

theorem productionDual_linear (a b s : ℝ) :
    productionDual a b s = a*(s-Real.exp (-s)+1)+b*(-s-Real.exp s+1) := by
  dsimp [productionDual,entropyDual]
  ring

theorem productionDual_ofReal_le (a b s : ℝ) :
    ENNReal.ofReal (productionDual a b s) ≤ extendedEntropyProduction a b := by
  by_cases hz : a = 0 ∧ b = 0
  · rcases hz with ⟨rfl,rfl⟩
    simp [productionDual,entropyDual,extendedEntropyProduction]
  by_cases hp : 0 < a ∧ 0 < b
  · have h₁ := entropyDual_le hp.2 hp.1.le s
    have h₂ := entropyDual_le hp.1 hp.2.le (-s)
    have he : scalarRelativeEntropy b a+scalarRelativeEntropy a b =
        (a-b)*Real.log (a/b) := by
      rw [scalarRelativeEntropy_eq hp.2,scalarRelativeEntropy_eq hp.1,
        Real.log_div hp.1.ne' hp.2.ne',Real.log_div hp.2.ne' hp.1.ne']
      ring
    simp only [extendedEntropyProduction,ite_eq_right hz,ite_eq_left hp]
    exact ENNReal.ofReal_le_ofReal (by unfold productionDual; linarith only [h₁,h₂,he])
  · simp only [extendedEntropyProduction,ite_eq_right hz,ite_eq_right hp]
    exact le_top

theorem productionDual_log_ratio {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    productionDual a b (Real.log (a/b)) = (a-b)*Real.log (a/b) := by
  have hlog : -Real.log (a/b) = Real.log (b/a) := by
    rw [Real.log_div ha.ne' hb.ne',Real.log_div hb.ne' ha.ne']
    ring
  rw [productionDual,hlog,entropyDual_log_ratio hb ha,entropyDual_log_ratio ha hb,
    scalarRelativeEntropy_eq hb,scalarRelativeEntropy_eq ha,
    Real.log_div ha.ne' hb.ne',Real.log_div hb.ne' ha.ne']
  ring

def rawProductionTest (n : ℕ) (a b : ℝ) : ℝ :=
  if a = 0 then -(n:ℝ) else if b = 0 then n else
    if |Real.log (a/b)| ≤ n then Real.log (a/b) else 0

def boundedProductionTest (n : ℕ) (a b : ℝ) : ℝ :=
  if 0 ≤ productionDual a b (rawProductionTest n a b) then rawProductionTest n a b else 0

theorem rawProductionTest_bound (n : ℕ) (a b : ℝ) :
    |rawProductionTest n a b| ≤ n := by
  unfold rawProductionTest
  split_ifs with ha hb hlog <;> simp_all

theorem boundedProductionTest_bound (n : ℕ) (a b : ℝ) :
    |boundedProductionTest n a b| ≤ n := by
  unfold boundedProductionTest
  split_ifs
  · exact rawProductionTest_bound n a b
  · simp

theorem productionDual_boundedTest_nonneg (n : ℕ) (a b : ℝ) :
    0 ≤ productionDual a b (boundedProductionTest n a b) := by
  unfold boundedProductionTest
  split_ifs with h
  · exact h
  · simp [productionDual,entropyDual]

theorem ofReal_productionDual_boundedTest (n : ℕ) (a b : ℝ) :
    ENNReal.ofReal (productionDual a b (boundedProductionTest n a b)) =
      ENNReal.ofReal (productionDual a b (rawProductionTest n a b)) := by
  unfold boundedProductionTest
  split_ifs with h
  · rfl
  · have hz : productionDual a b 0 = 0 := by simp [productionDual,entropyDual]
    rw [hz,ENNReal.ofReal_zero]
    exact (ENNReal.ofReal_eq_zero.mpr (le_of_not_ge h)).symm

theorem productionDual_coefficient_bound {s C : ℝ} (hC : |s| ≤ C) :
    |s-Real.exp (-s)+1| ≤ C+Real.exp C+1 := by
  have he : Real.exp (-s) ≤ Real.exp C :=
    Real.exp_le_exp.mpr ((neg_le_abs s).trans hC)
  calc
    _ ≤ |s-Real.exp (-s)|+|1| := abs_add_le _ _
    _ ≤ (|s|+|Real.exp (-s)|)+1 := by
      rw [abs_one]
      exact add_le_add (abs_sub _ _) le_rfl
    _ ≤ C+Real.exp C+1 := by
      rw [abs_of_pos (Real.exp_pos _)]
      exact add_le_add (add_le_add hC he) le_rfl

variable {X : Type*} [MeasurableSpace X]

theorem measurable_productionDual {a b s : X → ℝ}
    (ha : Measurable a) (hb : Measurable b) (hs : Measurable s) :
    Measurable (fun x => productionDual (a x) (b x) (s x)) :=
  (measurable_entropyDual hb ha hs).add (measurable_entropyDual ha hb hs.neg)

theorem measurable_rawProductionTest (n : ℕ) {a b : X → ℝ}
    (ha : Measurable a) (hb : Measurable b) :
    Measurable (fun x => rawProductionTest n (a x) (b x)) := by
  have hlog := (ha.div hb).log
  exact Measurable.ite (measurableSet_eq_fun ha measurable_const) measurable_const
    (Measurable.ite (measurableSet_eq_fun hb measurable_const) measurable_const
      (Measurable.ite (measurableSet_le hlog.abs measurable_const) hlog measurable_const))

theorem measurable_boundedProductionTest (n : ℕ) {a b : X → ℝ}
    (ha : Measurable a) (hb : Measurable b) :
    Measurable (fun x => boundedProductionTest n (a x) (b x)) := by
  have hs := measurable_rawProductionTest n ha hb
  exact Measurable.ite (measurableSet_le measurable_const (measurable_productionDual ha hb hs))
    hs measurable_const

theorem integrable_productionDual {μ : Measure X} {a b s : X → ℝ}
    (ha : Integrable a μ) (hb : Integrable b μ) (hs : Measurable s)
    {C : ℝ} (hC : ∀ x, |s x| ≤ C) :
    Integrable (fun x => productionDual (a x) (b x) (s x)) μ := by
  have hi := (integrable_entropyDual hb ha hs hC).add
    (integrable_entropyDual ha hb hs.neg (fun x => by simpa using hC x))
  simpa only [productionDual,Pi.add_def,Pi.neg_def] using hi

end BoltzmannNonuniqueness

end

end

section

/-! # Bounded linear tests recover infinite production at one-sided zeros -/

noncomputable section

open Filter
open scoped ENNReal Topology

namespace BoltzmannNonuniqueness

theorem ofReal_productionDual_rawTest_tendsto {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    Tendsto (fun n => ENNReal.ofReal (productionDual a b (rawProductionTest n a b))) atTop
      (𝓝 (extendedEntropyProduction a b)) := by
  by_cases haz : a = 0
  · subst a
    by_cases hbz : b = 0
    · subst b
      simp [rawProductionTest,productionDual,entropyDual,extendedEntropyProduction]
    · have hbp : 0 < b := lt_of_le_of_ne hb (Ne.symm hbz)
      have ht : Tendsto (fun n => productionDual 0 b (rawProductionTest n 0 b)) atTop atTop := by
        apply tendsto_atTop_mono _ (Tendsto.const_mul_atTop hbp tendsto_natCast_atTop_atTop)
        intro n
        have he : Real.exp (-(n:ℝ)) ≤ 1 := Real.exp_le_one_iff.mpr
          (neg_nonpos.mpr (Nat.cast_nonneg n))
        dsimp [rawProductionTest,productionDual,entropyDual]
        simp only [ite_true,zero_mul,sub_zero,zero_sub,neg_neg]
        nlinarith
      rw [show extendedEntropyProduction 0 b = ∞ by simp [extendedEntropyProduction,hbz]]
      exact ENNReal.tendsto_ofReal_atTop.comp ht
  · have hap : 0 < a := lt_of_le_of_ne ha (Ne.symm haz)
    by_cases hbz : b = 0
    · subst b
      have ht : Tendsto (fun n => productionDual a 0 (rawProductionTest n a 0)) atTop atTop := by
        apply tendsto_atTop_mono _ (Tendsto.const_mul_atTop hap tendsto_natCast_atTop_atTop)
        intro n
        have he : Real.exp (-(n:ℝ)) ≤ 1 := Real.exp_le_one_iff.mpr
          (neg_nonpos.mpr (Nat.cast_nonneg n))
        simp only [rawProductionTest,haz,↓reduceIte,productionDual,entropyDual,zero_mul,sub_zero]
        nlinarith
      rw [show extendedEntropyProduction a 0 = ∞ by simp [extendedEntropyProduction,haz]]
      exact ENNReal.tendsto_ofReal_atTop.comp ht
    · have hbp : 0 < b := lt_of_le_of_ne hb (Ne.symm hbz)
      apply tendsto_const_nhds.congr'
      filter_upwards [eventually_ge_atTop (Nat.ceil |Real.log (a/b)|)] with n hn
      have hlog : |Real.log (a/b)| ≤ (n:ℝ) :=
        (Nat.le_ceil _).trans (by exact_mod_cast hn)
      simp [rawProductionTest,haz,hbz,hlog,productionDual_log_ratio hap hbp,
        extendedEntropyProduction,hap,hbp]

theorem ofReal_productionDual_boundedTest_tendsto {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    Tendsto (fun n => ENNReal.ofReal (productionDual a b (boundedProductionTest n a b))) atTop
      (𝓝 (extendedEntropyProduction a b)) := by
  simpa only [ofReal_productionDual_boundedTest] using ofReal_productionDual_rawTest_tendsto ha hb

end BoltzmannNonuniqueness

end

end

end OAI
