import OAI.Analysis.StrictMeans.PositiveFunctionals

namespace OAI

section
open Set Filter Metric Complex MeasureTheory
open scoped Topology ENNReal ComplexConjugate
open Set Filter Metric Complex
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology
open Set Filter Metric Complex Function MeasureTheory
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter MeasureTheory
open scoped Topology

namespace StrictInverseFirstPower
noncomputable section
open Set Filter MeasureTheory
open scoped Topology

variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A]

omit [CompleteSpace A] in
lemma scaled_power (a : A) (t : ℝ) (n : ℕ) : (t • a) ^ n = t ^ n • a ^ n :=
  smul_pow t a n

def growthResolvent (a : A) (τ : ℝ) : A := ∑' n : ℕ, (τ⁻¹ • a) ^ n

lemma summable_growthResolvent (a : A) (h : ∀ n : ℕ, 1 ≤ ‖a ^ n‖)
    {τ : ℝ} (hτ : 0 < τ) (hg : logNormGrowth a h < Real.log τ) :
    Summable (fun n : ℕ => (τ⁻¹ • a) ^ n) := by
  simpa only [smul_pow] using summable_resolventPower a h hτ hg

lemma growthResolvent_mul (a : A) (h : ∀ n : ℕ, 1 ≤ ‖a ^ n‖)
    {τ : ℝ} (hτ : 0 < τ) (hg : logNormGrowth a h < Real.log τ) :
    growthResolvent a τ * a = τ • (growthResolvent a τ - 1) := by
  have hh := (summable_growthResolvent a h hτ hg).tsum_pow_mul_one_sub
  change growthResolvent a τ * (1 - τ⁻¹ • a) = 1 at hh
  rw [mul_sub, mul_one, mul_smul_comm] at hh
  have he : τ⁻¹ • (growthResolvent a τ * a) = growthResolvent a τ - 1 := by
    exact (sub_eq_iff_eq_add.mp hh).symm |> eq_sub_of_add_eq'
  calc
    growthResolvent a τ * a = τ • (τ⁻¹ • (growthResolvent a τ * a)) := by
      rw [smul_smul, mul_inv_cancel₀ hτ.ne', one_smul]
    _ = τ • (growthResolvent a τ - 1) := congrArg (τ • ·) he

lemma mul_growthResolvent (a : A) (h : ∀ n : ℕ, 1 ≤ ‖a ^ n‖)
    {τ : ℝ} (hτ : 0 < τ) (hg : logNormGrowth a h < Real.log τ) :
    a * growthResolvent a τ = τ • (growthResolvent a τ - 1) := by
  have hh := (summable_growthResolvent a h hτ hg).one_sub_mul_tsum_pow
  change (1 - τ⁻¹ • a) * growthResolvent a τ = 1 at hh
  rw [sub_mul, one_mul, smul_mul_assoc] at hh
  have he : τ⁻¹ • (a * growthResolvent a τ) = growthResolvent a τ - 1 := by
    exact (sub_eq_iff_eq_add.mp hh).symm |> eq_sub_of_add_eq'
  calc
    a * growthResolvent a τ = τ • (τ⁻¹ • (a * growthResolvent a τ)) := by
      rw [smul_smul, mul_inv_cancel₀ hτ.ne', one_smul]
    _ = τ • (growthResolvent a τ - 1) := congrArg (τ • ·) he

section Positive
variable {X : Type*} [TopologicalSpace X] [CompactSpace X]

lemma growthResolvent_apply_series (L : C(X, ℝ) →L[ℝ] C(X, ℝ))
    (h : ∀ n : ℕ, 1 ≤ ‖L ^ n‖) {τ : ℝ} (hτ : 0 < τ)
    (hg : logNormGrowth L h < Real.log τ) (f : C(X, ℝ)) (x : X) :
    growthResolvent L τ f x = ∑' n : ℕ, τ⁻¹ ^ n * ((L ^ n) f) x := by
  let e := (ContinuousMap.evalCLM ℝ x).comp (ContinuousLinearMap.apply ℝ C(X, ℝ) f)
  have he := e.map_tsum (summable_growthResolvent L h hτ hg)
  change growthResolvent L τ f x = _ at he
  rw [he]
  apply tsum_congr
  intro n
  rw [scaled_power]
  simp [e]

lemma growthResolvent_monotone (L : C(X, ℝ) →L[ℝ] C(X, ℝ)) (hL : Monotone L)
    (h : ∀ n : ℕ, 1 ≤ ‖L ^ n‖) {τ : ℝ} (hτ : 0 < τ)
    (hg : logNormGrowth L h < Real.log τ) : Monotone (growthResolvent L τ : C(X, ℝ) →L[ℝ] C(X, ℝ)) := by
  have hp : ∀ f : C(X, ℝ), 0 ≤ f → 0 ≤ growthResolvent L τ f := by
    intro f hf x
    change (0 : ℝ) ≤ growthResolvent L τ f x
    rw [growthResolvent_apply_series L h hτ hg]
    apply tsum_nonneg
    intro n
    apply mul_nonneg (pow_nonneg (inv_nonneg.mpr hτ.le) n)
    have hh := positiveOperator_pow_monotone L hL n hf x
    change ((L ^ n) 0) x ≤ ((L ^ n) f) x at hh
    simpa only [map_zero, ContinuousMap.zero_apply] using hh
  intro f g hfg
  rw [← sub_nonneg, ← map_sub]
  exact hp (g - f) (sub_nonneg.mpr hfg)

lemma growthResolvent_unit_ge_one (L : C(X, ℝ) →L[ℝ] C(X, ℝ)) (hL : Monotone L)
    (h : ∀ n : ℕ, 1 ≤ ‖L ^ n‖) {τ : ℝ} (hτ : 0 < τ)
    (hg : logNormGrowth L h < Real.log τ) : (1 : C(X, ℝ)) ≤ growthResolvent L τ 1 := by
  intro x
  let e := (ContinuousMap.evalCLM ℝ x).comp (ContinuousLinearMap.apply ℝ C(X, ℝ) (1 : C(X, ℝ)))
  have hs := e.summable (summable_growthResolvent L h hτ hg)
  have hh := hs.le_tsum 0 (fun n _ => show 0 ≤ e ((τ⁻¹ • L) ^ n) from by
    rw [scaled_power L τ⁻¹ n]
    change 0 ≤ τ⁻¹ ^ n * ((L ^ n) 1) x
    exact mul_nonneg (pow_nonneg (inv_nonneg.mpr hτ.le) n)
      (positiveOperator_unit_nonneg (L ^ n) (positiveOperator_pow_monotone L hL n) x))
  have he := e.map_tsum (summable_growthResolvent L h hτ hg)
  rw [← he] at hh
  simpa [e, growthResolvent] using hh

end Positive

end
end StrictInverseFirstPower

namespace StrictInverseFirstPower
noncomputable section
open Set Filter MeasureTheory
open scoped Topology

variable {X : Type*} [TopologicalSpace X] [CompactSpace X] [Nonempty X]
  [T2Space X] [MeasurableSpace X] [BorelSpace X]

lemma exists_approximate_eigenprobability
    (L : C(X, ℝ) →L[ℝ] C(X, ℝ)) (hL : Monotone L)
    (h : ∀ n : ℕ, 1 ≤ ‖L ^ n‖) {τ : ℝ} (hτ : 0 < τ)
    (hg : logNormGrowth L h < Real.log τ) :
    ∃ μ : ProbabilityMeasure X, ∀ f : C(X, ℝ),
      |(∫ x, L f x ∂(μ : Measure X)) - τ * ∫ x, f x ∂(μ : Measure X)| ≤
        (τ - Real.exp (logNormGrowth L h)) * ‖f‖ := by
  let R := growthResolvent L τ
  let g := R (1 : C(X, ℝ))
  have hR : Monotone R := growthResolvent_monotone L hL h hτ hg
  have hg1 : (1 : C(X, ℝ)) ≤ g := growthResolvent_unit_ge_one L hL h hτ hg
  obtain ⟨x, _, hx⟩ := isCompact_univ.exists_isMaxOn (univ_nonempty : (univ : Set X).Nonempty)
    g.continuous.continuousOn
  let M := g x
  have hM1 : 1 ≤ M := hg1 x
  have hMpos : 0 < M := lt_of_lt_of_le zero_lt_one hM1
  have hM : g ≤ M • (1 : C(X, ℝ)) := by
    intro y
    change g y ≤ M * 1
    rw [mul_one]
    exact hx (mem_univ y)
  have hMi : M⁻¹ ≤ 1 := by
    rw [inv_eq_one_div, div_le_one hMpos]
    exact hM1
  let a := τ * (1 - M⁻¹)
  have ha : 0 ≤ a := mul_nonneg hτ.le (sub_nonneg.mpr hMi)
  have hLg : L g = τ • (g - 1) := by
    have hh := congrArg (fun S : C(X, ℝ) →L[ℝ] C(X, ℝ) => S 1)
      (mul_growthResolvent L h hτ hg)
    exact hh
  have hsuper : L g ≤ a • g := by
    rw [hLg]
    intro y
    change τ * (g y - 1) ≤ a * g y
    have hi : M⁻¹ * g y ≤ 1 := by
      have hh := mul_le_mul_of_nonneg_left (hx (mem_univ y)) (inv_nonneg.mpr hMpos.le)
      change M⁻¹ * g y ≤ M⁻¹ * M at hh
      simpa only [inv_mul_cancel₀ hMpos.ne'] using hh
    dsimp [a]
    nlinarith [mul_nonneg hτ.le (sub_nonneg.mpr hi)]
  have hiter (n : ℕ) : ‖L ^ n‖ ≤ M * a ^ n :=
    positiveOperator_iterate_bound L hL g ha hg1 hM hsuper n
  have hapos : 0 < a := by
    have hh := (h 1).trans (hiter 1)
    simp only [pow_one] at hh
    by_contra hn
    have hz : a = 0 := le_antisymm (le_of_not_gt hn) ha
    norm_num [hz] at hh
  have hρ : Real.exp (logNormGrowth L h) ≤ a := by
    calc
      Real.exp (logNormGrowth L h) ≤ Real.exp (Real.log a) :=
        Real.exp_le_exp.mpr (logNormGrowth_le_of_power_bound L h hMpos hapos hiter)
      _ = a := Real.exp_log hapos
  have herr : τ / M ≤ τ - Real.exp (logNormGrowth L h) := by
    dsimp [a] at hρ
    rw [div_eq_mul_inv]
    nlinarith
  have herr0 : 0 ≤ τ / M := (div_pos hτ hMpos).le
  let Λ : C(X, ℝ) →L[ℝ] ℝ := M⁻¹ • ((ContinuousMap.evalCLM ℝ x).comp R)
  have hΛ : Monotone Λ := by
    intro f₁ f₂ hf
    change M⁻¹ * R f₁ x ≤ M⁻¹ * R f₂ x
    exact mul_le_mul_of_nonneg_left (hR hf x) (inv_nonneg.mpr hMpos.le)
  have hΛ1 : Λ 1 = 1 := by
    change M⁻¹ * M = 1
    exact inv_mul_cancel₀ hMpos.ne'
  obtain ⟨μ, hμ⟩ := exists_probabilityMeasure_of_positiveFunctional Λ hΛ hΛ1
  refine ⟨μ, fun f => ?_⟩
  rw [hμ (L f), hμ f]
  change |M⁻¹ * R (L f) x - τ * (M⁻¹ * R f x)| ≤ _
  have hh := congrArg (fun S : C(X, ℝ) →L[ℝ] C(X, ℝ) => S f x)
    (growthResolvent_mul L h hτ hg)
  change R (L f) x = τ * (R f x - f x) at hh
  rw [hh]
  have hid : M⁻¹ * (τ * (R f x - f x)) - τ * (M⁻¹ * R f x) = -(τ / M * f x) := by
    rw [div_eq_mul_inv]
    ring
  rw [hid, abs_neg, abs_mul, abs_of_nonneg herr0]
  exact (mul_le_mul_of_nonneg_left (f.norm_coe_le_norm x) herr0).trans
    (mul_le_mul_of_nonneg_right herr (norm_nonneg f))

theorem exists_exact_eigenprobability [TopologicalSpace.MetrizableSpace X]
    (L : C(X, ℝ) →L[ℝ] C(X, ℝ)) (hL : Monotone L)
    (h : ∀ n : ℕ, 1 ≤ ‖L ^ n‖) :
    ∃ μ : ProbabilityMeasure X, ∀ f : C(X, ℝ),
      (∫ x, L f x ∂(μ : Measure X)) =
        Real.exp (logNormGrowth L h) * ∫ x, f x ∂(μ : Measure X) := by
  classical
  let : MetricSpace X := TopologicalSpace.metrizableSpaceMetric X
  let ρ := Real.exp (logNormGrowth L h)
  have hρ : 0 < ρ := Real.exp_pos _
  let τ (n : ℕ) := ρ + 1 / ((n : ℝ) + 1)
  have hτgt (n : ℕ) : ρ < τ n := by
    dsimp [τ]
    have hn : (0 : ℝ) < n + 1 := by positivity
    exact lt_add_of_pos_right _ (one_div_pos.mpr hn)
  have hτ (n : ℕ) : 0 < τ n := hρ.trans (hτgt n)
  have hg (n : ℕ) : logNormGrowth L h < Real.log (τ n) := by
    calc
      logNormGrowth L h = Real.log ρ := (Real.log_exp _).symm
      _ < Real.log (τ n) := Real.log_lt_log hρ (hτgt n)
  choose μ hμ using fun n => exists_approximate_eigenprobability L hL h (hτ n) (hg n)
  obtain ⟨ν, φ, hφ, hν⟩ := CompactSpace.tendsto_subseq μ
  refine ⟨ν, fun f => ?_⟩
  have hτlim : Tendsto τ atTop (𝓝 ρ) := by
    simpa only [add_zero] using
      tendsto_one_div_add_atTop_nhds_zero_nat.const_add ρ
  have hτφ : Tendsto (τ ∘ φ) atTop (𝓝 ρ) := hτlim.comp hφ.tendsto_atTop
  have hf := (ProbabilityMeasure.continuous_integral_continuousMap f).tendsto ν |>.comp hν
  have hLf := (ProbabilityMeasure.continuous_integral_continuousMap (L f)).tendsto ν |>.comp hν
  have habs := (hLf.sub (hτφ.mul hf)).abs
  have hzero : Tendsto (fun n => (τ (φ n) - ρ) * ‖f‖) atTop (𝓝 0) := by
    convert! (hτφ.sub_const ρ).mul_const ‖f‖ using 1; simp only [sub_self, zero_mul]
  have hh : |(∫ x, L f x ∂(ν : Measure X)) - ρ * ∫ x, f x ∂(ν : Measure X)| ≤ 0 :=
    le_of_tendsto_of_tendsto habs hzero (Eventually.of_forall fun n => hμ (φ n) f)
  exact sub_eq_zero.mp (abs_nonpos_iff.mp hh)

end
end StrictInverseFirstPower

end

end OAI
