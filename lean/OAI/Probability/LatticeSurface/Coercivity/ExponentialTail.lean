import Mathlib

namespace OAI

open MeasureTheory Set

open scoped NNReal ENNReal

noncomputable section

theorem geometric_exponential_moment {T q : ℝ} (hT : 0<T) (hq0 : 0≤q) (hq1 : q<1) :
    ∃ c : ℝ,0<c ∧ ∃ C : ℝ≥0,∀ {Ω : Type*} [MeasurableSpace Ω]
      (μ : Measure Ω) (X : Ω → ℝ),Measurable X →
      (∀ j : ℕ,μ {ω | (j:ℝ)*T≤|X ω|}≤ENNReal.ofReal q^j*μ univ) →
      (∫⁻ ω,ENNReal.ofReal (Real.exp (c*|X ω|)) ∂μ)≤C*μ univ := by
  let v : ℝ := 2/(1+q)
  have hv1 : 1<v := by dsimp [v];rw [lt_div_iff₀ (by linarith : 0<1+q)];linarith
  have hv0 : 0≤v := le_of_lt (lt_trans (by norm_num) hv1)
  have hvq : v*q<1 := by dsimp [v];rw [div_mul_eq_mul_div,div_lt_iff₀ (by linarith : 0<1+q)];linarith
  let c : ℝ := Real.log v/T
  have hc : 0<c := div_pos (Real.log_pos hv1) hT
  have hcT : c*T=Real.log v := by dsimp [c];field_simp
  have hs : Summable (fun n : ℕ => v^(n+1)*q^n) := by
    have h := summable_geometric_of_norm_lt_one (x:=v*q) (by rw [Real.norm_eq_abs,abs_of_nonneg (mul_nonneg hv0 hq0)];exact hvq)
    have he : (fun n : ℕ => v^(n+1)*q^n)=(fun n : ℕ => v*(v*q)^n) := by
      funext n;rw [pow_succ,mul_pow];ring
    rw [he]
    exact h.mul_left v
  let K : ENNReal := ∑' n : ℕ,ENNReal.ofReal (v^(n+1)*q^n)
  have hK : K≠⊤ := hs.tsum_ofReal_ne_top
  refine ⟨c,hc,K.toNNReal,?_⟩
  intro Ω _ μ X hX htail
  rw [ENNReal.coe_toNNReal hK]
  let D : Ω → ℕ := fun ω => ⌊|X ω|/T⌋₊
  have hD : Measurable D := Nat.measurable_floor.comp (hX.abs.div_const T)
  have hd (n : ℕ) : μ {ω | D ω=n}≤ENNReal.ofReal q^n*μ univ := by
    apply (measure_mono ?_).trans (htail n)
    intro ω hω
    change D ω=n at hω
    have hfloor := Nat.floor_le (div_nonneg (abs_nonneg (X ω)) hT.le)
    change (D ω:ℝ)≤|X ω|/T at hfloor
    rw [hω] at hfloor
    exact (le_div_iff₀ hT).mp hfloor
  have hpoint (ω : Ω) : Real.exp (c*|X ω|)≤v^(D ω+1) := by
    have hfloor := Nat.lt_floor_add_one (|X ω|/T)
    change |X ω|/T<(D ω:ℝ)+1 at hfloor
    have hlt := (div_lt_iff₀ hT).mp hfloor
    have hle : c*|X ω|≤((D ω:ℝ)+1)*Real.log v := by
      nlinarith [mul_le_mul_of_nonneg_left hlt.le hc.le]
    calc
      _ ≤ Real.exp (((D ω:ℝ)+1)*Real.log v) := Real.exp_le_exp.mpr hle
      _ = v^(D ω+1) := by rw [← Nat.cast_add_one,Real.exp_nat_mul,Real.exp_log (lt_of_lt_of_le (by norm_num : (0:ℝ)<1) hv1.le)]
  calc
    _ ≤ ∫⁻ ω,ENNReal.ofReal (v^(D ω+1)) ∂μ := lintegral_mono (fun ω => ENNReal.ofReal_le_ofReal (hpoint ω))
    _ = ∫⁻ n : ℕ,ENNReal.ofReal (v^(n+1)) ∂(μ.map D) :=
      (lintegral_map (μ:=μ) (f:=fun n : ℕ => ENNReal.ofReal (v^(n+1))) (measurable_of_countable _) hD).symm
    _ = ∑' n : ℕ,ENNReal.ofReal (v^(n+1))*(μ.map D) {n} := lintegral_countable' _
    _ = ∑' n : ℕ,ENNReal.ofReal (v^(n+1))*μ {ω | D ω=n} := by
      apply tsum_congr;intro n;rw [Measure.map_apply hD (measurableSet_singleton n)];rfl
    _ ≤ ∑' n : ℕ,ENNReal.ofReal (v^(n+1))*(ENNReal.ofReal q^n*μ univ) := by
      apply ENNReal.tsum_le_tsum;intro n;gcongr;exact hd n
    _ = K*μ univ := by
      dsimp only [K]
      rw [← ENNReal.tsum_mul_right]
      apply tsum_congr
      intro n
      rw [← ENNReal.ofReal_pow hq0,ENNReal.ofReal_mul (pow_nonneg hv0 _)]
      ring

end

end OAI
