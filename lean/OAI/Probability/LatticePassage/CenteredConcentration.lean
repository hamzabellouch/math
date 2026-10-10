import OAI.Probability.LatticePassage.DyadicMGF

namespace OAI

namespace CompanionFPP
open MeasureTheory ProbabilityTheory Real Finset
open scoped ENNReal

theorem finitePassageTime_centered_exponential (x y : Vertex) (R : ℕ)
    (hR : latticeDistance x y < R) (t : ℝ) :
    (Measure.pi (fun _ : ↥(localEdges x R) => expMeasure 1))
      {v | t*sqrt R ≤ |finitePassageTime x y R v - ∫ w, finitePassageTime x y R w
        ∂Measure.pi (fun _ : ↥(localEdges x R) => expMeasure 1)|} ≤
      2*ENNReal.ofReal (exp (1-t/4)) := by
  let P := Measure.pi (fun _ : ↥(localEdges x R) => expMeasure 1)
  let F := finitePassageTime x y R
  let M := ∫ v, F v ∂P
  let a : ℝ := 1/(4*sqrt R)
  have hpos : 0 < R := lt_of_le_of_lt (Nat.zero_le _) hR
  have hs : 0 < sqrt R := sqrt_pos.mpr (by exact_mod_cast hpos)
  have hs1 : 1 ≤ sqrt R := by
    have hr : (1 : ℝ) ≤ R := by exact_mod_cast hpos
    nlinarith [sq_sqrt (Nat.cast_nonneg R), sqrt_nonneg (R : ℝ)]
  have ha : 0 < a := by dsimp [a]; positivity
  have ha1 : a ≤ 1/2 := by
    dsimp [a]
    apply (div_le_iff₀ (by positivity : 0 < 4*sqrt R)).mpr
    linarith
  have has : a*sqrt R = 1/4 := by dsimp [a]; field_simp
  have ha2 : a^2*R = 1/16 := by
    calc
      _ = (a*sqrt R)^2 := by rw [mul_pow, sq_sqrt (Nat.cast_nonneg R)]
      _ = _ := by rw [has]; norm_num
  have hc := finitePassageTime_cgf_centered x y R hR a
    (by rwa [abs_of_pos ha]) (by nlinarith [ha2])
  have hcn := finitePassageTime_cgf_centered x y R hR (-a)
    (by simpa only [abs_neg, abs_of_pos ha] using ha1) (by nlinarith [ha2])
  have hu : P.real {v | M+t*sqrt R ≤ F v} ≤ exp (1-t/4) := by
    apply (measure_ge_le_exp_cgf (μ := P) (X := F) (M+t*sqrt R) ha.le
      (integrable_finitePassageTime_exp x y R hR a ha1)).trans
    apply exp_le_exp.mpr
    change cgf F P a ≤ a*M+16*a^2*R at hc
    calc
      _ ≤ -a*(M+t*sqrt R)+(a*M+16*a^2*R) := add_le_add le_rfl hc
      _ = _ := by
        rw [show -a*(M+t*sqrt R)+(a*M+16*a^2*R) = 16*(a^2*R)-t*(a*sqrt R) by ring,
          ha2, has]
        ring
  have hl : P.real {v | F v ≤ M-t*sqrt R} ≤ exp (1-t/4) := by
    apply (measure_le_le_exp_cgf (μ := P) (X := F) (M-t*sqrt R) (neg_nonpos.mpr ha.le)
      (integrable_finitePassageTime_exp x y R hR (-a) (by linarith))).trans
    apply exp_le_exp.mpr
    change cgf F P (-a) ≤ (-a)*M+16*(-a)^2*R at hcn
    calc
      _ ≤ -(-a)*(M-t*sqrt R)+((-a)*M+16*(-a)^2*R) := add_le_add le_rfl hcn
      _ = _ := by
        rw [show -(-a)*(M-t*sqrt R)+((-a)*M+16*(-a)^2*R) =
          16*(a^2*R)-t*(a*sqrt R) by ring, ha2, has]
        ring
  have hu' : P {v | M+t*sqrt R ≤ F v} ≤ ENNReal.ofReal (exp (1-t/4)) := by
    have h := ENNReal.ofReal_le_ofReal hu
    simpa only [measureReal_def, ENNReal.ofReal_toReal (measure_ne_top _ _)] using h
  have hl' : P {v | F v ≤ M-t*sqrt R} ≤ ENNReal.ofReal (exp (1-t/4)) := by
    have h := ENNReal.ofReal_le_ofReal hl
    simpa only [measureReal_def, ENNReal.ofReal_toReal (measure_ne_top _ _)] using h
  have hsub : {v | t*sqrt R ≤ |F v-M|} ⊆
      {v | M+t*sqrt R ≤ F v} ∪ {v | F v ≤ M-t*sqrt R} := by
    intro v hv
    change t*sqrt R ≤ |F v-M| at hv
    rcases le_total M (F v) with h | h
    · left
      change M+t*sqrt R ≤ F v
      rw [abs_of_nonneg (sub_nonneg.mpr h)] at hv
      linarith
    · right
      change F v ≤ M-t*sqrt R
      rw [abs_of_nonpos (sub_nonpos.mpr h)] at hv
      linarith
  change P {v | t*sqrt R ≤ |F v-M|} ≤ _
  apply (measure_mono hsub).trans
  apply (measure_union_le _ _).trans
  simpa only [two_mul] using add_le_add hu' hl'

theorem localPassageTime_centered_exponential (x y : Vertex) (R : ℕ)
    (hR : latticeDistance x y < R) (t : ℝ) :
    environmentLaw {ω | t*sqrt R ≤ |localPassageTime ω x y R -
      ∫ η, localPassageTime η x y R ∂environmentLaw|} ≤ 2*ENNReal.ofReal (exp (1-t/4)) := by
  let S := {u : ℝ | t*sqrt R ≤ |u - ∫ η, localPassageTime η x y R ∂environmentLaw|}
  have hsub : Measurable (fun u : ℝ =>
      u - ∫ η, localPassageTime η x y R ∂environmentLaw) :=
    measurable_id.sub measurable_const
  have hS : MeasurableSet S := by
    exact measurableSet_le measurable_const (by
      simpa only [Real.norm_eq_abs] using hsub.norm)
  have h₁ := Measure.map_apply (μ := environmentLaw) (measurable_localPassageTime x y R) hS
  have h₂ := Measure.map_apply (μ := Measure.pi (fun _ : ↥(localEdges x R) => expMeasure 1)) (measurable_finitePassageTime x y R) hS
  rw [finitePassageTime_law] at h₁
  have he := h₁.symm.trans h₂
  change environmentLaw ((localPassageTime · x y R) ⁻¹' S) ≤ _
  rw [he]
  dsimp [S]
  rw [← finitePassageTime_mean]
  exact finitePassageTime_centered_exponential x y R hR t

end CompanionFPP

end OAI
