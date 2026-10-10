import OAI.MeasureTheory.Falconer.Geometry.ConditionalBalls

namespace OAI

/-! # The actual affine rescaling of a conditional class probability -/

namespace Falconer.Regularization
open Set MeasureTheory Metric
open scoped ENNReal
variable {d : ℕ}

noncomputable def cellScaleMap (p : ℕ) (c : Space d) (z : Space d) : Space d :=
  (2:ℝ)^p • (z-c)

theorem cellScaleMap_continuous (p : ℕ) (c : Space d) : Continuous (cellScaleMap p c) := by
  change Continuous (fun z : Space d => (2:ℝ)^p • (z-c))
  exact (continuous_id.sub continuous_const).const_smul ((2:ℝ)^p)

theorem cellScaleMap_preimage_ball (p : ℕ) (c x : Space d) (r : ℝ) :
    cellScaleMap p c ⁻¹' ball x r = ball (c+((2:ℝ)^p)⁻¹ • x) (r/(2:ℝ)^p) := by
  ext z
  have hs : 0 < (2:ℝ)^p := by positivity
  have he : (2:ℝ)^p • (z-c)-x = (2:ℝ)^p • (z-(c+((2:ℝ)^p)⁻¹ • x)) := by
    simp only [smul_sub,smul_add,smul_smul,mul_inv_cancel₀ hs.ne',one_smul]
    abel
  simp only [mem_preimage,mem_ball,dist_eq_norm,cellScaleMap]
  rw [he,norm_smul,Real.norm_eq_abs,abs_of_pos hs,lt_div_iff₀ hs]
  simp only [mul_comm]

theorem rescaled_conditional_ball_apply (ρ : Measure (Space d)) (p : ℕ) (c : Space d)
    (P : Set (Space d)) (x : Space d) (r : ℝ) :
    (Measure.map (cellScaleMap p c) (ProbabilityTheory.cond ρ P)) (ball x r) =
      ProbabilityTheory.cond ρ P (ball (c+((2:ℝ)^p)⁻¹ • x) (r/(2:ℝ)^p)) := by
  rw [Measure.map_apply (cellScaleMap_continuous p c).measurable measurableSet_ball,
    cellScaleMap_preimage_ball]

theorem sourceClass_rescaled_dyadic_ball (Q : DyadicCube d) (hQ : Q.side = 1)
    (μ : Measure (Space d)) [IsProbabilityMeasure μ] {N B : ℕ} (hN : 0 < N) (hB : 0 < B)
    {lam : ℝ} (hwidth : (B:ℝ) ≤ lam*(N:ℝ))
    (hlarge : (2:ℝ)^(N/B+2) ≤ ((2:ℝ)^N)^lam)
    {p₀ : CellPath d} (hp₀ : p₀ ∈ regularizationLeaves Q μ N)
    {p n : ℕ} (hpn : p ≤ n) (hn : n ≤ N) {P : CellPath d} (hP : P.length = p)
    (hPpos : 0 < sourceClass Q μ N B p₀ (Q.descendant P).carrier)
    (x : Space d) {C : ℝ} (hC : 0 ≤ C) :
    ((Measure.map (cellScaleMap p (Q.descendant P).center)
      (ProbabilityTheory.cond (sourceClass Q μ N B p₀) (Q.descendant P).carrier))
        (ball x (C/(2:ℝ)^(n-p)))).toReal ≤
      ((2*Nat.ceil (2*C+4*Real.sqrt d)+1)^d:ℕ)*((2:ℝ)^N)^
        (sourceProfile Q μ N B p₀ p-sourceProfile Q μ N B p₀ n+2*((d:ℝ)+1)*lam) := by
  rw [rescaled_conditional_ball_apply]
  have hr : (C/(2:ℝ)^(n-p))/(2:ℝ)^p = C*(Q.side/(2:ℝ)^n) := by
    rw [div_div,← pow_add,Nat.sub_add_cancel hpn,hQ]
    ring
  rw [hr]
  exact sourceClass_conditional_ball_upper Q (by rw [hQ]; norm_num) μ hN hB hwidth hlarge hp₀
    (hpn.trans hn) hn hP hPpos _ hC

theorem dyadic_radius_bracket {m : ℕ} {r : ℝ}
    (hmin : 1/(2:ℝ)^m ≤ r) (hmax : r ≤ 1) :
    ∃ j ≤ m, r ≤ 1/(2:ℝ)^j ∧ 1/(2:ℝ)^j ≤ 2*r := by
  induction m with
  | zero =>
    refine ⟨0,le_rfl,?_,?_⟩
    · simpa using hmax
    · norm_num at hmin ⊢
      linarith
  | succ m ih =>
    by_cases hcoarse : 1/(2:ℝ)^m ≤ r
    · obtain ⟨j,hj,hr,hjr⟩ := ih hcoarse
      exact ⟨j,hj.trans (Nat.le_succ m),hr,hjr⟩
    · refine ⟨m,Nat.le_succ m,(lt_of_not_ge hcoarse).le,?_⟩
      have he : 1/(2:ℝ)^m = 2*(1/(2:ℝ)^(m+1)) := by rw [pow_succ]; field_simp
      rw [he]
      linarith

end Falconer.Regularization

end OAI
