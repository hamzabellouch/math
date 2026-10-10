import OAI.Analysis.AncientFlat.Regularity.PointInterpolation

namespace OAI
noncomputable section
open Set Filter MeasureTheory Metric
open scoped ContDiff
namespace ParabolicInterpolation
variable {V E : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
omit [CompleteSpace E] in
lemma jet_lipschitz_ball (n : ℕ) (f : V → E) (hf : ContDiff ℝ (n+1) f)
    (R M : ℝ) (hD : ∀ z, ‖z‖<R → ‖iteratedFDeriv ℝ (n+1) f z‖≤M)
    (x y : V) (hx : ‖x‖<R) (hy : ‖y‖<R) :
    ‖iteratedFDeriv ℝ n f y-iteratedFDeriv ℝ n f x‖≤M*‖y-x‖ := by
  apply (convex_ball (0:V) R).norm_image_sub_le_of_norm_fderiv_le
    (fun z _ => hf.differentiable_iteratedFDeriv (by exact_mod_cast Nat.lt_succ_self n) z)
  · intro z hz
    rw [norm_fderiv_iteratedFDeriv]
    exact hD z (by simpa only [mem_ball,dist_zero_right] using hz)
  · simpa only [mem_ball,dist_zero_right] using hx
  · simpa only [mem_ball,dist_zero_right] using hy
lemma jet_ball_bound (n : ℕ) (f : V → E) (hf : ContDiff ℝ (n+1) f)
    (x : V) (R q U M : ℝ) (hq : 0<q) (hU : 0≤U) (hM : 0≤M)
    (hgap : ‖x‖+n*q<R) (hu : ∀ y, ‖y‖<R → ‖f y‖≤U)
    (hD : ∀ y, ‖y‖<R → ‖iteratedFDeriv ℝ (n+1) f y‖≤M) :
    ‖iteratedFDeriv ℝ n f x‖≤2^n/q^n*U+M*(n*q) := by
  have hx : ‖x‖<R := lt_of_le_of_lt (le_add_of_nonneg_right (by positivity)) hgap
  have hy (y : V) (h : ‖y-x‖≤n*q) : ‖y‖<R := by
    calc
      ‖y‖≤‖x‖+‖y-x‖ := norm_le_insert' _ _
      _≤‖x‖+n*q := add_le_add le_rfl h
      _<R := hgap
  apply jet_point_bound n f (hf.of_le (by exact_mod_cast Nat.le_succ n)) x q U (M*(n*q)) hq hU (by positivity)
  · intro y h; exact hu y (hy y h)
  · intro y h
    exact (jet_lipschitz_ball n f hf R M hD x y hx (hy y h)).trans
      (mul_le_mul_of_nonneg_left h hM)

lemma fourth_sup_interpolation (f : V → E) (hf : ContDiff ℝ 4 f)
    (x : V) (R q U H α : ℝ) (hq : 0<q) (hU : 0≤U) (hH : 0≤H) (hα : 0≤α)
    (hgap : ‖x‖+4*q<R) (hu : ∀ y, ‖y‖<R → ‖f y‖≤U)
    (hD : ∀ y, ‖y‖<R → ∀ z, ‖z‖<R →
      ‖iteratedFDeriv ℝ 4 f y-iteratedFDeriv ℝ 4 f z‖≤H*‖y-z‖^α) :
    ‖iteratedFDeriv ℝ 4 f x‖≤16/q^4*U+H*(4*q)^α := by
  have hx : ‖x‖<R := by linarith
  have hy (y : V) (h : ‖y-x‖≤4*q) : ‖y‖<R := by
    exact lt_of_le_of_lt (norm_le_insert' y x) (by linarith)
  simpa only [Nat.cast_ofNat, show (2:ℝ)^4=16 by norm_num] using jet_point_bound 4 f hf x q U (H*(4*q)^α) hq hU (by positivity)
    (fun y h => hu y (hy y h)) (fun y h => (hD y (hy y h) x hx).trans
      (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (norm_nonneg _) h hα) hH))

lemma lower_jet_bounds (f : V → E) (hf : ContDiff ℝ 4 f)
    (R q U M : ℝ) (hq : 0<q) (hU : 0≤U) (hM : 0≤M)
    (hu : ∀ y, ‖y‖<R → ‖f y‖≤U)
    (hD : ∀ y, ‖y‖<R → ‖iteratedFDeriv ℝ 4 f y‖≤M) :
    (∀ x, ‖x‖+3*q<R → ‖iteratedFDeriv ℝ 3 f x‖≤8/q^3*U+3*q*M) ∧
    (∀ x, ‖x‖+5*q<R → ‖iteratedFDeriv ℝ 2 f x‖≤20/q^2*U+6*q^2*M) ∧
    (∀ x, ‖x‖+6*q<R → ‖iteratedFDeriv ℝ 1 f x‖≤22/q*U+6*q^3*M) := by
  have h3 (x : V) (hx : ‖x‖+3*q<R) :
      ‖iteratedFDeriv ℝ 3 f x‖≤8/q^3*U+3*q*M := by
    have := jet_ball_bound 3 f hf x R q U M hq hU hM (by simpa using hx) hu hD
    convert this using 1
    norm_num
    ring
  have h2 (x : V) (hx : ‖x‖+5*q<R) :
      ‖iteratedFDeriv ℝ 2 f x‖≤20/q^2*U+6*q^2*M := by
    have hb := jet_ball_bound 2 f (hf.of_le (by norm_num)) x (R-3*q) q U (8/q^3*U+3*q*M)
      hq hU (by positivity) (by norm_num; linarith)
      (fun y hy => hu y (by linarith)) (fun y hy => h3 y (by linarith))
    convert hb using 1
    norm_num
    field_simp [hq.ne']; ring
  have h1 (x : V) (hx : ‖x‖+6*q<R) :
      ‖iteratedFDeriv ℝ 1 f x‖≤22/q*U+6*q^3*M := by
    have hb := jet_ball_bound 1 f (hf.of_le (by norm_num)) x (R-5*q) q U (20/q^2*U+6*q^2*M)
      hq hU (by positivity) (by norm_num; linarith)
      (fun y hy => hu y (by linarith)) (fun y hy => h2 y (by linarith))
    convert hb using 1
    norm_num
    field_simp [hq.ne']; ring
  exact ⟨h3,h2,h1⟩
end ParabolicInterpolation

end

end OAI
