import OAI.Analysis.FreeGroupFactor.UnitaryEvaluation

namespace OAI

noncomputable section

universe uA uι

open Set Metric Filter
open scoped NNReal Topology BigOperators ContDiff

open scoped Topology ContDiff
open Set Filter
namespace FreeGroupFactorMain

theorem flat_local_of_factorial_bound (f : ℝ → ℝ) (hf : ContDiff ℝ ∞ f)
    (B c : ℝ) (_hB : 0 ≤ B) (hc : 0 < c)
    (hbound : ∀ r t, |iteratedDeriv r f t| ≤ B * c ^ r * (r.factorial : ℝ))
    (a : ℝ) (ha : ∀ r, iteratedDeriv (r + 1) f a = 0)
    (x : ℝ) (hx : c * |x - a| < 1) : f x = f a := by
  by_cases hax : a = x
  · simp [hax]
  have htaylor (n : ℕ) : taylorWithinEval f n (uIcc a x) a x = f a := by
    induction n with
    | zero => simp
    | succ n ih =>
      rw [taylorWithinEval_succ, ih,
        iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_uIcc hax)
          ((hf.of_le (by exact_mod_cast (le_top : ((n + 1 : ℕ) : ℕ∞) ≤ ⊤))).contDiffAt)
          (left_mem_uIcc), ha n]
      simp
  have hest (n : ℕ) : |f x - f a| ≤ B * (c * |x - a|) ^ (n + 1) := by
    obtain ⟨y, _, hy⟩ := taylor_mean_remainder_lagrange_iteratedDeriv hax
      ((hf.of_le (by exact_mod_cast (le_top : ((n + 1 : ℕ) : ℕ∞) ≤ ⊤))).contDiffOn)
    rw [htaylor] at hy
    have hfpos : (0 : ℝ) < ((n + 1).factorial : ℝ) := by positivity
    calc
      |f x - f a| = |iteratedDeriv (n + 1) f y| * |x - a| ^ (n + 1) /
          ((n + 1).factorial : ℝ) := by rw [hy, abs_div, abs_mul, abs_pow, abs_of_pos hfpos]
      _ ≤ (B * c ^ (n + 1) * ((n + 1).factorial : ℝ)) * |x - a| ^ (n + 1) /
          ((n + 1).factorial : ℝ) := by gcongr; exact hbound _ _
      _ = B * (c * |x - a|) ^ (n + 1) := by rw [mul_pow]; field_simp
  have hlim : Tendsto (fun n : ℕ => B * (c * |x - a|) ^ (n + 1)) atTop (nhds 0) := by
    have hp := (tendsto_pow_atTop_nhds_zero_of_lt_one (mul_nonneg hc.le (abs_nonneg _)) hx)
    simpa using (hp.comp (tendsto_add_atTop_nat 1)).const_mul B
  have hz : |f x - f a| ≤ 0 := ge_of_tendsto hlim (Eventually.of_forall hest)
  exact sub_eq_zero.mp (abs_nonpos_iff.mp hz)

theorem flat_global_of_factorial_bound (f : ℝ → ℝ) (hf : ContDiff ℝ ∞ f)
    (B c : ℝ) (hB : 0 ≤ B) (hc : 0 < c)
    (hbound : ∀ r t, |iteratedDeriv r f t| ≤ B * c ^ r * (r.factorial : ℝ))
    (ha : ∀ r, iteratedDeriv (r + 1) f 0 = 0) (x : ℝ) : f x = f 0 := by
  let Z : Set ℝ := {a | ∀ r, iteratedDeriv (r + 1) f a = 0}
  have hclosed : IsClosed Z := by
    change IsClosed {a | ∀ r, iteratedDeriv (r + 1) f a = 0}
    simp only [ofPred_forall]
    apply isClosed_iInter
    intro r
    exact isClosed_eq (hf.continuous_iteratedDeriv (r + 1) (by exact_mod_cast (le_top : ((r + 1 : ℕ) : ℕ∞) ≤ ⊤))) continuous_const
  have hopen : IsOpen Z := by
    apply isOpen_iff_mem_nhds.mpr
    intro a ha
    have hδ : 0 < c⁻¹ := inv_pos.mpr hc
    apply Filter.mem_of_superset (Metric.ball_mem_nhds a hδ)
    intro y hy
    have heq : f =ᶠ[nhds y] (fun _ => f a) := by
      filter_upwards [Metric.isOpen_ball.mem_nhds hy] with z hz
      apply flat_local_of_factorial_bound f hf B c hB hc hbound a ha z
      rw [Metric.mem_ball, Real.dist_eq] at hz
      have := mul_lt_mul_of_pos_left hz hc
      simpa [ne_of_gt hc] using this
    intro r
    rw [heq.iteratedDeriv_eq (r + 1)]
    simp [iteratedDeriv_const]
  have hall : Z = univ := (show IsClopen Z from ⟨hclosed, hopen⟩).eq_univ ⟨0, ha⟩
  have hderiv (a : ℝ) : deriv f a = 0 := by
    have hz : a ∈ Z := hall ▸ mem_univ a
    simpa using hz 0
  exact isOpen_univ.is_const_of_deriv_eq_zero isPreconnected_univ
    (fun a _ => ((hf.of_le (by simp : (1 : ℕ∞ω) ≤ ∞)).differentiable (by simp)).differentiableOn a (mem_univ a))
    (fun a _ => hderiv a) (mem_univ x) (mem_univ 0)

namespace NCPolynomial

theorem iteratedDeriv_moment {ι : Type uι} {A : Type uA} [NormedRing A] [NormedAlgebra ℂ A]
    (X : ℝ → ι → A) (V : ι → Expr ι) (L : A →L[ℝ] ℝ)
    (hX : ∀ t i, HasDerivAt (fun s => X s i) (eval (X t) (V i)) t)
    (p : Expr ι) (r : ℕ) :
    iteratedDeriv r (fun t => L (eval (X t) p)) =
      fun t => L (eval (X t) ((delta V)^[r] p)) := by
  induction r with
  | zero => rfl
  | succ r ih =>
    rw [iteratedDeriv_succ, ih]
    funext t
    rw [Function.iterate_succ_apply']
    convert! (L.hasFDerivAt.comp_hasDerivAt t (hasDerivAt_eval X V t (hX t) ((delta V)^[r] p))).deriv using 1

theorem polynomial_moments {ι : Type uι} {A : Type uA} [NormedRing A] [NormedAlgebra ℂ A]
    [NormOneClass A] (X : ℝ → ι → A) (V : ι → Expr ι) (L : A →L[ℝ] ℝ)
    (hsmooth : ∀ i, ContDiff ℝ ∞ (fun t => X t i))
    (hX : ∀ t i, HasDerivAt (fun s => X s i) (eval (X t) (V i)) t)
    (R : ℝ) (hR : 1 ≤ R) (hbounded : ∀ t i, ‖X t i‖ ≤ R)
    (J : ℕ) (B : ℝ) (hB : 0 ≤ B)
    (hdeg : ∀ i, degree (V i) ≤ J + 1) (hmass : ∀ i, mass (V i) ≤ B)
    (htrace : ∀ p, L (eval (X 0) (delta V p)) = 0)
    (p : Expr ι) (t : ℝ) : L (eval (X t) p) = L (eval (X 0) p) := by
  let b := ‖L‖ * (mass p * R ^ degree p)
  let c := B * ((degree p : ℝ) + J) * R ^ J + 1
  have hR0 : 0 ≤ R := le_trans zero_le_one hR
  have hbase : 0 ≤ B * ((degree p : ℝ) + J) * R ^ J := by positivity
  have hb : 0 ≤ b := mul_nonneg (norm_nonneg _) (mul_nonneg (mass_nonneg _) (pow_nonneg hR0 _))
  have hc : 0 < c := by dsimp [c]; linarith
  apply flat_global_of_factorial_bound (fun t => L (eval (X t) p)) (L.contDiff.comp (smooth_eval X hsmooth p)) b c hb hc
  · intro r u
    rw [iteratedDeriv_moment X V L hX]
    calc
      |L (eval (X u) ((delta V)^[r] p))| ≤ ‖L‖ * ‖eval (X u) ((delta V)^[r] p)‖ :=
        L.le_opNorm _
      _ ≤ ‖L‖ * ((mass p * R ^ degree p) *
          (B * ((degree p : ℝ) + J) * R ^ J) ^ r * (r.factorial : ℝ)) := by
        gcongr
        exact norm_eval_iterate (X u) R hR (hbounded u) V J B hB hdeg hmass p r
      _ ≤ b * c ^ r * (r.factorial : ℝ) := by
        dsimp [b]
        calc
          _ = (‖L‖ * (mass p * R ^ degree p)) *
              (B * ((degree p : ℝ) + J) * R ^ J) ^ r * (r.factorial : ℝ) := by ring
          _ ≤ _ := by
            gcongr
            dsimp [c]; linarith
  · intro r
    rw [iteratedDeriv_moment X V L hX, Function.iterate_succ_apply']
    exact htrace _

end NCPolynomial
end FreeGroupFactorMain

end

end OAI
