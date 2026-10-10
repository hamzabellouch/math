import OAI.Analysis.KadisonKastler.SupportBounds

namespace OAI

/-!
# Restoring clipped coefficient columns

These estimates separate the small errors on fixed vectors from the
commutator of the moving unitary. In particular, a contractive discarded
column costs only the commutator bound of that unitary.
-/

namespace KadisonKastler

open Filter
open scoped Topology

noncomputable section

variable {H ω J : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [Fintype ω]

omit [InnerProductSpace ℂ H] in
/-- Finitely many strong errors vanish in column norm as well. -/
theorem tendsto_column_norm_zero (l : Filter J) (v : J → ω → H)
    (hv : ∀ w, Tendsto (fun j => ‖v j w‖) l (𝓝 0)) :
    Tendsto (fun j => ‖WithLp.toLp 2 (v j)‖) l (𝓝 0) := by
  have hs : Tendsto (fun j => ∑ w, ‖v j w‖ ^ 2) l (𝓝 0) := by
    simpa only [zero_pow (by decide : (2 : ℕ) ≠ 0), Finset.sum_const_zero] using
      tendsto_finsetSum Finset.univ (fun w _ => (hv w).pow 2)
  simpa only [PiLp.norm_eq_of_L2, Real.sqrt_zero, Function.comp_def] using
    (Real.continuous_sqrt.tendsto 0).comp hs

theorem column_commutator_error_le (h : H →L[ℂ] H) (E : ω → H →L[ℂ] H) (x : H) :
    ‖WithLp.toLp 2 (fun w => (h * E w - E w * h) x)‖ ≤
      ‖h‖ * ‖WithLp.toLp 2 (fun w => E w x)‖ +
        ‖WithLp.toLp 2 (fun w => E w (h x))‖ := by
  change ‖WithLp.toLp 2 (fun w => h (E w x)) -
    WithLp.toLp 2 (fun w => E w (h x))‖ ≤ _
  exact (norm_sub_le _ _).trans
    (add_le_add (norm_pointwise_operator_le h _) le_rfl)

/-- Restoring a discarded column on a moving vector isolates the sole
term which need not vanish on fixed vectors. -/
theorem column_commutator_moving_error_le (h s : H →L[ℂ] H)
    (E : ω → H →L[ℂ] H)
    (hE : ∀ z, ‖WithLp.toLp 2 (fun w => E w z)‖ ≤ ‖z‖) (y : H) :
    ‖WithLp.toLp 2 (fun w => (h * E w - E w * h) (s y))‖ ≤
      ‖h‖ * ‖WithLp.toLp 2 (fun w => E w (s y))‖ +
        ‖WithLp.toLp 2 (fun w => E w (s (h y)))‖ + ‖(h * s - s * h) y‖ := by
  have he : WithLp.toLp 2 (fun w => E w (h (s y))) =
      WithLp.toLp 2 (fun w => E w (s (h y))) +
        WithLp.toLp 2 (fun w => E w ((h * s - s * h) y)) := by
    ext w
    change E w (h (s y)) = E w (s (h y)) + E w (h (s y) - s (h y))
    rw [map_sub]
    abel
  calc
    _ ≤ ‖h‖ * ‖WithLp.toLp 2 (fun w => E w (s y))‖ +
        ‖WithLp.toLp 2 (fun w => E w (h (s y)))‖ := column_commutator_error_le h E _
    _ ≤ ‖h‖ * ‖WithLp.toLp 2 (fun w => E w (s y))‖ +
        (‖WithLp.toLp 2 (fun w => E w (s (h y)))‖ + ‖(h * s - s * h) y‖) := by
      apply add_le_add le_rfl
      rw [he]
      exact (norm_add_le _ _).trans (add_le_add le_rfl (hE _))
    _ = _ := by ring

/-- A pointwise error estimate for replacing a clipped column by the
original column. -/
theorem column_restored_drift_le (h : H →L[ℂ] H)
    (K K' E : ω → H →L[ℂ] H) (hK : ∀ w, K w = K' w + E w)
    (x : H) {C : ℝ}
    (hC : ‖WithLp.toLp 2 (fun w => (h * K' w - K' w * h) x)‖ ≤ C) :
    ‖WithLp.toLp 2 (fun w => (h * K w - K w * h) x)‖ ≤ C +
      ‖h‖ * ‖WithLp.toLp 2 (fun w => E w x)‖ +
        ‖WithLp.toLp 2 (fun w => E w (h x))‖ := by
  have he : WithLp.toLp 2 (fun w => (h * K w - K w * h) x) =
      WithLp.toLp 2 (fun w => (h * K' w - K' w * h) x) +
        WithLp.toLp 2 (fun w => (h * E w - E w * h) x) := by
    ext w
    change (h * K w - K w * h) x =
      (h * K' w - K' w * h) x + (h * E w - E w * h) x
    simp only [hK, mul_add, add_mul, sub_apply, add_apply]
    abel
  rw [he]
  exact ((norm_add_le _ _).trans
    (add_le_add hC (column_commutator_error_le h E x))).trans_eq (by ring)

/-- The moving-vector version retains only the commutator of the moving
operator besides the two strong errors. -/
theorem column_restored_moving_drift_le (h s : H →L[ℂ] H)
    (K K' E : ω → H →L[ℂ] H) (hK : ∀ w, K w = K' w + E w)
    (hE : ∀ z, ‖WithLp.toLp 2 (fun w => E w z)‖ ≤ ‖z‖)
    (y : H) {C : ℝ}
    (hC : ‖WithLp.toLp 2 (fun w => (h * K' w - K' w * h) (s y))‖ ≤ C) :
    ‖WithLp.toLp 2 (fun w => (h * K w - K w * h) (s y))‖ ≤ C +
      ‖h‖ * ‖WithLp.toLp 2 (fun w => E w (s y))‖ +
        ‖WithLp.toLp 2 (fun w => E w (s (h y)))‖ + ‖(h * s - s * h) y‖ := by
  have he : WithLp.toLp 2 (fun w => (h * K w - K w * h) (s y)) =
      WithLp.toLp 2 (fun w => (h * K' w - K' w * h) (s y)) +
        WithLp.toLp 2 (fun w => (h * E w - E w * h) (s y)) := by
    ext w
    change (h * K w - K w * h) (s y) =
      (h * K' w - K' w * h) (s y) + (h * E w - E w * h) (s y)
    simp only [hK, mul_add, add_mul, sub_apply, add_apply]
    abel
  rw [he]
  exact ((norm_add_le _ _).trans
    (add_le_add hC (column_commutator_moving_error_le h s E hE y))).trans_eq (by ring)

/-- Vanishing discarded coefficients on two fixed vectors restore the
original drift bound, with arbitrarily small error along the filter. -/
theorem eventually_column_restored_drift_le (l : Filter J) (h : H →L[ℂ] H)
    (K K' E : J → ω → H →L[ℂ] H) (hK : ∀ j w, K j w = K' j w + E j w)
    (x : H) {C : ℝ}
    (hC : ∀ j, ‖WithLp.toLp 2 (fun w => (h * K' j w - K' j w * h) x)‖ ≤ C)
    (hE : Tendsto (fun j => ‖WithLp.toLp 2 (fun w => E j w x)‖) l (𝓝 0))
    (hEh : Tendsto (fun j => ‖WithLp.toLp 2 (fun w => E j w (h x))‖) l (𝓝 0)) :
    ∀ ε > 0, ∀ᶠ j in l,
      ‖WithLp.toLp 2 (fun w => (h * K j w - K j w * h) x)‖ ≤ C + ε := by
  have he : Tendsto (fun j => ‖h‖ * ‖WithLp.toLp 2 (fun w => E j w x)‖ +
      ‖WithLp.toLp 2 (fun w => E j w (h x))‖) l (𝓝 0) := by
    simpa only [mul_zero, add_zero] using (tendsto_const_nhds.mul hE).add hEh
  intro ε hε
  filter_upwards [he.eventually (gt_mem_nhds hε)] with j hj
  have hb := column_restored_drift_le h (K j) (K' j) (E j) (hK j) x (hC j)
  linarith

/-- The moving-vector restoration costs the prescribed commutator bound
`D`, without a factor depending on the number of coefficients. -/
theorem eventually_column_restored_moving_drift_le (l : Filter J)
    (h : H →L[ℂ] H) (s : J → H →L[ℂ] H)
    (K K' E : J → ω → H →L[ℂ] H) (hK : ∀ j w, K j w = K' j w + E j w)
    (hEcontract : ∀ j z, ‖WithLp.toLp 2 (fun w => E j w z)‖ ≤ ‖z‖)
    (y : H) {C D : ℝ}
    (hC : ∀ j, ‖WithLp.toLp 2 (fun w => (h * K' j w - K' j w * h) (s j y))‖ ≤ C)
    (hD : ∀ j, ‖(h * s j - s j * h) y‖ ≤ D)
    (hEs : Tendsto (fun j => ‖WithLp.toLp 2 (fun w => E j w (s j y))‖) l (𝓝 0))
    (hEsh : Tendsto (fun j => ‖WithLp.toLp 2 (fun w => E j w (s j (h y)))‖) l (𝓝 0)) :
    ∀ ε > 0, ∀ᶠ j in l,
      ‖WithLp.toLp 2 (fun w => (h * K j w - K j w * h) (s j y))‖ ≤ C + D + ε := by
  have he : Tendsto (fun j => ‖h‖ * ‖WithLp.toLp 2 (fun w => E j w (s j y))‖ +
      ‖WithLp.toLp 2 (fun w => E j w (s j (h y)))‖) l (𝓝 0) := by
    simpa only [mul_zero, add_zero] using (tendsto_const_nhds.mul hEs).add hEsh
  intro ε hε
  filter_upwards [he.eventually (gt_mem_nhds hε)] with j hj
  have hb := column_restored_moving_drift_le h (s j) (K j) (K' j) (E j)
    (hK j) (hEcontract j) y (hC j)
  have hs := hD j
  linarith

end

end KadisonKastler

end OAI
