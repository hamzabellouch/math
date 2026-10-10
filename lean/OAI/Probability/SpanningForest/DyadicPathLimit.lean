import OAI.Probability.SpanningForest.DyadicInterpolation
import OAI.Probability.SpanningForest.ContinuousPathLimit

namespace OAI

noncomputable section

namespace Problem336.DyadicPathLimit

open Filter MeasureTheory ProbabilityTheory
open scoped Topology BigOperators
open DyadicInterpolation

def unitApprox (x : ℝ → ℝ) (n : ℕ) : C(unitInterval, ℝ) :=
  ⟨fun t => approx x n t, (continuous_approx x n).comp continuous_subtype_val⟩

@[simp] theorem unitApprox_apply (x : ℝ → ℝ) (n : ℕ) (t : unitInterval) :
    unitApprox x n t = approx x n t := rfl

def unitPath (x : ℝ → ℝ) : C(unitInterval, ℝ) :=
  ContinuousPathLimit.pathLimit (unitApprox x)

theorem approx_grid_add (x : ℝ → ℝ) (n j : ℕ) (hj : j ≤ 2 ^ n) (r : ℕ) :
    approx x (n + r) (grid n j) = x (grid n j) := by
  induction r with
  | zero => simpa using approx_grid x n j hj
  | succ r ih =>
      rw [Nat.add_succ, approx_succ, ih]
      have hz := SchauderTents.level_prior_grid_zero n r j (coefficient x (n + r))
      change SchauderTents.level (n + r) (coefficient x (n + r)) (grid n j) = 0 at hz
      rw [hz, add_zero]

theorem eventually_unitApprox_grid (x : ℝ → ℝ) (n j : ℕ) (hj : j ≤ 2 ^ n)
    (t : unitInterval) (ht : (t : ℝ) = grid n j) :
    ∀ᶠ m in atTop, unitApprox x m t = x t := by
  filter_upwards [eventually_ge_atTop n] with m hm
  obtain ⟨r, rfl⟩ := Nat.exists_eq_add_of_le hm
  simpa only [unitApprox_apply, ht] using approx_grid_add x n j hj r

theorem dist_unitApprox_succ_le (x : ℝ → ℝ) (n : ℕ) {D : ℝ} (hD : 0 ≤ D)
    (hinc : ∀ j < 2 ^ (n + 1),
      |x (grid (n + 1) (j + 1)) - x (grid (n + 1) j)| ≤ D) :
    dist (unitApprox x n) (unitApprox x (n + 1)) ≤ D := by
  apply (ContinuousMap.dist_le hD).mpr
  intro t
  rw [dist_comm, Real.dist_eq]
  exact abs_approx_succ_sub_le x n hD hinc t

theorem tendsto_unitPath (x : ℝ → ℝ) (d : ℕ → ℝ)
    (hd0 : ∀ n, 0 ≤ d n) (hd : Summable d)
    (hinc : ∀ᶠ n in atTop, ∀ j < 2 ^ (n + 1),
      |x (grid (n + 1) (j + 1)) - x (grid (n + 1) j)| ≤ d n) :
    Tendsto (unitApprox x) atTop (𝓝 (unitPath x)) := by
  exact ContinuousPathLimit.tendsto_pathLimit_of_eventually_summable d
    (hinc.mono fun n hn => dist_unitApprox_succ_le x n (hd0 n) hn) hd

theorem unitPath_grid (x : ℝ → ℝ) (d : ℕ → ℝ)
    (hd0 : ∀ n, 0 ≤ d n) (hd : Summable d)
    (hinc : ∀ᶠ n in atTop, ∀ j < 2 ^ (n + 1),
      |x (grid (n + 1) (j + 1)) - x (grid (n + 1) j)| ≤ d n)
    (n j : ℕ) (hj : j ≤ 2 ^ n) (t : unitInterval) (ht : (t : ℝ) = grid n j) :
    unitPath x t = x t := by
  exact tendsto_nhds_unique
    ((continuous_eval_const t).continuousAt.tendsto.comp (tendsto_unitPath x d hd0 hd hinc))
    (tendsto_const_nhds.congr' ((eventually_unitApprox_grid x n j hj t ht).mono (fun _ h => h.symm)))

section EvaluationLaws

variable {Ω ι : Type*} [MeasurableSpace Ω] {P : Measure Ω}

theorem ae_unitPath_grid (x : Ω → ℝ → ℝ) (d : ℕ → ℝ)
    (hd0 : ∀ n, 0 ≤ d n) (hd : Summable d)
    (hinc : ∀ᵐ ω ∂P, ∀ᶠ n in atTop, ∀ j < 2 ^ (n + 1),
      |x ω (grid (n + 1) (j + 1)) - x ω (grid (n + 1) j)| ≤ d n)
    (times : ι → unitInterval)
    (hgrid : ∀ i, ∃ n j, j ≤ 2 ^ n ∧ (times i : ℝ) = grid n j) :
    ∀ᵐ ω ∂P, ∀ i, unitPath (x ω) (times i) = x ω (times i) := by
  filter_upwards [hinc] with ω hω
  intro i
  obtain ⟨n, j, hj, ht⟩ := hgrid i
  exact unitPath_grid (x ω) d hd0 hd hω n j hj (times i) ht

theorem hasLaw_unitPath_grid (x : Ω → ℝ → ℝ) (d : ℕ → ℝ)
    (hd0 : ∀ n, 0 ≤ d n) (hd : Summable d)
    (hinc : ∀ᵐ ω ∂P, ∀ᶠ n in atTop, ∀ j < 2 ^ (n + 1),
      |x ω (grid (n + 1) (j + 1)) - x ω (grid (n + 1) j)| ≤ d n)
    (times : ι → unitInterval)
    (hgrid : ∀ i, ∃ n j, j ≤ 2 ^ n ∧ (times i : ℝ) = grid n j)
    (μ : Measure (ι → ℝ)) (ha : HasLaw (fun ω i => x ω (times i)) μ P) :
    HasLaw (fun ω i => unitPath (x ω) (times i)) μ P := by
  apply ha.congr
  filter_upwards [ae_unitPath_grid x d hd0 hd hinc times hgrid] with ω hω
  exact funext hω

end EvaluationLaws

variable {Ω : Type*} [MeasurableSpace Ω]
variable [MeasurableSpace C(unitInterval, ℝ)] [BorelSpace C(unitInterval, ℝ)]

theorem measurable_unitApprox (x : Ω → ℝ → ℝ)
    (hx : ∀ t, Measurable (fun ω => x ω t)) (n : ℕ) :
    Measurable (fun ω => unitApprox (x ω) n) := by
  let coordinate : C(unitInterval, ℝ) := ⟨Subtype.val, continuous_subtype_val⟩
  let tentPath (m k : ℕ) : C(unitInterval, ℝ) :=
    ⟨fun t => SchauderTents.tent m k t,
      (SchauderTents.continuous_tent m k).comp continuous_subtype_val⟩
  have hc : Continuous (ContinuousMap.const unitInterval : ℝ → C(unitInterval, ℝ)) :=
    ContinuousMap.continuous_of_continuous_uncurry _ continuous_fst
  have heq : (fun ω => unitApprox (x ω) n) = fun ω =>
      ContinuousMap.const unitInterval (x ω 0) + (x ω 1 - x ω 0) • coordinate +
        ∑ m ∈ Finset.range n, ∑ k ∈ Finset.range (2 ^ m),
          coefficient (x ω) m k • tentPath m k := by
    funext ω
    ext t
    simp [unitApprox, approx, SchauderTents.level, coordinate, tentPath]
  rw [heq]
  apply Measurable.add
  · exact (hc.measurable.comp (hx 0)).add (((hx 1).sub (hx 0)).smul measurable_const)
  · apply Finset.measurable_sum
    intro m hm
    apply Finset.measurable_sum
    intro k hk
    exact (measurable_coefficient x hx m k).smul measurable_const

theorem measurable_unitPath (x : Ω → ℝ → ℝ)
    (hx : ∀ t, Measurable (fun ω => x ω t)) :
    Measurable (fun ω => unitPath (x ω)) :=
  ContinuousPathLimit.measurable_pathLimit (fun n ω => unitApprox (x ω) n)
    (measurable_unitApprox x hx)

end Problem336.DyadicPathLimit

end

end OAI
