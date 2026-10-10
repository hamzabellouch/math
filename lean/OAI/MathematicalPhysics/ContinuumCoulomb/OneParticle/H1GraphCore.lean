import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.CompactSobolevCore

namespace OAI

/-! The full weak-H1 graph as finitely many actual L2 coordinates. Compact
C1 states approximate every coordinate simultaneously, so continuous form
inequalities on this graph extend to the full weak-H1 domain. -/

noncomputable section
open MeasureTheory Filter
open scoped Topology BigOperators
namespace ContinuumCoulomb

abbrev H1Index (n : ℕ) := SpinConfiguration n ⊕ (SpinConfiguration n × (Fin n × Fin 3))

def h1CoordinateFunction {n : ℕ} (u : Coulomb.H1Vector n) :
    H1Index n → Configuration n → ℂ
  | Sum.inl s => u.value s
  | Sum.inr (s, a) => u.gradient s a

theorem h1Coordinate_memLp {n : ℕ} (u : Coulomb.H1Vector n) (a : H1Index n) :
    MemLp (h1CoordinateFunction u a) 2 := by
  cases a with
  | inl s => exact u.value_L2 s
  | inr sa => exact u.partial_L2 sa.1 sa.2

def h1Coordinates {n : ℕ} (u : Coulomb.H1Vector n) :
    H1Index n → Lp ℂ 2 (volume : Measure (Configuration n)) :=
  fun a => (h1Coordinate_memLp u a).toLp (h1CoordinateFunction u a)

theorem h1Coordinate_error {n : ℕ} (u v : Coulomb.H1Vector n) (a : H1Index n) :
    ‖h1Coordinates u a-h1Coordinates v a‖^2 =
      ∫ x, ‖h1CoordinateFunction u a x-h1CoordinateFunction v a x‖^2 := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [Lp.coeFn_sub (h1Coordinates u a) (h1Coordinates v a),
    (h1Coordinate_memLp u a).coeFn_toLp, (h1Coordinate_memLp v a).coeFn_toLp]
    with x hs hu hv
  rw [real_inner_self_eq_norm_sq]
  change ‖(h1Coordinates u a-h1Coordinates v a) x‖^2 = _
  rw [hs]
  change ‖h1Coordinates u a x-h1Coordinates v a x‖^2 = _
  change h1Coordinates u a x = h1CoordinateFunction u a x at hu
  change h1Coordinates v a x = h1CoordinateFunction v a x at hv
  rw [hu, hv]

theorem h1GraphError_eq_sum {n : ℕ} (u v : Coulomb.H1Vector n) :
    h1GraphError u v = ∑ a : H1Index n, ‖h1Coordinates u a-h1Coordinates v a‖^2 := by
  simp only [h1Coordinate_error, Fintype.sum_sum_type, Fintype.sum_prod_type,
    h1CoordinateFunction, h1GraphError]

theorem h1Coordinate_error_le {n : ℕ} (u v : Coulomb.H1Vector n) (a : H1Index n) :
    ‖h1Coordinates u a-h1Coordinates v a‖^2 ≤ h1GraphError u v := by
  rw [h1GraphError_eq_sum]
  exact Finset.single_le_sum (fun (i : H1Index n) _ =>
    sq_nonneg ‖h1Coordinates u i-h1Coordinates v i‖) (Finset.mem_univ a)

/-- Compact C1 states converge to every actual weak-H1 state in the finite
product of value and derivative L2 spaces. -/
theorem exists_compact_h1_graph_sequence (hpublished : PublishedSobolevSmoothDensity)
    {n : ℕ} (u : Coulomb.H1Vector n) :
    ∃ v : ℕ → Coulomb.H1Vector n,
      (∀ k s, ContDiff ℝ 1 ((v k).value s) ∧ HasCompactSupport ((v k).value s)) ∧
      (∀ k s a x, (v k).gradient s a x =
        fderiv ℝ ((v k).value s) x (EuclideanSpace.single a 1)) ∧
      Tendsto (fun k => h1Coordinates (v k)) atTop (𝓝 (h1Coordinates u)) := by
  have he (k : ℕ) := exists_compact_h1_approximation hpublished u
    (show (0 : ℝ) < 1/((k : ℝ)+1) by positivity)
  choose v hv hd herr using he
  refine ⟨v, hv, hd, ?_⟩
  apply tendsto_pi_nhds.2
  intro a
  rw [tendsto_iff_dist_tendsto_zero]
  have hs : Tendsto (fun k => ‖h1Coordinates (v k) a-h1Coordinates u a‖^2)
      atTop (𝓝 0) := by
    apply squeeze_zero (fun k => sq_nonneg _) _
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
    intro k
    rw [norm_sub_rev]
    exact (h1Coordinate_error_le u (v k) a).trans (herr k).le
  have ht := (Real.continuous_sqrt.tendsto 0).comp hs
  simpa only [Function.comp_def, Real.sqrt_sq (norm_nonneg _), Real.sqrt_zero,
    dist_eq_norm] using ht

/-- Transfer a continuous inequality from compact classical states to the
full declared weak-H1 graph. -/
theorem h1_continuous_nonnegative_of_compact
    (hpublished : PublishedSobolevSmoothDensity) {n : ℕ}
    (F : (H1Index n → Lp ℂ 2 (volume : Measure (Configuration n))) → ℝ)
    (hF : Continuous F)
    (hcompact : ∀ v : Coulomb.H1Vector n,
      (∀ s, ContDiff ℝ 1 (v.value s) ∧ HasCompactSupport (v.value s)) →
      (∀ s a x, v.gradient s a x =
        fderiv ℝ (v.value s) x (EuclideanSpace.single a 1)) → 0 ≤ F (h1Coordinates v))
    (u : Coulomb.H1Vector n) : 0 ≤ F (h1Coordinates u) := by
  obtain ⟨v, hv, hd, ht⟩ := exists_compact_h1_graph_sequence hpublished u
  exact ge_of_tendsto (hF.continuousAt.tendsto.comp ht)
    (Filter.Eventually.of_forall (fun k => hcompact (v k) (hv k) (hd k)))

end ContinuumCoulomb

end

end OAI
