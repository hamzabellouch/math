import OAI.NumberTheory.TotientAsymptotic.Prefactor

namespace OAI

/-! Convergence of the actual finite-tail intersection volumes. -/

noncomputable section
open scoped BigOperators Topology
open Filter MeasureTheory

namespace TotientAsymptotic

def intersectionWeight {H : ℕ} (s : ℝ) (T : Finset (TailDatum H)) : ℝ :=
  rho^(H*(H-1)/2)*(gamma/alpha s)^H *
    Real.exp (-(gamma/alpha s) * ∑' n : ℕ, rho^(H+n)*maxD (H+n) T)

lemma normalized_intersection_expression_limit (hford : FordRenewalInput)
    {H : ℕ} {s : ℝ} (T : Finset (TailDatum H))
    (hT : ∀ η ∈ T, IsWitness H s η) :
    Tendsto (fun x : ℝ => G x (R x H)/G x (m x) *
      (max (1-tailBudget x H T/B x) 0)^(R x H) -
      intersectionWeight (theta x) T) atTop (nhds 0) := by
  let Q : ℝ → ℝ := fun x => rho^(H*(H-1)/2)*(gamma/alpha (theta x))^H
  let U : ℝ → ℝ := fun x => (max (1-tailBudget x H T/B x) 0)^(R x H)
  let E : ℝ → ℝ := fun x => Real.exp (-(gamma/alpha (theta x)) *
    ∑' n : ℕ, rho^(H+n)*maxD (H+n) T)
  let K := rho^(H*(H-1)/2)*(gamma/lam)^H
  have hQ : ∀ᶠ x : ℝ in atTop, 0 ≤ Q x ∧ Q x ≤ K := by
    filter_upwards [theta_eventually_mem] with x hx
    refine ⟨mul_nonneg (pow_nonneg rho_pos.le _)
      (pow_nonneg (div_pos gamma_pos (alpha_pos _)).le _), ?_⟩
    apply mul_le_mul_of_nonneg_left _ (pow_nonneg rho_pos.le _)
    exact pow_le_pow_left₀ (div_pos gamma_pos (alpha_pos _)).le
      (div_le_div_of_nonneg_left gamma_pos.le lam_pos (alpha_ge_lam hx.1)) H
  have hU : ∀ᶠ x : ℝ in atTop, 0 ≤ U x ∧ U x ≤ 1 := by
    filter_upwards [m_tendsto.eventually (eventually_ge_atTop H),
      B_tendsto.eventually (eventually_gt_atTop 0)] with x hm hB
    have hq := div_nonneg (tailBudget_nonneg T hT hm) hB.le
    exact ⟨pow_nonneg (le_max_right _ _) _, pow_le_one₀ (le_max_right _ _)
      (max_le (by linarith) zero_le_one)⟩
  have h₁ : Tendsto (fun x : ℝ => |G x (R x H)/G x (m x)-Q x|)
      atTop (nhds 0) := by simpa [Q] using (prefactor_error hford H).abs
  have h₂ : Tendsto (fun x : ℝ => |U x-E x|) atTop (nhds 0) := by
    simpa [U, E] using (tail_simplex_power_limit hford T hT).abs
  apply squeeze_zero_norm' (a := fun x =>
    |G x (R x H)/G x (m x)-Q x|+K*|U x-E x|)
  · filter_upwards [hQ, hU] with x hQx hUx
    change |G x (R x H)/G x (m x)*U x-Q x*E x| ≤ _
    calc
      _ = |(G x (R x H)/G x (m x)-Q x)*U x+Q x*(U x-E x)| := by
        congr 1; ring
      _ ≤ |(G x (R x H)/G x (m x)-Q x)*U x|+|Q x*(U x-E x)| := abs_add_le _ _
      _ = |G x (R x H)/G x (m x)-Q x| * U x+Q x * |U x-E x| := by
        rw [abs_mul, abs_mul, abs_of_nonneg hUx.1, abs_of_nonneg hQx.1]
      _ ≤ _ := add_le_add
        (by nlinarith [abs_nonneg (G x (R x H)/G x (m x)-Q x)])
        (mul_le_mul_of_nonneg_right hQx.2 (abs_nonneg _))
  · simpa using h₁.add (h₂.const_mul K)

/-- Each genuine intersection volume has its stated coefficient limit.
The hypothesis concerns only a fixed finite set of tail witnesses. -/
theorem normalized_intersection_volume_limit (hford : FordRenewalInput)
    {H : ℕ} {s : ℝ} (T : Finset (TailDatum H)) (hne : T.Nonempty)
    (hT : ∀ η ∈ T, IsWitness H s η) :
    Tendsto (fun x : ℝ => (volume (tailIntersection x H T)).toReal/G x (m x) -
      intersectionWeight (theta x) T) atTop (nhds 0) := by
  apply (normalized_intersection_expression_limit hford T hT).congr'
  filter_upwards [m_tendsto.eventually (eventually_gt_atTop H),
    B_tendsto.eventually (eventually_gt_atTop 0)] with x hm hB
  rw [volume_tailIntersection x H T hne (by dsimp [R]; omega) hB,
    ENNReal.toReal_ofReal (mul_nonneg (G_pos hB _).le
      (pow_nonneg (le_max_right _ _) _))]
  ring

end TotientAsymptotic

end

end OAI
