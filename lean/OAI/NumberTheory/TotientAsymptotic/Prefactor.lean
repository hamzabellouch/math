import OAI.NumberTheory.TotientAsymptotic.TailPower

namespace OAI

/-! The finite-tail prefactor, including its dependence on the moving phase. -/

noncomputable section
open scoped BigOperators Topology
open Filter

namespace TotientAsymptotic

lemma G_step {x : ℝ} (hB : 0 < B x) (j : ℕ) :
    G x j = ((j+1 : ℝ)*g (j+1)/B x)*G x (j+1) := by
  have hp : (∏ i ∈ Finset.Icc 1 j, g i) ≠ 0 :=
    (Finset.prod_pos (fun i _ => g_pos i)).ne'
  have hf : (j.factorial : ℝ) ≠ 0 := by exact_mod_cast (Nat.factorial_ne_zero j)
  have hj : (j+1 : ℝ) ≠ 0 := by positivity
  unfold G
  rw [Finset.prod_Icc_succ_top (by omega), Nat.factorial_succ, Nat.cast_mul,
    Nat.cast_add, Nat.cast_one, pow_succ]
  field_simp [hB.ne', hp, hf, hj, (g_pos (j+1)).ne']

lemma G_sub_eq_product {x : ℝ} (hB : 0 < B x) (n H : ℕ) (hH : H ≤ n) :
    G x (n-H) = G x n *
      ∏ k ∈ Finset.range H, ((n-k : ℕ) : ℝ)*g (n-k)/B x := by
  induction H with
  | zero => simp
  | succ H ih =>
    have hH' : H ≤ n := by omega
    have hidx : n-(H+1)+1 = n-H := by omega
    have hcast : ((n-(H+1) : ℕ) : ℝ)+1 = ((n-H : ℕ) : ℝ) := by
      exact_mod_cast hidx
    rw [G_step hB (n-(H+1)), hidx, ih hH', Finset.prod_range_succ]
    rw [hcast]
    ring

lemma sub_div_self_tendsto (k : ℕ) :
    Tendsto (fun x : ℝ => ((m x-k : ℕ) : ℝ)/(m x : ℝ)) atTop (nhds 1) := by
  have hi : Tendsto (fun x : ℝ => (m x : ℝ)⁻¹) atTop (nhds 0) :=
    tendsto_inv_atTop_zero.comp (tendsto_natCast_atTop_atTop.comp m_tendsto)
  have hh : Tendsto (fun x : ℝ => 1-(k : ℝ)*(m x : ℝ)⁻¹) atTop (nhds 1) := by
    simpa using tendsto_const_nhds.sub (hi.const_mul (k : ℝ))
  apply hh.congr'
  filter_upwards [m_tendsto.eventually (eventually_ge_atTop k),
    m_tendsto.eventually (eventually_gt_atTop 0)] with x hk hm
  rw [Nat.cast_sub hk]
  field_simp [show (m x : ℝ) ≠ 0 from Nat.cast_ne_zero.mpr hm.ne']

lemma normalized_prefactor_step (hford : FordRenewalInput) (k : ℕ) :
    Tendsto (fun x : ℝ => alpha (theta x) *
      (((m x-k : ℕ) : ℝ)*g (m x-k)/B x)) atTop (nhds (gamma*rho^k)) := by
  have hn := (normalizedRenewal_properties hford).1.comp
    ((tendsto_sub_atTop_nat k).comp m_tendsto)
  have hh := (((sub_div_self_tendsto k).mul hn).mul_const (rho^k)).div
    bandCenterRatio_tendsto (by norm_num : (1 : ℝ) ≠ 0)
  simp only [one_mul, div_one] at hh
  apply hh.congr'
  filter_upwards [B_tendsto.eventually (eventually_gt_atTop (1 : ℝ)),
    m_tendsto.eventually (eventually_ge_atTop k),
    m_tendsto.eventually (eventually_gt_atTop 0)] with x hB hk hm
  have hpow : rho^(m x-k)*rho^k = rho^(m x) := by
    rw [← pow_add, Nat.sub_add_cancel hk]
  change (((m x-k : ℕ) : ℝ)/(m x : ℝ) * normalizedRenewal (m x-k) * rho^k) /
      bandCenterRatio x = alpha (theta x) * (((m x-k : ℕ) : ℝ)*g (m x-k)/B x)
  rw [alpha_theta_eq hB]
  unfold normalizedRenewal bandCenterRatio
  have hmn : (m x : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hm.ne'
  have hl : Real.log (B x) ≠ 0 := (Real.log_pos hB).ne'
  field_simp [hmn, hl, lam_pos.ne', (zero_lt_one.trans hB).ne']
  rw [← hpow]
  ring

lemma normalized_prefactor_limit (hford : FordRenewalInput) (H : ℕ) :
    Tendsto (fun x : ℝ => alpha (theta x)^H * G x (R x H)/G x (m x))
      atTop (nhds (rho^(H*(H-1)/2)*gamma^H)) := by
  have hh := tendsto_finsetProd (Finset.range H)
    (fun k _ => normalized_prefactor_step hford k)
  have hp : (∏ k ∈ Finset.range H, gamma*rho^k) = rho^(H*(H-1)/2)*gamma^H := by
    rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_range,
      Finset.prod_pow_eq_pow_sum, Finset.sum_range_id]
    ring
  rw [hp] at hh
  apply hh.congr'
  filter_upwards [m_tendsto.eventually (eventually_ge_atTop H),
    B_tendsto.eventually (eventually_gt_atTop (0 : ℝ))] with x hm hB
  rw [show R x H = m x-H from rfl, G_sub_eq_product hB (m x) H hm,
    Finset.prod_mul_distrib, Finset.prod_const, Finset.card_range]
  field_simp [(G_pos hB (m x)).ne']

/-- The prefactor in the exact intersection volume has the finite-tail limit
specified in the manuscript, even though the phase itself need not converge. -/
theorem prefactor_error (hford : FordRenewalInput) (H : ℕ) :
    Tendsto (fun x : ℝ => G x (R x H)/G x (m x) -
      rho^(H*(H-1)/2)*(gamma/alpha (theta x))^H) atTop (nhds 0) := by
  have hh := phase_division_error
    (fun x : ℝ => alpha (theta x)^H * G x (R x H)/G x (m x))
    (fun _ => 1) (fun x => alpha (theta x)^H)
    (rho^(H*(H-1)/2)*gamma^H) (lam^H) (pow_pos lam_pos H)
    (normalized_prefactor_limit hford H) tendsto_const_nhds
    (theta_eventually_mem.mono (fun _ hx =>
      pow_le_pow_left₀ lam_pos.le (alpha_ge_lam hx.1) H))
  apply hh.congr'
  exact Eventually.of_forall (fun x => by
    dsimp only
    rw [mul_one, div_pow]
    field_simp [(pow_pos (alpha_pos (theta x)) H).ne'])

end TotientAsymptotic

end

end OAI
