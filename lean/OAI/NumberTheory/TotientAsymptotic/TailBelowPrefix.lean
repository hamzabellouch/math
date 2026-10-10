import OAI.NumberTheory.TotientAsymptotic.CofactorShellDecay
import OAI.NumberTheory.TotientAsymptotic.SuffixSize
import OAI.NumberTheory.TotientAsymptotic.CollisionIndices

namespace OAI

noncomputable section
open scoped Topology
open Filter

namespace TotientAsymptotic

lemma tail_log_comparison : ∀ᶠ b : ℝ in atTop,
    4*b*Real.exp ((7/10 : ℝ)*b) < Real.exp ((9/10 : ℝ)*b) := by
  have ht : Tendsto (fun b : ℝ => 4*(b*Real.exp (-(1/5 : ℝ)*b))) atTop (nhds 0) := by
    simpa only [Real.rpow_one,mul_zero] using
      (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 1 (1/5) (by norm_num : (0 : ℝ)<1/5)).const_mul 4
  filter_upwards [ht.eventually (eventually_lt_nhds (by norm_num : (0 : ℝ)<1))] with b hb
  have h := mul_lt_mul_of_pos_right hb (Real.exp_pos ((9/10 : ℝ)*b))
  rw [mul_assoc,mul_assoc,← Real.exp_add] at h
  rw [show -(1/5 : ℝ)*b+9/10*b=(7/10 : ℝ)*b by ring,one_mul] at h
  simpa only [mul_assoc] using h

/-- The exact arithmetic tail lies below every retained prefix prime. This is
uniform in the phase; the cofactor cut grows much slower than the prefix cut. -/
theorem basic_tail_lt_last_prefix : ∀ᶠ H : ℕ in atTop,
    ∀ x : ℝ, theta x ∈ Set.Ico (0 : ℝ) 1 → H < m x →
    ∀ η : RemainderDatum (L x H), IsBasicRemainder x H η →
      remainderTail x H η < remainderPrime η (R x H) := by
  obtain ⟨b₀,hb₀⟩ := eventually_atTop.mp tail_log_comparison
  filter_upwards [eventually_ge_atTop 2,
    P_tendsto.eventually (eventually_ge_atTop 1),
    cofactor_envelope_le_self (2*(lam/rho)),
    (tendsto_natCast_atTop_atTop.const_mul_atTop lam_pos).eventually (eventually_ge_atTop b₀)]
    with H hH hP hcof hlarge
  intro x hs hm η hη
  have hPH := P_lt_self hH
  have hR : 0 < R x H := by unfold R; omega
  have hRL : R x H < L x H := by unfold R L; omega
  have hRmem : R x H ∈ Finset.Icc 1 (L x H) := Finset.mem_Icc.mpr ⟨hR,hRL.le⟩
  have hRH : m x-R x H=H := by unfold R; omega
  have hLP : m x-L x H=P H := by unfold L; omega
  let b := bandScale x (R x H)
  have hb0 : 0 ≤ b := bandScale_nonnegative _ _
  have hα : lam ≤ alpha (theta x) := by
    unfold alpha
    exact le_mul_of_one_le_right lam_pos.le (Real.one_le_exp (mul_nonneg lam_pos.le hs.1))
  have hpow : (1 : ℝ) ≤ (rho^H)⁻¹ := one_le_inv₀ (pow_pos rho_pos H) |>.mpr
    (pow_le_one₀ rho_pos.le rho_lt_one.le)
  have hbH : lam*H ≤ b := by
    change _ ≤ alpha (theta x)*(m x-R x H : ℕ)*(rho^(m x-R x H))⁻¹
    rw [hRH]
    exact (mul_le_mul_of_nonneg_right hα (Nat.cast_nonneg H)).trans
      (le_mul_of_one_le_right (mul_nonneg (alpha_pos _).le (Nat.cast_nonneg _)) hpow)
  have hHb : (H : ℝ) ≤ 2*b := by
    have hl := collision_lambda_bounds.1
    nlinarith [Nat.cast_nonneg (α := ℝ) H]
  have hsuc : (11/10 : ℝ)*bandScale x (R x H+1) ≤ (7/10 : ℝ)*b := by
    have hh := bandScale_succ_le x (R x H)
    have hr := collision_rho_bounds.2
    change bandScale x (R x H+1) ≤ rho*b at hh
    nlinarith
  have hlast : Real.exp (2*bandScale x (L x H)) ≤ H := by
    apply (Real.exp_le_exp.mpr ?_).trans hcof
    rw [bandScale,hLP]
    unfold cofactorScale
    have hi := (inv_pos.mpr (pow_pos rho_pos (P H))).le
    have ha := alpha_le _ hs
    nlinarith [mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right ha (Nat.cast_nonneg (P H))) hi]
  have hlen : L x H-R x H ≤ H := by unfold L R; omega
  have hlenR : (L x H-R x H : ℕ) ≤ (H : ℝ) := by exact_mod_cast hlen
  have he : (1 : ℝ) ≤ Real.exp ((7/10 : ℝ)*b) := Real.one_le_exp (by positivity)
  have hlog := basic_suffix_log_bound (j := R x H) hη
  have hu : Real.log (remainderTail x H η : ℝ) < Real.exp ((9/10 : ℝ)*b) := by
    change Real.log (suffixPreimage η (R x H) : ℝ) < _
    calc
      _ ≤ (H : ℝ)*Real.exp ((7/10 : ℝ)*b)+H := hlog.trans
        (add_le_add (mul_le_mul hlenR (Real.exp_le_exp.mpr hsuc) (Real.exp_pos _).le (Nat.cast_nonneg _)) hlast)
      _ ≤ 4*b*Real.exp ((7/10 : ℝ)*b) := by nlinarith
      _ < _ := hb₀ b (hlarge.trans hbH)
  have hp := hη.2.1 _ hRmem
  have hpR : (1 : ℝ) < remainderPrime η (R x H) := by exact_mod_cast hp.1.one_lt
  have hlower : Real.exp ((9/10 : ℝ)*b) ≤ Real.log (remainderPrime η (R x H) : ℝ) := by
    apply (Real.le_log_iff_exp_le (Real.log_pos hpR)).mp
    simpa only [remainderCoord,ite_eq_right (ne_of_gt hR)] using hp.2.1
  have hpos : (0 : ℝ) < remainderTail x H η := by
    exact_mod_cast suffixPreimage_pos (i := R x H) hη
  exact_mod_cast (Real.log_lt_log_iff hpos (zero_lt_one.trans hpR)).mp (hu.trans_le hlower)

end TotientAsymptotic

end

end OAI
