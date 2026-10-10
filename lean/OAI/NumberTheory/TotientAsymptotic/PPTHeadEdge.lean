import OAI.NumberTheory.TotientAsymptotic.PPTNormalizedParameters
import OAI.NumberTheory.TotientAsymptotic.NormalPrimeBands

namespace OAI

/-!
A single lower endpoint for all leading prime factors in a local PPT
comparison block.  It depends only on the comparison scale, so the
finite grid count does not require any continuously varying labels.
-/

noncomputable section
open scoped Topology
open Filter

namespace TotientAsymptotic

def pptUniformHeadEdge (t : ℝ) : ℝ := 1-(2+Real.log (3*t))/t

/-- Every normal large head lies above the same normalized endpoint.
The hypotheses are local to `z`, including the normality cutoff. -/
theorem ppt_normal_head_uniform_edge : ∀ᶠ z : ℝ in atTop,
    ∀ (p : ℕ) (S : ℝ), 1 < S → 0 ≤ B S → S ≤ z →
      IsNormalPrime S p → z^(9/10 : ℝ) ≤ p → (p-1 : ℕ) ≤ z →
      pptUniformHeadEdge (B z) ≤ B (largestPrimeFactor (p-1))/B z ∧
      B (largestPrimeFactor (p-1))/B z ≤ 1 := by
  filter_upwards [eventually_gt_atTop (1 : ℝ),
    B_tendsto.eventually (eventually_gt_atTop (0 : ℝ)),
    (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 9/10)).eventually
      (eventually_gt_atTop (2 : ℝ))] with z hz hB hpow
  intro p S hS hBS hSz hp hhead hsize
  have hp3 : 3 ≤ p := by
    have hh : (2 : ℝ) < p := hpow.trans_le hhead
    exact_mod_cast hh
  have hp1 : (1 : ℝ) < (p-1 : ℕ) := by
    exact_mod_cast (show 1 < p-1 by omega)
  have hpred : B (p-1 : ℕ) ≤ B z :=
    Real.log_le_log (Real.log_pos hp1)
      (Real.log_le_log (zero_lt_one.trans hp1) hsize)
  have hBSz : B S ≤ B z := Real.log_le_log (Real.log_pos hS)
    (Real.log_le_log (zero_lt_one.trans hS) hSz)
  have hband := normal_prime_largest_band hp hp3 hS hBS hBSz hB hpred
    (le_refl (B p)) (le_refl (B p))
  have hlog := Real.log_le_log (Real.rpow_pos_of_pos (zero_lt_one.trans hz) _) hhead
  rw [Real.log_rpow (zero_lt_one.trans hz)] at hlog
  have hdouble := Real.log_le_log
    (mul_pos (by norm_num : (0 : ℝ) < 9/10) (Real.log_pos hz)) hlog
  rw [Real.log_mul (by norm_num : (9/10 : ℝ) ≠ 0) (Real.log_pos hz).ne'] at hdouble
  change Real.log (9/10 : ℝ)+B z ≤ B p at hdouble
  have hlogfrac : -1 ≤ Real.log (9/10 : ℝ) := by
    have hh := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 9/10)
    norm_num only [inv_div, div_self] at hh
    linarith only [hh]
  have hlower : B z-(2+Real.log (3*B z)) ≤ B (largestPrimeFactor (p-1)) := by
    linarith only [hband.1, hdouble, hlogfrac]
  constructor
  · apply (le_div_iff₀ hB).mpr
    unfold pptUniformHeadEdge
    calc
      (1-(2+Real.log (3*B z))/B z)*B z = B z-(2+Real.log (3*B z)) := by
        rw [sub_mul, one_mul, div_mul_cancel₀ _ hB.ne']
      _ ≤ _ := hlower
  · apply (div_le_one hB).mpr
    have hlp : (1 : ℝ) < largestPrimeFactor (p-1) := by
      exact_mod_cast one_lt_largestPrimeFactor (show 2 ≤ p-1 by omega)
    apply Real.log_le_log (Real.log_pos hlp)
    apply Real.log_le_log (zero_lt_one.trans hlp)
    exact (Nat.cast_le.mpr (largestPrimeFactor_le_self (by omega))).trans hsize

lemma ppt_uniform_head_edge_lt_one {t : ℝ} (ht : 1 ≤ t) :
    pptUniformHeadEdge t < 1 := by
  have ht0 : 0 < t := zero_lt_one.trans_le ht
  have hlog : 0 ≤ Real.log (3*t) := Real.log_nonneg (by linarith)
  have herror : 0 < (2+Real.log (3*t))/t := div_pos (by linarith) ht0
  unfold pptUniformHeadEdge
  linarith only [herror]

/-- Only the left head needs a large-prime size estimate.  Alignment
places both heads above one common endpoint without imposing that size
estimate separately on the arbitrary right preimage. -/
lemma ppt_aligned_heads_uniform_edge {t u v η : ℝ}
    (ht : 1 ≤ t) (hu : pptUniformHeadEdge t ≤ u) (halign : |u-v| ≤ η) :
    pptUniformHeadEdge t-η ≤ min u v ∧ pptUniformHeadEdge t-η < 1 := by
  have hη : 0 ≤ η := (abs_nonneg _).trans halign
  constructor
  · exact le_min (by linarith only [hu, hη])
      (by linarith only [hu, (abs_le.mp halign).2])
  · have hh := ppt_uniform_head_edge_lt_one ht
    linarith only [hh, hη]

/-- The uniform head loss is smaller than every fixed inverse-log-cube
margin, so the same lower edge works for every pair in a grid class. -/
theorem ppt_first_cutoff_below_uniform_head {γ : ℝ} (hγ : 0 < γ) :
    ∀ᶠ t : ℝ in atTop, ∀ ν : ℝ,
      ν ≤ 1-γ/(Real.log t)^3 → ν < pptUniformHeadEdge t := by
  have h₃ : Tendsto (fun t : ℝ => (Real.log t)^3/t) atTop (𝓝 0) :=
    Real.isLittleO_pow_log_id_atTop.tendsto_div_nhds_zero
  have h₄ : Tendsto (fun t : ℝ => (Real.log t)^4/t) atTop (𝓝 0) :=
    Real.isLittleO_pow_log_id_atTop.tendsto_div_nhds_zero
  have hsum : Tendsto (fun t : ℝ =>
      (2+Real.log 3)*((Real.log t)^3/t)+(Real.log t)^4/t) atTop (𝓝 0) := by
    simpa only [mul_zero, zero_add] using (h₃.const_mul (2+Real.log 3)).add h₄
  filter_upwards [hsum.eventually (eventually_lt_nhds hγ),
    eventually_gt_atTop (1 : ℝ)] with t hsmall ht
  intro ν hν
  have ht0 : 0 < t := zero_lt_one.trans ht
  have hlog : 0 < Real.log t := Real.log_pos ht
  have heq : (2+Real.log (3*t))*(Real.log t)^3/t =
      (2+Real.log 3)*((Real.log t)^3/t)+(Real.log t)^4/t := by
    rw [Real.log_mul (by norm_num : (3 : ℝ) ≠ 0) ht0.ne']
    ring
  rw [← heq] at hsmall
  have hm := (div_lt_iff₀ ht0).mp hsmall
  have hloss : (2+Real.log (3*t))/t < γ/(Real.log t)^3 :=
    (div_lt_div_iff₀ ht0 (pow_pos hlog 3)).mpr hm
  unfold pptUniformHeadEdge
  linarith only [hν, hloss]

/-- The same head endpoint still lies above the first cutoff after the
uniform alignment allowance used by the doubled PPT mesh. -/
theorem ppt_first_cutoff_below_aligned_head {γ : ℝ} (hγ : 0 < γ) :
    ∀ᶠ t : ℝ in atTop, ∀ ν η : ℝ,
      ν ≤ 1-γ/(Real.log t)^3 →
      η ≤ 2*((Real.log t)^5/Real.sqrt t) →
      ν < pptUniformHeadEdge t-η := by
  have hlim : Tendsto (fun t : ℝ => 2*((Real.log t)^8/Real.sqrt t))
      atTop (𝓝 0) := by
    have hh : Tendsto (fun t : ℝ => (Real.log t)^8/Real.sqrt t)
        atTop (𝓝 0) := by
      simpa only [Real.sqrt_eq_rpow, Real.rpow_natCast] using
        (isLittleO_log_rpow_rpow_atTop (8 : ℕ)
          (show (0 : ℝ) < 1/2 by norm_num)).tendsto_div_nhds_zero
    simpa only [mul_zero] using hh.const_mul 2
  filter_upwards [ppt_first_cutoff_below_uniform_head (show 0 < γ/2 by positivity),
    hlim.eventually (eventually_lt_nhds (show (0 : ℝ) < γ/2 by positivity)),
    eventually_gt_atTop (1 : ℝ)] with t hhead hsmall ht
  intro ν η hν hη
  have hlog : 0 < Real.log t := Real.log_pos ht
  have hhead' := hhead (1-(γ/2)/(Real.log t)^3) le_rfl
  have hmesh : 2*((Real.log t)^5/Real.sqrt t) < (γ/2)/(Real.log t)^3 := by
    apply (lt_div_iff₀ (pow_pos hlog 3)).mpr
    convert hsmall using 1
    ring
  have hη' := hη.trans_lt hmesh
  have he : γ/(Real.log t)^3 = (γ/2)/(Real.log t)^3+(γ/2)/(Real.log t)^3 := by
    ring
  rw [he] at hν
  linarith only [hν, hhead', hη']

end TotientAsymptotic

end

end OAI
