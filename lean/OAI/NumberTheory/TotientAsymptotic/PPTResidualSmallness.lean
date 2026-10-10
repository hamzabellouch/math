import OAI.NumberTheory.TotientAsymptotic.PPTResidualFamily
import OAI.NumberTheory.TotientAsymptotic.TailProductBounds
import OAI.NumberTheory.TotientAsymptotic.PPTHeadEdge

namespace OAI

/-! Small common factors and small left tails in the residual comparison. -/

noncomputable section
open scoped BigOperators Topology
open Filter

namespace TotientAsymptotic

/-- A logarithmic number of primes below the strict first-coordinate
gap has an arbitrarily small fixed power of the local value scale. -/
theorem ppt_prime_product_subpower_of_gap {A γ ε : ℝ}
    (hA : 0 ≤ A) (hγ : 0 < γ) (hε : 0 < ε) :
    ∀ᶠ z : ℝ in atTop, ∀ (n : ℕ) (p : Fin n → ℕ),
      (∀ i, (p i).Prime) → (n : ℝ) ≤ A*Real.log (B z) →
      (∀ i, B (p i) ≤ B z-γ*B z/(Real.log (B z))^3) →
      ((∏ i, p i : ℕ) : ℝ) ≤ z^ε := by
  filter_upwards [ppt_comparison_exp_decay_at_scale 0 2 hγ,
    B_tendsto.eventually (eventually_ge_atTop (max 1 (A/ε))),
    eventually_gt_atTop (1 : ℝ)] with z hdecay ht hz
  intro n p hp hdim hcoords
  have ht1 : 1 ≤ B z := (le_max_left _ _).trans ht
  have ht0 : 0 < B z := zero_lt_one.trans_le ht1
  have htA : A/ε ≤ B z := (le_max_right _ _).trans ht
  have hN : (n : ℝ) ≤ A*B z := hdim.trans
    (mul_le_mul_of_nonneg_left (Real.log_le_self ht0.le) hA)
  have hdecay' : Real.exp (-(γ*B z/(Real.log (B z))^3)) ≤ 1/(B z)^2 := by
    simpa only [zero_mul, zero_sub, Real.rpow_neg ht0.le, Real.rpow_two, one_div] using hdecay
  have hsmall : (n : ℝ)*Real.exp (-(γ*B z/(Real.log (B z))^3)) ≤ ε := by
    calc
      _ ≤ (A*B z)*(1/(B z)^2) :=
        mul_le_mul hN hdecay' (Real.exp_pos _).le (mul_nonneg hA ht0.le)
      _ = A/B z := by field_simp
      _ ≤ ε := by
        apply (div_le_iff₀ ht0).mpr
        have hh := (div_le_iff₀ hε).mp htA
        nlinarith only [hh]
  have hlog := prime_tail_log_bound p hp (by
    intro i
    exact hcoords i)
  have hlog' : Real.log ((∏ i, p i : ℕ) : ℝ) ≤ ε*Real.log z := by
    apply hlog.trans
    calc
      _ = ((n : ℝ)*Real.exp (-(γ*B z/(Real.log (B z))^3)))*Real.exp (B z) := by
        rw [show B z-γ*B z/(Real.log (B z))^3 =
          -(γ*B z/(Real.log (B z))^3)+B z by ring, Real.exp_add]
        ring
      _ ≤ ε*Real.exp (B z) := mul_le_mul_of_nonneg_right hsmall (Real.exp_pos _).le
      _ = ε*Real.log z := by rw [B, Real.exp_log (Real.log_pos hz)]
  have hprod : (0 : ℝ) < (∏ i, p i : ℕ) := by
    exact_mod_cast Finset.prod_pos (fun i _ => (hp i).pos)
  have hh := Real.exp_le_exp.mpr hlog'
  rw [Real.exp_log hprod] at hh
  simpa only [Real.rpow_def_of_pos (zero_lt_one.trans hz), mul_comm] using hh

/-- The same strict coordinate gap makes the seed-multiplied totient
small, for the fixed seed and any prescribed positive power. -/
theorem ppt_seed_totient_subpower_of_gap (d : ℕ) {A γ ε : ℝ}
    (hA : 0 ≤ A) (hγ : 0 < γ) (hε : 0 < ε) :
    ∀ᶠ z : ℝ in atTop, ∀ (n : ℕ) (p : Fin n → ℕ),
      (∀ i, (p i).Prime) → (n : ℝ) ≤ A*Real.log (B z) →
      (∀ i, B (p i) ≤ B z-γ*B z/(Real.log (B z))^3) →
      ((d*(∏ i, p i).totient : ℕ) : ℝ) ≤ z^ε := by
  filter_upwards [ppt_prime_product_subpower_of_gap hA hγ (half_pos hε),
    (tendsto_rpow_atTop (half_pos hε)).eventually (eventually_ge_atTop (d : ℝ)),
    eventually_gt_atTop (0 : ℝ)] with z hprod hd hz
  intro n p hp hdim hcoords
  have hφ : ((∏ i, p i).totient : ℝ) ≤ z^(ε/2) :=
    (Nat.cast_le.mpr (Nat.totient_le _)).trans (hprod n p hp hdim hcoords)
  calc
    _ = (d : ℝ)*((∏ i, p i).totient : ℝ) := Nat.cast_mul _ _
    _ ≤ z^(ε/2)*z^(ε/2) := mul_le_mul hd hφ (Nat.cast_nonneg _) (Real.rpow_pos_of_pos hz _).le
    _ = z^ε := by rw [← Real.rpow_add hz]; congr 1; ring

/-- A normal prime whose predecessor is smooth at `V` has double
logarithm at most `6 B(V)`.  No bound on the prime itself is assumed. -/
lemma ppt_normal_smooth_prime_coordinate {p : ℕ} {S V : ℝ}
    (hp : IsNormalPrime S p) (hp3 : 3 ≤ p) (hS : 1 < S)
    (hBS : 0 ≤ B S) (hSV : S ≤ V) (hBV : 1 ≤ B V)
    (hsmooth : (largestPrimeFactor (p-1) : ℝ) ≤ V) : B p ≤ 6*B V := by
  have hparts : partBelow (p-1) V = p-1 :=
    partBelow_all_of_largest_le (Nat.sub_pos_of_lt hp.1.one_lt).ne' hsmooth
  have hΩ : ((p-1).primeFactorsList.length : ℝ) ≤ 4*B V := by
    simpa only [hparts] using normal_terminal_omega hp hS hBS hSV
  have hBV0 : 0 < B V := zero_lt_one.trans_le hBV
  have hfactor : B (largestPrimeFactor (p-1)) ≤ B V := by
    have hpone : (1 : ℝ) < largestPrimeFactor (p-1) := by
      exact_mod_cast one_lt_largestPrimeFactor (show 2 ≤ p-1 by omega)
    exact Real.log_le_log (Real.log_pos hpone)
      (Real.log_le_log (zero_lt_one.trans hpone) hsmooth)
  have hlower := largest_factor_doubleLog_lower (show 2 ≤ p-1 by omega)
    (show 0 < 4*B V by positivity) hΩ
  have hlog := Real.log_le_self (show 0 ≤ 4*B V by positivity)
  have hshift := shifted_doubleLog_lower hp3
  linarith only [hlower, hfactor, hlog, hshift, hBV]

/-- The smooth-tail coordinate scale is eventually below half of the
comparison double logarithm. -/
theorem ppt_smooth_height_half_scale : ∀ᶠ t : ℝ in atTop,
    ∀ V : ℝ, B V ≤ 2*t^(2/3 : ℝ) → 6*B V ≤ t/2 := by
  filter_upwards [(tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1/3)).eventually
      (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1/24)),
    eventually_gt_atTop (0 : ℝ)] with t hsmall ht
  intro V hV
  have he : t^(2/3 : ℝ)/t = t^(-(1/3 : ℝ)) := by
    calc
      _ = t^(2/3 : ℝ)/t^(1 : ℝ) := by rw [Real.rpow_one]
      _ = _ := by rw [← Real.rpow_sub ht]; norm_num
  rw [← he] at hsmall
  have hh := (div_lt_iff₀ ht).mp hsmall
  linarith only [hV, hh]

lemma ppt_half_scale_below_gap : ∀ᶠ t : ℝ in atTop,
    t/2 ≤ t-t/(Real.log t)^3 := by
  filter_upwards [Real.tendsto_log_atTop.eventually (eventually_ge_atTop (2 : ℝ)),
    eventually_gt_atTop (0 : ℝ)] with t hlog ht
  have hlog0 : 0 < Real.log t := by linarith only [hlog]
  have hp : (2 : ℝ) ≤ (Real.log t)^3 := by
    have hh := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) hlog 3
    norm_num at hh ⊢
    linarith only [hh]
  have hfrac : t/(Real.log t)^3 ≤ t/2 := by
    apply (div_le_div_iff₀ (pow_pos hlog0 3) (by norm_num : (0 : ℝ) < 2)).mpr
    nlinarith only [mul_le_mul_of_nonneg_left hp ht.le]
  linarith only [hfrac]

/-- A normal small left tail supplies the actual `D=d*φ(a)` power
restriction in Ford's comparison parameters. -/
theorem ppt_normal_small_tail_subpower (d : ℕ) {A ε : ℝ}
    (hA : 0 ≤ A) (hε : 0 < ε) :
    ∀ᶠ z : ℝ in atTop, ∀ (n : ℕ) (p : Fin n → ℕ) (S V : ℝ),
      (n : ℝ) ≤ A*Real.log (B z) → 1 < S → 0 ≤ B S → S ≤ V →
      1 ≤ B V → B V ≤ 2*(B z)^(2/3 : ℝ) →
      (∀ i, IsNormalPrime S (p i)) → (∀ i, 3 ≤ p i) →
      (∀ i, (largestPrimeFactor (p i-1) : ℝ) ≤ V) →
      ((d*(∏ i, p i).totient : ℕ) : ℝ) ≤ z^ε := by
  filter_upwards [ppt_seed_totient_subpower_of_gap d hA (by norm_num : (0 : ℝ) < 1) hε,
    B_tendsto.eventually ppt_smooth_height_half_scale,
    B_tendsto.eventually ppt_half_scale_below_gap] with z hsmall hhalf hgap
  intro n p S V hdim hS hBS hSV hBV hV hp hp3 hsmooth
  apply hsmall n p (fun i => (hp i).1) hdim
  intro i
  have hh := (ppt_normal_smooth_prime_coordinate (hp i) (hp3 i) hS hBS hSV hBV
    (hsmooth i)).trans ((hhalf V hV).trans hgap)
  simpa only [one_mul] using hh

/-- A gap for largest predecessor factors is a gap for the actual
primes, after halving its fixed constant.  This supplies smallness of
the common canceled prime product. -/
theorem ppt_prime_gap_of_factor_gap {γ : ℝ} (hγ : 0 < γ) :
    ∀ᶠ z : ℝ in atTop, ∀ (p : ℕ) (S : ℝ),
      3 ≤ p → 1 < S → 0 ≤ B S → S ≤ z → IsNormalPrime S p → (p-1 : ℕ) ≤ z →
      B (largestPrimeFactor (p-1))/B z ≤ 1-γ/(Real.log (B z))^3 →
      B p ≤ B z-(γ/2)*B z/(Real.log (B z))^3 := by
  filter_upwards [ppt_normal_factor_loss_mesh,
    B_tendsto.eventually (ppt_first_cutoff_below_aligned_head (half_pos hγ)),
    B_tendsto.eventually (eventually_ge_atTop (1 : ℝ))] with z hloss hhead hB
  intro p S hp3 hS hBS hSz hp hpz hgap
  have hB0 : 0 < B z := zero_lt_one.trans_le hB
  have hδ := hhead (1-(γ/2)/(Real.log (B z))^3)
    (2*((Real.log (B z))^5/Real.sqrt (B z))) le_rfl le_rfl
  have hθ := ppt_uniform_head_edge_lt_one hB
  have hδ' : 2*((Real.log (B z))^5/Real.sqrt (B z)) ≤ (γ/2)/(Real.log (B z))^3 := by
    linarith only [hδ, hθ]
  have hfactor := (hloss p S hp3 hS hBS hSz hp hpz).1
  have hsum : γ/(Real.log (B z))^3 =
      (γ/2)/(Real.log (B z))^3+(γ/2)/(Real.log (B z))^3 := by ring
  have hnorm : B p/B z ≤ 1-(γ/2)/(Real.log (B z))^3 := by
    rw [hsum] at hgap
    linarith only [hgap, hfactor, hδ']
  have hh := (div_le_iff₀ hB0).mp hnorm
  convert hh using 1
  ring

end TotientAsymptotic

end

end OAI
