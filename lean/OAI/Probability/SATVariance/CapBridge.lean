import OAI.Probability.SATVariance.CappedUpper

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory

namespace RandomKSAT

open scoped Classical ENNReal

lemma T_eq_min_natH_ae {n k : ℕ} (hkn : k ≤ n) (B : ℝ) :
    ∀ᵐ ω ∂streamLaw n k, T B ω = ((min (firstFailure ω).toNat (cap n B) : ℕ) : ℝ) := by
  filter_upwards [firstFailure_finite_ae hkn] with ω hω
  have he := ENat.natCast_toNat (ne_of_lt hω)
  by_cases h : (firstFailure ω).toNat ≤ cap n B
  · have hEN : firstFailure ω ≤ (cap n B : ℕ∞) := by rw [← he]; exact_mod_cast h
    simp only [T, min_eq_left hEN, min_eq_left h]
  · have hEN : (cap n B : ℕ∞) ≤ firstFailure ω := by rw [← he]; exact_mod_cast (le_of_not_ge h)
    simp only [T, min_eq_right hEN, min_eq_right (le_of_not_ge h), ENat.toNat_natCast]

lemma cap_error_eq_nat_ae {n k : ℕ} (hkn : k ≤ n) (B : ℝ) :
    ∀ᵐ ω ∂streamLaw n k, (H ω-T B ω)^2 = (((firstFailure ω).toNat-cap n B : ℕ) : ℝ)^2 := by
  filter_upwards [T_eq_min_natH_ae hkn B] with ω hω
  rw [hω, H, ← Nat.cast_sub (Nat.min_le_left _ _)]
  congr 2
  omega

lemma natH_integral {n k : ℕ} (hkn : k ≤ n) (f : ℕ → ℝ) :
    (∫ ω, f (firstFailure ω).toNat ∂streamLaw n k) =
      ∑' m, ((streamLaw n k).map (fun ω => (firstFailure ω).toNat) {m}).toReal * f m := by
  let := streamLaw_probability n k hkn
  rw [← integral_map (measurable_natH n k).aemeasurable
    (measurable_of_countable f).aestronglyMeasurable]
  conv_lhs => rw [
    ← Measure.sum_smul_dirac ((streamLaw n k).map (fun ω => (firstFailure ω).toNat)),
    integral_sum_dirac (fun _ => measure_ne_top _ _)]
  rfl

lemma summable_sub_sq_geometric {q : ℝ} (hq : 0 ≤ q) (hq1 : q < 1) (M : ℕ) :
    Summable (fun m : ℕ => ((m-M : ℕ) : ℝ)^2*q^m) := by
  have hn : ‖q‖ < 1 := by simpa [Real.norm_eq_abs, abs_of_nonneg hq] using hq1
  apply Summable.of_nonneg_of_le (fun m => by positivity) _
    (summable_pow_mul_geometric_of_norm_lt_one 2 hn)
  intro m
  exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by positivity)
    (by exact_mod_cast Nat.sub_le m M) 2) (pow_nonneg hq m)

lemma tsum_sub_sq_geometric {q : ℝ} (hq : 0 ≤ q) (hq1 : q < 1) (M : ℕ) :
    (∑' m : ℕ, ((m-M : ℕ) : ℝ)^2*q^m) = q^M * ∑' j : ℕ, (j : ℝ)^2*q^j := by
  have hs := summable_sub_sq_geometric hq hq1 M
  have he := hs.sum_add_tsum_nat_add M
  have hz : ∑ m ∈ Finset.range M, ((m-M : ℕ) : ℝ)^2*q^m = 0 := by
    apply Finset.sum_eq_zero
    intro m hm
    simp only [Nat.sub_eq_zero_of_le (le_of_lt (Finset.mem_range.mp hm)),
      Nat.cast_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_mul]
  rw [hz, zero_add] at he
  rw [← he, ← tsum_mul_left]
  apply tsum_congr
  intro j
  rw [Nat.add_sub_cancel, pow_add]
  ring

lemma cap_error_geom {n k : ℕ} (hk : 1 ≤ k) (hkn : k ≤ n) (B : ℝ) :
    (∫ ω : Stream n k, (H ω-T B ω)^2 ∂streamLaw n k) ≤
      ((2 : ℝ)^n * (1-((2 : ℝ)^k)⁻¹)^(cap n B)) /
        (1-((2 : ℝ)^k)⁻¹) * ∑' j : ℕ, (j : ℝ)^2*(1-((2 : ℝ)^k)⁻¹)^j := by
  let q := 1-((2 : ℝ)^k)⁻¹
  have hq : 0 < q := real_rate_pos hk
  have hq1 : q < 1 := real_rate_lt_one k
  rw [integral_congr_ae (cap_error_eq_nat_ae hkn B),
    natH_integral hkn (fun m => (((m-cap n B : ℕ) : ℝ)^2))]
  have hb (m : ℕ) := mul_le_mul_of_nonneg_right (natH_mass_bound hk hkn m)
    (sq_nonneg (((m-cap n B : ℕ) : ℝ)))
  have hs := (summable_sub_sq_geometric hq.le hq1 (cap n B)).mul_left ((2 : ℝ)^n/q)
  have ht : Summable (fun m : ℕ =>
      ((streamLaw n k).map (fun ω => (firstFailure ω).toNat) {m}).toReal *
      (((m-cap n B : ℕ) : ℝ)^2)) := by
    apply Summable.of_nonneg_of_le (fun _ => by positivity) _ hs
    intro m
    calc
      _ ≤ (((2 : ℝ)^n/q)*q^m)*(((m-cap n B : ℕ) : ℝ)^2) := hb m
      _ = _ := by ring
  calc
    _ ≤ ∑' m : ℕ, ((2 : ℝ)^n/q)*((((m-cap n B : ℕ) : ℝ)^2)*q^m) := by
      apply ht.tsum_le_tsum _ hs
      intro m
      convert hb m using 1
      dsimp [q]
      ring
    _ = _ := by rw [tsum_mul_left, tsum_sub_sq_geometric hq.le hq1]; dsimp [q]; ring

lemma U_pos {k : ℕ} (hk : 1 ≤ k) : 0 < U k := by
  have hq := real_rate_pos hk
  have hq1 := real_rate_lt_one k
  exact div_pos (Real.log_pos (by norm_num)) (neg_pos.mpr (Real.log_neg hq hq1))

lemma cap_geometric_uniform {k : ℕ} (hk : 1 ≤ k) {B : ℝ} (hB : U k ≤ B) (n : ℕ) :
    (2 : ℝ)^n * (1-((2 : ℝ)^k)⁻¹)^(cap n B) ≤ (1-((2 : ℝ)^k)⁻¹)⁻¹ := by
  let q := 1-((2 : ℝ)^k)⁻¹
  have hq : 0 < q := real_rate_pos hk
  have hl : Real.log q < 0 := Real.log_neg hq (real_rate_lt_one k)
  have ht : Real.log 2 ≤ B*(-Real.log q) := (div_le_iff₀ (by linarith)).mp hB
  have hf : B*n < (cap n B : ℝ)+1 := Nat.lt_floor_add_one _
  apply (Real.log_le_log_iff (mul_pos (by positivity) (pow_pos hq _)) (inv_pos.mpr hq)).mp
  rw [Real.log_mul (by positivity) (ne_of_gt (pow_pos hq _)), Real.log_pow, Real.log_pow,
    Real.log_inv]
  have hh := mul_le_mul_of_nonneg_left ht (Nat.cast_nonneg n : (0 : ℝ) ≤ n)
  change _ ≤ -Real.log q
  nlinarith

def bridgeC (k : ℕ) : ℝ := (1-((2 : ℝ)^k)⁻¹)⁻¹^2 *
  ∑' j : ℕ, (j : ℝ)^2*(1-((2 : ℝ)^k)⁻¹)^j

lemma bridgeC_nonneg {k : ℕ} (hk : 1 ≤ k) : 0 ≤ bridgeC k := by
  unfold bridgeC
  exact mul_nonneg (sq_nonneg _) (tsum_nonneg (fun j => by positivity [real_rate_pos hk]))

lemma cap_error_uniform {n k : ℕ} (hk : 1 ≤ k) (hkn : k ≤ n) {B : ℝ} (hB : U k ≤ B) :
    (∫ ω : Stream n k, (H ω-T B ω)^2 ∂streamLaw n k) ≤ bridgeC k := by
  have hq := real_rate_pos hk
  have hb := cap_error_geom hk hkn B
  have hz : 0 ≤ ∑' j : ℕ, (j : ℝ)^2*(1-((2 : ℝ)^k)⁻¹)^j :=
    tsum_nonneg (fun _ => by positivity)
  have hh := mul_le_mul_of_nonneg_right
    ((div_le_div_iff_of_pos_right hq).mpr (cap_geometric_uniform hk hB n)) hz
  apply hb.trans
  convert hh using 1
  dsimp [bridgeC]
  ring

lemma variance_bridge.{u_1} {Ω : Type u_1} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {f g : Ω → ℝ} (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    variance f μ ≤ 2*variance g μ + 2*(∫ ω, (f ω-g ω)^2 ∂μ) := by
  let c := ∫ ω, g ω ∂μ
  have hfc := hf.sub (memLp_const c)
  have hgc := hg.sub (memLp_const c)
  have hfg := hf.sub hg
  have hv := variance_le_expectation_sq hfc.aestronglyMeasurable
  simp only [Pi.sub_apply, Pi.pow_apply] at hv
  change variance (fun ω => f ω-c) μ ≤ (∫ ω, (f ω-c)^2 ∂μ) at hv
  rw [variance_sub_const hf.aestronglyMeasurable] at hv
  have hm := integral_mono hfc.integrable_sq
    ((hgc.integrable_sq.const_mul 2).add (hfg.integrable_sq.const_mul 2))
    (fun ω => by dsimp; nlinarith [sq_nonneg ((f ω-g ω)-(g ω-c))])
  change (∫ ω, (f ω-c)^2 ∂μ) ≤ (∫ ω, 2*(g ω-c)^2+2*(f ω-g ω)^2 ∂μ) at hm
  have hgi : Integrable (fun ω => (g ω-c)^2) μ := hgc.integrable_sq
  have hfgi : Integrable (fun ω => (f ω-g ω)^2) μ := hfg.integrable_sq
  rw [integral_add (hgi.const_mul 2) (hfgi.const_mul 2),
    integral_const_mul, integral_const_mul, ← variance_eq_integral hg.aemeasurable] at hm
  exact hv.trans hm

lemma H_variance_le_cap {n k : ℕ} (hk : 1 ≤ k) (hkn : k ≤ n) {B : ℝ} (hB : U k ≤ B) :
    variance (H : Stream n k → ℝ) (streamLaw n k) ≤
      2*variance (T B : Stream n k → ℝ) (streamLaw n k)+2*bridgeC k := by
  let := streamLaw_probability n k hkn
  exact (variance_bridge (H_memLp_two hk hkn) (T_memLp hkn B 2)).trans
    (by linarith [cap_error_uniform hk hkn hB])

lemma cap_variance_le_H {n k : ℕ} (hk : 1 ≤ k) (hkn : k ≤ n) {B : ℝ} (hB : U k ≤ B) :
    variance (T B : Stream n k → ℝ) (streamLaw n k) ≤
      2*variance (H : Stream n k → ℝ) (streamLaw n k)+2*bridgeC k := by
  let := streamLaw_probability n k hkn
  have hh := variance_bridge (T_memLp hkn B 2) (H_memLp_two hk hkn)
  have he : (∫ ω : Stream n k, (T B ω-H ω)^2 ∂streamLaw n k) =
      ∫ ω : Stream n k, (H ω-T B ω)^2 ∂streamLaw n k := by
    congr 1
    funext ω
    ring
  rw [he] at hh
  exact hh.trans (by linarith [cap_error_uniform hk hkn hB])

theorem uncapped_variance_upper (k : ℕ) (hk : 3 ≤ k) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ, k ≤ n →
      variance (H : Stream n k → ℝ) (streamLaw n k) ≤ C*n*ell k n := by
  have hk1 : 1 ≤ k := by omega
  obtain ⟨C,hC,hv⟩ := capped_variance_upper k hk (U k) (U_pos hk1)
  refine ⟨2*C+2*bridgeC k, by positivity [bridgeC_nonneg hk1], fun n hkn => ?_⟩
  have hh := H_variance_le_cap hk1 hkn (le_refl (U k))
  have hn : (1 : ℝ) ≤ n := by exact_mod_cast (hk1.trans hkn)
  have he := ell_one_le k n (hk1.trans hkn)
  have hb := bridgeC_nonneg hk1
  have hm : 1 ≤ (n : ℝ)*ell k n := by nlinarith
  have hm' := mul_le_mul_of_nonneg_left hm hb
  nlinarith [hv n hkn]

end RandomKSAT

end

end OAI
