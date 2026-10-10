import OAI.Probability.Renewal.Decay
import OAI.Probability.Renewal.TiltMoments

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology ENNReal
namespace HoneycombLocal

lemma integrable_stretched_exp {a c : ℝ} (ha : 0 < a) (hc : 0 < c) :
    Integrable (fun t : ℝ => Real.exp (-c * |t| ^ a)) := by
  have hi : IntegrableOn (fun t : ℝ => Real.exp (-c * t ^ a)) (Ioi 0) := by
    simpa using integrableOn_rpow_mul_exp_neg_mul_rpow (s := 0) (by norm_num) ha hc
  have hp : IntegrableOn (fun t : ℝ => Real.exp (-c * |t| ^ a)) (Ioi 0) :=
    (integrableOn_congr_fun (fun t ht => by rw [abs_of_pos ht]) measurableSet_Ioi).mpr hi
  have hn : IntegrableOn (fun t : ℝ => Real.exp (-c * |t| ^ a)) (Iic 0) := by
    rw [← Measure.map_neg_eq_self (volume : Measure ℝ)]
    let em : MeasurableEmbedding (fun x : ℝ => -x) := (Homeomorph.neg ℝ).measurableEmbedding
    rw [em.integrableOn_map_iff]
    simp only [Function.comp_def, abs_neg, neg_preimage, neg_Iic, neg_zero]
    exact Iff.mpr integrableOn_Ici_iff_integrableOn_Ioi hp
  simpa only [Iic_union_Ioi, integrableOn_univ] using hn.union hp

lemma exists_integral_tail_small {g : ℝ → ℝ} (hg : Integrable g) {ε : ℝ} (hε : 0 < ε) :
    ∃ ω : ℝ, 1 ≤ ω ∧ (∫ t : ℝ in (Icc (-ω) ω)ᶜ, g t) ≤ ε := by
  have hlim := intervalIntegral_tendsto_integral hg tendsto_neg_atTop_atBot (tendsto_id : Tendsto (fun x : ℝ => x) atTop atTop)
  have ht : Tendsto (fun ω : ℝ => (∫ t, g t) - ∫ t in -ω..ω, g t) atTop (𝓝 0) := by
    simpa using (tendsto_const_nhds (x := ∫ t, g t)).sub hlim
  have hεv := ht.eventually (Iio_mem_nhds hε)
  obtain ⟨ω, hω, he⟩ := (eventually_ge_atTop (1 : ℝ)).and hεv |>.exists
  refine ⟨ω, hω, ?_⟩
  rw [setIntegral_compl measurableSet_Icc hg, integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (by linarith : -ω ≤ ω)]
  exact he.le

lemma sigma_rpow_bound {a u σ V : ℝ} (ha : 0 < a ∧ a < 1) (hu : 0 < u)
    (hσ : 0 < σ) (hV : 0 < V) {k : ℕ} (hku : 1 ≤ (k : ℝ) * u ^ a)
    (hvar : σ ^ 2 ≤ (k : ℝ) * V * u ^ (a - 2)) :
    σ ^ a ≤ (max V 1) ^ a * (k : ℝ) := by
  let K := (k : ℝ) * u ^ a
  let H := max V 1
  have hK : 1 ≤ K := hku
  have hH : 1 ≤ H := le_max_right _ _
  have hH0 : 0 < H := hV.trans_le (le_max_left _ _)
  have hK0 : 0 < K := zero_lt_one.trans_le hK
  have hid : u ^ (a - 2) * u ^ 2 = u ^ a := by
    rw [Real.rpow_sub hu, Real.rpow_two]
    field_simp
  have hs : (σ * u) ^ 2 ≤ V * K := by
    have hh := mul_le_mul_of_nonneg_right hvar (sq_nonneg u)
    simpa only [mul_pow, mul_assoc, hid, K, mul_left_comm V (k : ℝ)] using hh
  have hHK : 1 ≤ H * K := by nlinarith [mul_nonneg (by linarith : 0 ≤ H - 1) (by linarith : 0 ≤ K - 1)]
  have hvhk : V * K ≤ H * K := mul_le_mul_of_nonneg_right (le_max_left _ _) hK0.le
  have hsu : σ * u ≤ H * K := by
    nlinarith [sq_nonneg (H * K - 1), mul_nonneg (by linarith : 0 ≤ H * K) (by linarith : 0 ≤ H * K - 1)]
  have hr := Real.rpow_le_rpow (by positivity : 0 ≤ σ * u) hsu ha.1.le
  rw [Real.mul_rpow hσ.le hu.le, Real.mul_rpow hH0.le hK0.le] at hr
  have hr' := hr.trans (mul_le_mul_of_nonneg_left (Real.rpow_le_self_of_one_le hK ha.2.le)
    (Real.rpow_pos_of_pos hH0 a).le)
  apply (mul_le_mul_iff_left₀ (Real.rpow_pos_of_pos hu a)).mp
  convert hr' using 1
  dsimp [H, K]
  ring

namespace AnnulusData
variable {p : PMF ℕ} {a : ℝ} (D : AnnulusData p a) (M : MomentData p a)

def envelope (t : ℝ) : ℝ :=
  Real.exp (-(D.decayConst / M.varUpper) * t ^ 2) +
  Real.exp (-(D.decayConst / (max M.varUpper 1) ^ a) * |t| ^ a)

lemma envelope_nonneg (t : ℝ) : 0 ≤ D.envelope M t := by
  unfold envelope
  positivity

lemma envelope_integrable (ha : 0 < a) : Integrable (D.envelope M) := by
  apply Integrable.add
  · apply integrable_exp_neg_mul_sq
    exact div_pos D.decayConst_pos M.varUpper_pos
  · apply integrable_stretched_exp ha
    exact div_pos D.decayConst_pos (Real.rpow_pos_of_pos (lt_of_lt_of_le zero_lt_one (le_max_right _ _)) a)

lemma normalized_bound (ha : 0 < a ∧ a < 1) {u σ : ℝ} (hu : 0 < u)
    (huD : u ≤ D.epsilon) (huM : u ≤ M.epsilon) {k : ℕ}
    (hku : 1 ≤ (k : ℝ) * u ^ a) (hσ : 0 < σ)
    (hvar : σ ^ 2 = k * natVariance (tilt p u hu.le))
    {ρ : ℝ} (hρ : 0 ≤ ρ)
    (hgap : ∀ t, D.epsilon ≤ |t| → |t| ≤ Real.pi → ‖latticeChar (tilt p u hu.le) t‖ ≤ ρ)
    (t : ℝ) (ht : |t| ≤ Real.pi * σ) :
    ‖latticeChar (tilt p u hu.le) (t / σ)‖ ^ k ≤ D.envelope M t + ρ ^ k := by
  have hV := M.varUpper_pos
  have hv : σ ^ 2 ≤ (k : ℝ) * M.varUpper * u ^ (a - 2) := by
    rw [hvar]
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_left (M.var_upper u hu huM) (Nat.cast_nonneg k)
  have hσa := sigma_rpow_bound ha hu hσ hV hku hv
  have hC := D.decayConst_pos
  have hH : 0 < max M.varUpper 1 := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  have hθ : |t / σ| ≤ Real.pi := by
    rw [abs_div, abs_of_pos hσ, div_le_iff₀ hσ]
    exact ht
  by_cases hlo : |t / σ| ≤ u
  · have hb := pow_le_pow_left₀ (norm_nonneg _) (D.char_bound hu huD hu.le le_rfl hlo) k
    rw [← Real.exp_nat_mul] at hb
    have hbase : σ ^ 2 / M.varUpper ≤ (k : ℝ) * u ^ (a - 2) := by
      apply (div_le_iff₀ hV).mpr
      nlinarith [hv]
    have hm := mul_le_mul_of_nonneg_right hbase (by positivity : 0 ≤ D.decayConst * (t / σ) ^ 2)
    have hid : σ ^ 2 / M.varUpper * (D.decayConst * (t / σ) ^ 2) =
        D.decayConst / M.varUpper * t ^ 2 := by field_simp
    rw [hid] at hm
    have hexp : (k : ℝ) * (-D.decayConst * u ^ (a - 2) * (t / σ) ^ 2) ≤
        -(D.decayConst / M.varUpper) * t ^ 2 := by nlinarith
    have he := hb.trans (Real.exp_le_exp.mpr hexp)
    exact he.trans (by
      unfold envelope
      nlinarith [Real.exp_pos (-(D.decayConst / (max M.varUpper 1) ^ a) * |t| ^ a), pow_nonneg hρ k])
  · by_cases hmid : |t / σ| ≤ D.epsilon
    · have hθ0 : 0 < |t / σ| := hu.trans (lt_of_not_ge hlo)
      have hb := pow_le_pow_left₀ (norm_nonneg _) (D.intermediate hθ0 hmid hu.le (le_of_not_ge hlo)) k
      rw [← Real.exp_nat_mul] at hb
      have hcoef : D.decayConst / (max M.varUpper 1) ^ a ≤ D.decayConst * k / σ ^ a := by
        apply (div_le_div_iff₀ (Real.rpow_pos_of_pos hH a) (Real.rpow_pos_of_pos hσ a)).mpr
        nlinarith [mul_le_mul_of_nonneg_left hσa hC.le]
      have hm := mul_le_mul_of_nonneg_right hcoef (Real.rpow_nonneg (abs_nonneg t) a)
      have hid : |t / σ| ^ a = |t| ^ a / σ ^ a := by
        rw [abs_div, abs_of_pos hσ, Real.div_rpow (abs_nonneg t) hσ.le]
      have hexp : (k : ℝ) * (-D.decayConst * |t / σ| ^ a) ≤
          -(D.decayConst / (max M.varUpper 1) ^ a) * |t| ^ a := by
        rw [hid]
        simpa only [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm, neg_mul, mul_neg] using neg_le_neg hm
      have he := hb.trans (Real.exp_le_exp.mpr hexp)
      exact he.trans (by
        unfold envelope
        nlinarith [Real.exp_pos (-(D.decayConst / M.varUpper) * t ^ 2), pow_nonneg hρ k])
    · have hb := pow_le_pow_left₀ (norm_nonneg _) (hgap (t / σ) (le_of_not_ge hmid) hθ) k
      exact hb.trans (le_add_of_nonneg_left (D.envelope_nonneg M t))

end AnnulusData
end HoneycombLocal

end

end OAI
