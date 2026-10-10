import OAI.MathematicalPhysics.AlternatingFlow.EffectiveProfiles
import OAI.MathematicalPhysics.AlternatingFlow.Names

namespace OAI

section DecoderBoundsDevelopment

open scoped BigOperators Topology ContDiff
open Filter

namespace AlternatingNS.Quantitative

lemma linear_id_jet (r : ℕ) {x : ℝ} (hx : |x| ≤ 1) : |iteratedDeriv r id x| ≤ 1 := by
  rw [iteratedDeriv_id]; split_ifs <;> simp_all

lemma transition_affine (r : ℕ) (a d : ℝ) :
    iteratedDeriv r (fun x => Real.smoothTransition ((x-a)/d)) =
      fun x => d⁻¹ ^ r * iteratedDeriv r Real.smoothTransition ((x-a)/d) := by
  have h : (fun x => Real.smoothTransition ((x-a)/d)) =
      (fun x => Real.smoothTransition (d⁻¹ * (x-a))) := by funext x; congr 1; ring
  rw [h, iteratedDeriv_comp_sub_const r (fun z => Real.smoothTransition (d⁻¹ * z)) a,
    iteratedDeriv_comp_const_mul
    (Real.smoothTransition.contDiff.of_le (WithTop.coe_le_coe.mpr le_top))]
  simp only [div_eq_mul_inv, mul_comm]

lemma periodizer_jet_bound (r : ℕ) (a c : ℝ) (ha : 0 < a) (hac : a < c) (hc : c < 1)
    (x : ℝ) :
    ‖iteratedFDeriv ℝ r (Profiles.periodizer a c) x‖ ≤
      1 + (c-a)⁻¹ ^ r * transitionBound r := by
  rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, Real.norm_eq_abs]
  have hnon : 0 ≤ (c-a)⁻¹ ^ r * (transitionBound r : ℝ) := by positivity
  by_cases hx : x = (⌊x⌋ : ℝ)
  · have he : Profiles.periodizer a c =ᶠ[𝓝 x] (fun y => y - (⌊x⌋ : ℝ)) := by
      have hlo : (⌊x⌋ : ℝ) + (c - 1) < x := by linarith
      have hhi : x < (⌊x⌋ : ℝ) + a := by linarith
      filter_upwards [Ioo_mem_nhds hlo hhi] with y hy
      have hy' : y - (⌊x⌋ : ℝ) ∈ Set.Ioo (c - 1) a := by
        constructor <;> linarith [hy.1, hy.2]
      calc
        Profiles.periodizer a c y = Profiles.periodizer a c ((⌊x⌋ : ℝ) + (y - (⌊x⌋ : ℝ))) := by congr 1; ring
        _ = Profiles.periodizer a c (y - (⌊x⌋ : ℝ)) := Profiles.periodizer_int_add a c _ _
        _ = y - (⌊x⌋ : ℝ) := Profiles.periodizer_near_zero a c ha hac hc _ hy'
    rw [he.iteratedDeriv_eq r]
    change |iteratedDeriv r (fun y => id (y - (⌊x⌋ : ℝ))) x| ≤ _
    rw [iteratedDeriv_comp_sub_const]
    exact (linear_id_jet r (by rw [hx]; simp)).trans (le_add_of_nonneg_right hnon)
  · have he : Profiles.periodizer a c =ᶠ[𝓝 x]
        (fun y => (y - (⌊x⌋ : ℝ)) - Real.smoothTransition ((y - (⌊x⌋ : ℝ)-a)/(c-a))) := by
      have hlo : (⌊x⌋ : ℝ) < x := (Int.floor_le x).lt_of_ne (Ne.symm hx)
      filter_upwards [Ioo_mem_nhds hlo (Int.lt_floor_add_one x)] with y hy
      have hy' : ⌊y⌋ = ⌊x⌋ := Int.floor_eq_iff.2 ⟨hy.1.le, hy.2⟩
      simp only [Profiles.periodizer, Int.fract, hy']
    rw [he.iteratedDeriv_eq r]
    change |iteratedDeriv r (fun y => ((id : ℝ → ℝ) - fun z => Real.smoothTransition ((z-a)/(c-a)))
      (y - (⌊x⌋ : ℝ))) x| ≤ _
    rw [iteratedDeriv_comp_sub_const]
    dsimp only
    rw [iteratedDeriv_sub contDiffAt_id
      (show ContDiffAt ℝ (r : ℕ∞ω) (fun z => Real.smoothTransition ((z-a)/(c-a))) (x - (⌊x⌋ : ℝ)) from by fun_prop),
      transition_affine]
    calc
      _ ≤ |iteratedDeriv r id (x - (⌊x⌋ : ℝ))| +
          (c-a)⁻¹ ^ r * |iteratedDeriv r Real.smoothTransition ((x - (⌊x⌋:ℝ)-a)/(c-a))| := by
        simpa only [Real.norm_eq_abs, abs_mul, abs_of_nonneg (pow_nonneg (inv_nonneg.mpr (sub_pos.mpr hac).le) r)] using
          norm_sub_le (iteratedDeriv r id (x - (⌊x⌋ : ℝ)))
            ((c-a)⁻¹ ^ r * iteratedDeriv r Real.smoothTransition ((x - (⌊x⌋:ℝ)-a)/(c-a)))
      _ ≤ _ := add_le_add (linear_id_jet r (by
          rw [abs_of_nonneg (sub_nonneg.mpr (Int.floor_le x))]
          linarith [Int.lt_floor_add_one x]))
        (mul_le_mul_of_nonneg_left
          (by simpa only [norm_iteratedFDeriv_eq_norm_iteratedDeriv, Real.norm_eq_abs] using
            transition_jet_bound r ((x - (⌊x⌋:ℝ)-a)/(c-a)))
          (pow_nonneg (inv_nonneg.mpr (sub_pos.mpr hac).le) r))

def decoderBound (b r : ℕ) : ℕ := 1 + (3 * (b - 1)) ^ r * transitionBound r

lemma decoder_jet_bound (b : ℕ) (hb : 2 ≤ b) (r : ℕ) (x : ℝ) :
    ‖iteratedFDeriv ℝ r (Profiles.decoder b) x‖ ≤ decoderBound b r := by
  have hm0 := Encoding.tailMax_nonneg b hb
  have hm1 := Encoding.tailMax_lt_one b hb
  have hgap : (((Encoding.tailMax b + 2) / 3) - ((2 * Encoding.tailMax b + 1) / 3))⁻¹ =
      (3 * (b - 1) : ℕ) := by
    have hbn : (b - 1 : ℕ) = (b : ℝ) - 1 := by exact_mod_cast Nat.cast_sub (by omega : 1 ≤ b)
    rw [Nat.cast_mul, hbn]
    have h : (b : ℝ) - 1 ≠ 0 := by
      have hb' : (2 : ℝ) ≤ b := by exact_mod_cast hb
      linarith
    unfold Encoding.tailMax
    field_simp
    ring
  have h := periodizer_jet_bound r ((2 * Encoding.tailMax b + 1) / 3)
    ((Encoding.tailMax b + 2) / 3) (by linarith) (by linarith) (by linarith) x
  rw [hgap] at h
  simpa only [Profiles.decoder, decoderBound, Nat.cast_add, Nat.cast_mul, Nat.cast_one, Nat.cast_pow] using h

end AlternatingNS.Quantitative

end DecoderBoundsDevelopment

end OAI
