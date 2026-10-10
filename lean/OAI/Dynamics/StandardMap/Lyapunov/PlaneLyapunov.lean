import OAI.Dynamics.StandardMap.EntropyEndpoint

namespace OAI

section
section
namespace StandardMapEntropy
open MeasureTheory Set Filter Metric
open scoped Topology BigOperators

namespace PlaneLyapunov

variable (A : ℕ → ℂ →L[ℝ] ℂ)

def Growth (v : ℂ) (l : ℝ) : Prop :=
  v ≠ 0 ∧ Tendsto (fun n : ℕ => Real.log ‖A n v‖ / (n : ℝ)) atTop (𝓝 l)

lemma norm_pos (hA : ∀ n, PlaneAreaPreserving (A n)) (n : ℕ) : 0 < ‖A n‖ :=
  lt_of_lt_of_le zero_lt_one (hA n).singular_pair.choose_spec.2.2.2.2

lemma image_norm_pos (hA : ∀ n, PlaneAreaPreserving (A n)) {v : ℂ} (hv : v ≠ 0) (n : ℕ) :
    0 < ‖A n v‖ := by
  have hh := (hA n).norm_lower v
  by_contra h
  have hz : ‖A n v‖ = 0 := le_antisymm (not_lt.mp h) (norm_nonneg _)
  rw [hz, mul_zero] at hh
  exact (norm_pos_iff.mpr hv).not_ge hh

lemma eventual_exp_lower (hA : ∀ n, PlaneAreaPreserving (A n)) {l α : ℝ}
    (hl : Tendsto (fun n : ℕ => Real.log ‖A n‖ / (n : ℝ)) atTop (𝓝 l)) (hα : α < l) :
    ∀ᶠ n : ℕ in atTop, Real.exp (α*(n : ℝ)) ≤ ‖A n‖ := by
  filter_upwards [(tendsto_order.mp hl).1 α hα, eventually_gt_atTop 0] with n hn hn0
  have hp : (0 : ℝ) < n := by exact_mod_cast hn0
  calc
    _ ≤ Real.exp (Real.log ‖A n‖) := Real.exp_le_exp.mpr ((le_div_iff₀ hp).mp hn.le)
    _ = _ := Real.exp_log (norm_pos A hA n)

noncomputable def tailConstant (M α : ℝ) : ℝ :=
  M * Real.exp (-α) / (1-Real.exp (-2*α))

lemma tailConstant_pos {M α : ℝ} (hM : 0 < M) (hα : 0 < α) : 0 < tailConstant M α := by
  unfold tailConstant
  apply div_pos (mul_pos hM (Real.exp_pos _))
  exact sub_pos.mpr (Real.exp_lt_one_iff.mpr (by linarith))

lemma stable_error_exp_bound (D : ℕ → ℝ) (M α : ℝ) (hM : 0 ≤ M) (hα : 0 < α)
    (n B : ℕ) (_hnB : n ≤ B)
    (hD : ∀ i, n ≤ i → i ≤ B → Real.exp (α*(i : ℝ)) ≤ D i) :
    (∑ i ∈ Finset.Ico n B, M/(D i*D (i+1))) ≤
      tailConstant M α * Real.exp (-2*α*(n : ℝ)) := by
  have hq0 : 0 ≤ Real.exp (-2*α) := (Real.exp_pos _).le
  have hq1 : Real.exp (-2*α) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
  have he (i : ℕ) (hi : i ∈ Finset.Ico n B) :
      M/(D i*D (i+1)) ≤ M*Real.exp (-α)*(Real.exp (-2*α))^i := by
    have hi0 := (Finset.mem_Ico.mp hi).1
    have hiB := (Finset.mem_Ico.mp hi).2
    have hl := hD i hi0 hiB.le
    have hr := hD (i+1) (by omega) (by omega)
    have hp := mul_le_mul hl hr (Real.exp_pos _).le ((Real.exp_pos _).trans_le hl).le
    calc
      _ ≤ M/(Real.exp (α*(i : ℝ))*Real.exp (α*((i+1 : ℕ) : ℝ))) :=
        div_le_div_of_nonneg_left hM (mul_pos (Real.exp_pos _) (Real.exp_pos _)) hp
      _ = _ := by
        rw [← Real.exp_add, div_eq_mul_inv, ← Real.exp_neg, ← Real.exp_nat_mul]
        rw [mul_assoc, ← Real.exp_add]
        congr 2
        push_cast
        ring
  calc
    _ ≤ ∑ i ∈ Finset.Ico n B, M*Real.exp (-α)*(Real.exp (-2*α))^i :=
      Finset.sum_le_sum he
    _ = (M*Real.exp (-α)) * ∑ i ∈ Finset.Ico n B, (Real.exp (-2*α))^i := by
      rw [Finset.mul_sum]
    _ ≤ (M*Real.exp (-α)) * ((Real.exp (-2*α))^n/(1-Real.exp (-2*α))) :=
      mul_le_mul_of_nonneg_left (geom_sum_Ico_le_of_lt_one hq0 hq1) (by positivity)
    _ = _ := by
      rw [← Real.exp_nat_mul]
      unfold tailConstant
      rw [show (n : ℝ)*(-2*α) = -2*α*(n : ℝ) by ring]
      ring

lemma inverse_bound_by_exp (D α : ℝ) (n : ℕ) (hD : Real.exp (α*(n : ℝ)) ≤ D) :
    D⁻¹ ≤ D*Real.exp (-2*α*(n : ℝ)) := by
  have hp : 0 < D := (Real.exp_pos _).trans_le hD
  calc
    _ ≤ (Real.exp (α*(n : ℝ)))⁻¹ := (inv_le_inv₀ hp (Real.exp_pos _)).mpr hD
    _ = Real.exp (α*(n : ℝ))*Real.exp (-2*α*(n : ℝ)) := by
      rw [← Real.exp_neg, ← Real.exp_add]
      congr 1
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_right hD (Real.exp_pos _).le

lemma exists_stable_bound (hA : ∀ n, PlaneAreaPreserving (A n))
    (M : ℝ) (hM : 0 < M)
    (hstep : ∀ n v, ‖A n v‖ ≤ M*‖A (n+1) v‖)
    {l : ℝ} (hl : Tendsto (fun n : ℕ => Real.log ‖A n‖ / (n : ℝ)) atTop (𝓝 l)) :
    ∃ s : ℂ, ‖s‖=1 ∧ ∀ α : ℝ, 0 < α → α < l →
      ∀ᶠ n : ℕ in atTop, ‖A n s‖ ≤
        ‖A n‖*(1+tailConstant M α)*Real.exp (-2*α*(n : ℝ)) := by
  classical
  choose a hau ham hao has hnorm using fun n => (hA n).singular_pair
  have hu (n : ℕ) : quarterTurn (a n) ∈ sphere (0 : ℂ) 1 := by
    simp only [mem_sphere, dist_zero_right, norm_quarterTurn, hau]
  obtain ⟨s, hs, φ, hφ, hlim⟩ := (isCompact_sphere (0 : ℂ) 1).tendsto_subseq hu
  have hsunit : ‖s‖=1 := by simpa only [mem_sphere, dist_zero_right] using hs
  refine ⟨s, hsunit, ?_⟩
  intro α hα hαl
  obtain ⟨N, hN⟩ := eventually_atTop.mp (eventual_exp_lower A hA hl hαl)
  filter_upwards [eventually_ge_atTop (max N 1)] with n hn
  have hnN : N ≤ n := (le_max_left _ _).trans hn
  have hn1 : 1 ≤ n := (le_max_right _ _).trans hn
  have hb : ‖A n s‖ ≤ ‖A n‖⁻¹ + ‖A n‖ *
      (tailConstant M α * Real.exp (-2*α*(n : ℝ))) := by
    apply le_of_tendsto ((A n).continuous.norm.tendsto s |>.comp hlim)
    filter_upwards [hφ.tendsto_atTop.eventually (eventually_ge_atTop n)] with j hj
    have hh := stable_prefix_finite_bound A a (fun i => ‖A i‖) M n (φ j) hn1 hj
      (fun i _ _ => hA i) (fun i _ _ => hau i) (fun _ _ _ => rfl)
      (fun i _ _ => ham i) (fun i _ _ => has i) (fun i _ _ => hstep i)
    have ht := stable_error_exp_bound (fun i => ‖A i‖) M α hM.le hα n (φ j) hj
      (fun i hni _ => hN i (hnN.trans hni))
    exact hh.trans (add_le_add le_rfl (mul_le_mul_of_nonneg_left ht (norm_nonneg _)))
  have hi := inverse_bound_by_exp ‖A n‖ α n (hN n hnN)
  calc
    _ ≤ ‖A n‖*Real.exp (-2*α*(n : ℝ)) +
        ‖A n‖*(tailConstant M α*Real.exp (-2*α*(n : ℝ))) := add_le_add hi le_rfl |>.trans' hb
    _ = _ := by ring

lemma all_growth_zero (hA : ∀ n, PlaneAreaPreserving (A n))
    (hl : Tendsto (fun n : ℕ => Real.log ‖A n‖ / (n : ℝ)) atTop (𝓝 0))
    (v : ℂ) (hv : v ≠ 0) : Growth A v 0 := by
  refine ⟨hv, ?_⟩
  have hvpos := norm_pos_iff.mpr hv
  have hc : Tendsto (fun n : ℕ => Real.log ‖v‖ / (n : ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  have hlo : Tendsto (fun n : ℕ =>
      Real.log ‖v‖/(n : ℝ)-Real.log ‖A n‖/(n : ℝ)) atTop (𝓝 0) := by
    simpa only [sub_zero] using hc.sub hl
  have hup : Tendsto (fun n : ℕ =>
      Real.log ‖A n‖/(n : ℝ)+Real.log ‖v‖/(n : ℝ)) atTop (𝓝 0) := by
    simpa only [add_zero] using hl.add hc
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hlo hup
  · filter_upwards [eventually_gt_atTop 0] with n hn
    have hh := Real.log_le_log hvpos ((hA n).norm_lower v)
    rw [Real.log_mul (norm_pos A hA n).ne' (image_norm_pos A hA hv n).ne'] at hh
    have hh' : Real.log ‖v‖-Real.log ‖A n‖ ≤ Real.log ‖A n v‖ := by linarith
    simpa only [sub_div] using div_le_div_of_nonneg_right hh' (Nat.cast_nonneg n)
  · filter_upwards [eventually_gt_atTop 0] with n hn
    have hh := Real.log_le_log (image_norm_pos A hA hv n) ((A n).le_opNorm v)
    rw [Real.log_mul (norm_pos A hA n).ne' hvpos.ne'] at hh
    simpa only [add_div] using div_le_div_of_nonneg_right hh (Nat.cast_nonneg n)

lemma stable_growth (hA : ∀ n, PlaneAreaPreserving (A n)) (M : ℝ) (hM : 0 < M)
    {l : ℝ} (hlpos : 0 < l)
    (hl : Tendsto (fun n : ℕ => Real.log ‖A n‖ / (n : ℝ)) atTop (𝓝 l))
    (s : ℂ) (hs : ‖s‖=1)
    (hbound : ∀ α : ℝ, 0 < α → α < l →
      ∀ᶠ n : ℕ in atTop, ‖A n s‖ ≤
        ‖A n‖*(1+tailConstant M α)*Real.exp (-2*α*(n : ℝ))) : Growth A s (-l) := by
  have hsne : s ≠ 0 := by intro h; simp [h] at hs
  have hlow (n : ℕ) : -Real.log ‖A n‖/(n : ℝ) ≤ Real.log ‖A n s‖/(n : ℝ) := by
    have hh := (hA n).norm_lower s
    rw [hs] at hh
    have hhlog := Real.log_le_log zero_lt_one hh
    rw [Real.log_one, Real.log_mul (norm_pos A hA n).ne'
      (image_norm_pos A hA hsne n).ne'] at hhlog
    apply div_le_div_of_nonneg_right (by linarith) (Nat.cast_nonneg n)
  refine ⟨hsne, tendsto_order.mpr ⟨?_, ?_⟩⟩
  · intro b hb
    have hh : Tendsto (fun n : ℕ => -Real.log ‖A n‖/(n : ℝ)) atTop (𝓝 (-l)) := by
      simpa only [neg_div] using hl.neg
    filter_upwards [(tendsto_order.mp hh).1 b hb] with n hn
    exact hn.trans_le (hlow n)
  · intro b hb
    have hc : max 0 ((l-b)/2) < l := max_lt hlpos (by linarith)
    obtain ⟨α, hαlo, hαhi⟩ := exists_between hc
    have hα : 0 < α := (le_max_left _ _).trans_lt hαlo
    have hαb : l-2*α < b := by
      have := (le_max_right 0 ((l-b)/2)).trans_lt hαlo
      linarith
    have hC : 0 < 1+tailConstant M α := by
      have := tailConstant_pos hM hα
      linarith
    have hu : Tendsto (fun n : ℕ =>
        Real.log ‖A n‖/(n : ℝ)+Real.log (1+tailConstant M α)/(n : ℝ)-2*α)
        atTop (𝓝 (l-2*α)) := by
      have hh := (hl.add (tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop :
        Tendsto (fun n : ℕ => Real.log (1+tailConstant M α)/(n : ℝ)) atTop (𝓝 0))).sub
        (tendsto_const_nhds (x := 2*α))
      simpa only [add_zero] using hh
    filter_upwards [hbound α hα hαhi, (tendsto_order.mp hu).2 b hαb,
      eventually_gt_atTop 0] with n hn hnb hn0
    have hnpos : (0 : ℝ) < n := by exact_mod_cast hn0
    have hh := Real.log_le_log (image_norm_pos A hA hsne n) hn
    rw [Real.log_mul (mul_pos (norm_pos A hA n) hC).ne' (Real.exp_pos _).ne',
      Real.log_mul (norm_pos A hA n).ne' hC.ne', Real.log_exp] at hh
    have hdiv := div_le_div_of_nonneg_right hh hnpos.le
    have he : (Real.log ‖A n‖+Real.log (1+tailConstant M α)+ -2*α*(n : ℝ))/(n : ℝ) =
        Real.log ‖A n‖/(n : ℝ)+Real.log (1+tailConstant M α)/(n : ℝ)-2*α := by
      rw [add_div, add_div, mul_div_cancel_right₀ _ hnpos.ne']
      ring
    rw [he] at hdiv
    exact hdiv.trans_lt hnb

lemma growth_on_line (hA : ∀ n, PlaneAreaPreserving (A n))
    {s : ℂ} {l : ℝ} (hsunit : ‖s‖=1) (hs : Growth A s l)
    (v : ℂ) (hv : v ≠ 0) (halign : wedge s v=0) : Growth A v l := by
  have he : v = dot s v • s := by simpa only [halign, zero_smul, add_zero] using unit_expansion s v hsunit
  have hd : dot s v ≠ 0 := by
    intro hz
    rw [hz, zero_smul] at he
    exact hv he
  have hc : Tendsto (fun n : ℕ => Real.log |dot s v|/(n : ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  refine ⟨hv, ?_⟩
  have hh := hc.add hs.2
  simp only [zero_add] at hh
  apply hh.congr'
  exact Eventually.of_forall fun n => by
    dsimp only
    conv_rhs => rw [he, map_smul, norm_smul, Real.norm_eq_abs,
      Real.log_mul (abs_pos.mpr hd).ne' (image_norm_pos A hA hs.1 n).ne', add_div]

lemma growth_off_line (hA : ∀ n, PlaneAreaPreserving (A n))
    {l : ℝ} (hl : Tendsto (fun n : ℕ => Real.log ‖A n‖ / (n : ℝ)) atTop (𝓝 l))
    {s : ℂ} (hs : Growth A s (-l)) (v : ℂ) (hv : v ≠ 0) (hoff : wedge s v ≠ 0) :
    Growth A v l := by
  have hws : 0 < |wedge s v| := abs_pos.mpr hoff
  have hvpos : 0 < ‖v‖ := norm_pos_iff.mpr hv
  have hlo : Tendsto (fun n : ℕ =>
      Real.log |wedge s v|/(n : ℝ)-Real.log ‖A n s‖/(n : ℝ)) atTop (𝓝 l) := by
    have hc : Tendsto (fun n : ℕ => Real.log |wedge s v|/(n : ℝ)) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
    simpa using hc.sub hs.2
  have hup : Tendsto (fun n : ℕ =>
      Real.log ‖A n‖/(n : ℝ)+Real.log ‖v‖/(n : ℝ)) atTop (𝓝 l) := by
    have hc : Tendsto (fun n : ℕ => Real.log ‖v‖/(n : ℝ)) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
    simpa using hl.add hc
  refine ⟨hv, tendsto_of_tendsto_of_tendsto_of_le_of_le hlo hup ?_ ?_⟩
  · intro n
    have hh := abs_wedge_le_norm_mul (A n s) (A n v)
    rw [hA n] at hh
    have hhlog := Real.log_le_log hws hh
    rw [Real.log_mul (image_norm_pos A hA hs.1 n).ne' (image_norm_pos A hA hv n).ne'] at hhlog
    have hsub : Real.log |wedge s v|-Real.log ‖A n s‖ ≤ Real.log ‖A n v‖ := by linarith
    simpa only [sub_div] using div_le_div_of_nonneg_right hsub (Nat.cast_nonneg n)
  · intro n
    have hh := Real.log_le_log (image_norm_pos A hA hv n) ((A n).le_opNorm v)
    rw [Real.log_mul (norm_pos A hA n).ne' hvpos.ne'] at hh
    simpa only [add_div] using div_le_div_of_nonneg_right hh (Nat.cast_nonneg n)

theorem positive_flag (hA : ∀ n, PlaneAreaPreserving (A n))
    (M : ℝ) (hM : 0 < M) (hstep : ∀ n v, ‖A n v‖ ≤ M*‖A (n+1) v‖)
    {l : ℝ} (hlpos : 0 < l)
    (hl : Tendsto (fun n : ℕ => Real.log ‖A n‖ / (n : ℝ)) atTop (𝓝 l)) :
    ∃ s : ℂ, s ≠ 0 ∧ ∀ v : ℂ, v ≠ 0 → Growth A v (if wedge s v=0 then -l else l) := by
  obtain ⟨s, hsunit, hsbound⟩ := exists_stable_bound A hA M hM hstep hl
  have hs := stable_growth A hA M hM hlpos hl s hsunit hsbound
  refine ⟨s, hs.1, ?_⟩
  intro v hv
  by_cases hw : wedge s v=0
  · simp only [ite_eq_left hw]
    exact growth_on_line A hA hsunit hs v hv hw
  · simp only [ite_eq_right hw]
    exact growth_off_line A hA hl hs v hv hw

end PlaneLyapunov
end StandardMapEntropy

end
end

end OAI
