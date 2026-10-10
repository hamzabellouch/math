import OAI.Geometry.TranslativeCovering.PatternEnumeration

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal

namespace RadialShell
open Filter
open scoped Topology
noncomputable def η (n : ℕ) : ℝ := ((n:ℝ)⁻¹)^4
noncomputable def low (a : ℝ) (n : ℕ) : ℝ := a*(1-10*(Real.log n/(n:ℝ)))-3*η n
noncomputable def high (a : ℝ) (n : ℕ) : ℝ := a*(1+(n:ℝ)⁻¹)+3*η n

lemma inv_limit : Tendsto (fun n : ℕ => (n:ℝ)⁻¹) atTop (𝓝 0) :=
  tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
lemma eta_limit : Tendsto η atTop (𝓝 0) := by
  unfold η
  simpa only [zero_pow (by norm_num : (4:ℕ) ≠ 0)] using inv_limit.pow 4
lemma log_div_limit : Tendsto (fun n : ℕ => Real.log n/(n:ℝ)) atTop (𝓝 0) := by
  have ht : Tendsto (fun x : ℝ => Real.log x/x) atTop (𝓝 0) := by
    simpa using Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero
  exact ht.comp tendsto_natCast_atTop_atTop
lemma low_limit (a : ℝ) : Tendsto (low a) atTop (𝓝 a) := by
  unfold low
  simpa using (((tendsto_const_nhds (x := (1:ℝ))).sub (log_div_limit.const_mul 10)).const_mul a).sub (eta_limit.const_mul 3)
lemma high_limit (a : ℝ) : Tendsto (high a) atTop (𝓝 a) := by
  unfold high
  simpa using (((tendsto_const_nhds (x := (1:ℝ))).add inv_limit).const_mul a).add (eta_limit.const_mul 3)

lemma n_eta {n : ℕ} (hn : 1 ≤ n) : (n:ℝ)*η n ≤ 1 := by
  have hnreal : (1:ℝ) ≤ n := by exact_mod_cast hn
  have hnp : (0:ℝ) < n := by linarith
  have hinv : (n:ℝ)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hnreal
  have hinv0 : (0:ℝ) ≤ (n:ℝ)⁻¹ := inv_nonneg.mpr hnp.le
  have hpow : ((n:ℝ)⁻¹)^4 ≤ (n:ℝ)⁻¹ := by nlinarith [sq_nonneg ((n:ℝ)⁻¹),sq_nonneg (1-(n:ℝ)⁻¹),mul_le_mul_of_nonneg_left hinv hinv0, mul_le_mul_of_nonneg_right (pow_le_one₀ (n := 3) hinv0 hinv) hinv0]
  calc
    (n:ℝ)*η n ≤ (n:ℝ)*(n:ℝ)⁻¹ := mul_le_mul_of_nonneg_left hpow hnp.le
    _ = 1 := mul_inv_cancel₀ hnp.ne'

lemma thresholds {a l u : ℝ} (ha : 0 < a) (hl : l < 1/a) (hu : 1/a < u) :
    ∃ n₀ : ℕ,∀ n : ℕ,n₀ ≤ n → 2 ≤ n ∧ 1 ≤ Real.log n ∧
      a/2 ≤ low a n ∧ (n:ℝ)*η n ≤ 1 ∧
      ∀ r : ℝ,low a n ≤ r → r ≤ high a n →
        l ≤ (1+3*η n)/r ∧ (1+3*η n)/r ≤ u := by
  have hupper : Tendsto (fun n => (1+3*η n)/low a n) atTop (𝓝 (1/a)) := by
    convert ((tendsto_const_nhds (x := (1:ℝ))).add (eta_limit.const_mul 3)).div (low_limit a) ha.ne' using 1
    first | rfl | simp
  have hlower : Tendsto (fun n => (1+3*η n)/high a n) atTop (𝓝 (1/a)) := by
    convert ((tendsto_const_nhds (x := (1:ℝ))).add (eta_limit.const_mul 3)).div (high_limit a) ha.ne' using 1
    first | rfl | simp
  have hev : ∀ᶠ n : ℕ in atTop,2 ≤ n ∧ 1 ≤ Real.log n ∧ a/2 ≤ low a n ∧
      (1+3*η n)/low a n ≤ u ∧ l ≤ (1+3*η n)/high a n := by
    filter_upwards [eventually_ge_atTop 2,
      (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually (eventually_ge_atTop 1),
      (low_limit a).eventually_const_le (by linarith : a/2 < a),
      hupper.eventually_le_const hu,hlower.eventually_const_le hl] with n hn hlog hlo hup hdown
    exact ⟨hn,hlog,hlo,hup,hdown⟩
  obtain ⟨n₀,hn₀⟩ := eventually_atTop.mp hev
  refine ⟨n₀,?_⟩
  intro n hn
  obtain ⟨hn2,hlog,hlo,hup,hdown⟩ := hn₀ n hn
  refine ⟨hn2,hlog,hlo,n_eta (by omega),?_⟩
  intro r hr hrü
  have hlo0 : 0 < low a n := lt_of_lt_of_le (by linarith) hlo
  have hr0 : 0 < r := hlo0.trans_le hr
  have hnum : 0 ≤ 1+3*η n := by unfold η; positivity
  exact ⟨hdown.trans (div_le_div_of_nonneg_left hnum hr0 hrü),
    (div_le_div_of_nonneg_left hnum hlo0 hr).trans hup⟩

lemma weight_upper {n : ℕ} {a r : ℝ} (ha : 1 ≤ a)
    (hlog : 1 ≤ Real.log n) (_hr : 0 ≤ r) (hlo : low a n ≤ r)
    (hnη : (n:ℝ)*η n ≤ 1) :
    1+(n:ℝ)*max (1-r^2/a^2) 0 ≤ 27*Real.log n := by
  have hap : 0 < a := by linarith
  have hnpos : (0:ℝ) < n := by
    by_contra h
    have hz : n = 0 := by exact_mod_cast le_antisymm (le_of_not_gt h) (Nat.cast_nonneg n)
    simp [hz] at hlog
    norm_num at hlog
  have hx : a-r ≤ 10*a*(Real.log n/(n:ℝ))+3*η n := by
    dsimp [low] at hlo
    linarith only [hlo]
  have hq : max (1-r^2/a^2) 0 ≤ (20*Real.log n/(n:ℝ))+6*η n/a := by
    apply max_le _ (by unfold η; positivity)
    apply (mul_le_mul_iff_right₀ (sq_pos_of_pos hap)).mp
    have hh := mul_le_mul_of_nonneg_left hx (by linarith : 0 ≤ 2*a)
    have hh2 : a^2-r^2 ≤ 2*a*(10*a*(Real.log n/(n:ℝ))+3*η n) := by
      nlinarith only [hh,sq_nonneg (a-r)]
    convert hh2 using 1 <;> (try field_simp [hap.ne'])
    first | rfl | ring
  have hh := mul_le_mul_of_nonneg_left hq hnpos.le
  have he : (n:ℝ)*(20*Real.log n/(n:ℝ)+6*η n/a) = 20*Real.log n+6*((n:ℝ)*η n)/a := by field_simp
  rw [he] at hh
  have hdiv : ((n:ℝ)*η n)/a ≤ 1 := (div_le_one hap).mpr (hnη.trans ha)
  rw [mul_div_assoc 6] at hh
  linarith only [hh,hdiv,hlog]

end RadialShell

end OAI
