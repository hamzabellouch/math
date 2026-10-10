import OAI.Analysis.DiskMaximal.Basic

namespace OAI

open MeasureTheory Set
open scoped ENNReal NNReal Topology ContDiff
open scoped RealInnerProductSpace
open MeasureTheory Set Filter
open scoped Topology ENNReal
open scoped Real RealInnerProductSpace

noncomputable section

namespace DiskGeometry
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem mem_tangent_ball_iff {z y θ : E} (hθ : ‖θ‖ = 1) {L : ℝ} (hL : 0 < L) :
    y ∈ Metric.ball (z + L • θ) L ↔ ‖y - z‖ ^ 2 < 2 * L * ⟪y - z, θ⟫ := by
  rw [Metric.mem_ball, dist_eq_norm]
  have hv : y - (z + L • θ) = (y - z) - L • θ := by abel
  rw [hv, ← sq_lt_sq₀ (norm_nonneg _) hL.le, norm_sub_sq_real,
    norm_smul, Real.norm_eq_abs, abs_of_pos hL, hθ, mul_one, real_inner_smul_right]
  constructor <;> intro h <;> nlinarith

theorem tangent_ball_mono {z θ : E} (hθ : ‖θ‖ = 1) {L L' : ℝ}
    (hL : 0 < L) (hLL' : L ≤ L') :
    Metric.ball (z + L • θ) L ⊆ Metric.ball (z + L' • θ) L' := by
  intro y hy
  rw [mem_tangent_ball_iff hθ hL] at hy
  rw [mem_tangent_ball_iff hθ (hL.trans_le hLL')]
  have hinner : 0 < ⟪y - z, θ⟫ := by
    by_contra hh
    have hh' : ⟪y - z, θ⟫ ≤ 0 := le_of_not_gt hh
    have := mul_nonpos_of_nonneg_of_nonpos (show 0 ≤ 2 * L by positivity) hh'
    nlinarith [sq_nonneg ‖y - z‖]
  exact hy.trans_le (mul_le_mul_of_nonneg_right (by linarith) hinner.le)

def entryParameter (z y θ : E) : ℝ := ‖y - z‖ ^ 2 / (2 * ⟪y - z, θ⟫)

theorem mem_tangent_ball_iff_entry {z y θ : E} (hθ : ‖θ‖ = 1)
    {L : ℝ} (hL : 0 < L) (ha : 0 < ⟪y - z, θ⟫) :
    y ∈ Metric.ball (z + L • θ) L ↔ entryParameter z y θ < L := by
  rw [mem_tangent_ball_iff hθ hL, entryParameter, div_lt_iff₀ (by positivity)]
  ring_nf

/-- Uniform estimate on the affine difference of squared distances in a thin shell. -/
theorem shell_square_error {l δ d : ℝ} (hl : 0 ≤ l) (hl3 : l ≤ 3)
    (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1 / 4) (hd : 0 ≤ d) (hclose : |d - l| ≤ 2 * δ) :
    |d ^ 2 - l ^ 2| ≤ 13 * δ := by
  have hd_upper : d ≤ l + 2 * δ := (abs_le.mp hclose).2 |> fun h => by linarith
  have hsum : 0 ≤ d + l := add_nonneg hd hl
  calc
    |d ^ 2 - l ^ 2| = |d - l| * (d + l) := by
      rw [show d ^ 2 - l ^ 2 = (d - l) * (d + l) by ring, abs_mul, abs_of_nonneg hsum]
    _ ≤ (2 * δ) * (d + l) := mul_le_mul_of_nonneg_right hclose hsum
    _ ≤ 13 * δ := by nlinarith

/-- A shell point separated from the tangency point has positive radial projection. -/
theorem shell_projection_lower {ρ δ l a w2 : ℝ}
    (hρ : 0 < ρ) (hl : 0 < l) (hl3 : l ≤ 3)
    (hδ : δ ≤ ρ ^ 2 / 1600) (hw : ρ ^ 2 ≤ w2)
    (herr : |w2 - 2 * l * a| ≤ 13 * δ) :
    ρ ^ 2 / 12 ≤ a := by
  have hr2 : 0 < ρ ^ 2 := sq_pos_of_pos hρ
  have he := (abs_le.mp herr).2
  have hla : 0 < a := by nlinarith
  nlinarith

theorem entry_window {ρ δ l a w2 : ℝ}
    (hρ : 0 < ρ) (hδ : 0 ≤ δ) (ha : ρ ^ 2 / 12 ≤ a)
    (herr : |w2 - 2 * l * a| ≤ 13 * δ) :
    |w2 / (2 * a) - l| ≤ 78 * δ / ρ ^ 2 := by
  have hr2 : 0 < ρ ^ 2 := sq_pos_of_pos hρ
  have ha0 : 0 < a := lt_of_lt_of_le (by positivity) ha
  have h2a : 0 < 2 * a := by positivity
  rw [show w2 / (2 * a) - l = (w2 - 2 * l * a) / (2 * a) by field_simp,
    abs_div, abs_of_pos h2a]
  calc
    |w2 - 2 * l * a| / (2 * a) ≤ 13 * δ / (2 * a) :=
      div_le_div_of_nonneg_right herr h2a.le
    _ ≤ 78 * δ / ρ ^ 2 := by
      apply (div_le_div_iff₀ h2a hr2).2
      nlinarith [mul_le_mul_of_nonneg_right ha hδ]

/-- Bound for the entry parameter for an actual shell near a tangent disk. -/
theorem shell_entry_window {z y θ : E} (hθ : ‖θ‖ = 1) {l ρ δ : ℝ}
    (hl : 1 / 2 ≤ l) (hl3 : l ≤ 3) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1)
    (hδ : 0 < δ) (hδρ : δ ≤ ρ ^ 2 / 1600)
    (hsep : ρ ≤ ‖y - z‖)
    (hclose : |dist y (z + l • θ) - l| ≤ 2 * δ) :
    ρ ^ 2 / 12 ≤ ⟪y - z, θ⟫ ∧
    |entryParameter z y θ - l| ≤ 78 * δ / ρ ^ 2 := by
  have hl0 : 0 < l := by linarith
  have hδ1 : δ ≤ 1 / 4 := by nlinarith
  have hsq : ρ ^ 2 ≤ ‖y - z‖ ^ 2 :=
    (sq_le_sq₀ hρ.le (norm_nonneg _)).2 hsep
  have hd := shell_square_error hl0.le hl3 hδ.le hδ1 (dist_nonneg (x := y)) hclose
  have hv : y - (z + l • θ) = (y - z) - l • θ := by abel
  have herr : |‖y - z‖ ^ 2 - 2 * l * ⟪y - z, θ⟫| ≤ 13 * δ := by
    rw [dist_eq_norm, hv, norm_sub_sq_real, real_inner_smul_right, norm_smul,
      Real.norm_eq_abs, abs_of_pos hl0, hθ, mul_one] at hd
    convert hd using 1
    congr 1
    ring
  have ha := shell_projection_lower hρ hl0 hl3 hδρ hsq herr
  exact ⟨ha, entry_window hρ hδ.le ha herr⟩

theorem earlier_tangent_disk_subset {z θ : E} (hθ : ‖θ‖ = 1) {l ρ δ : ℝ}
    (hl : 1 / 2 ≤ l) (hl3 : l ≤ 3) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1)
    (hδ : 0 < δ) (hδρ : δ ≤ ρ ^ 2 / 1600) :
    {y : E | ρ ≤ ‖y - z‖} ∩
      Metric.ball (z + (l - 200 * δ / ρ ^ 2) • θ) (l - 200 * δ / ρ ^ 2) ⊆
      Metric.ball (z + l • θ) (l - 2 * δ) := by
  let v : ℝ := 200 * δ / ρ ^ 2
  have hr2 : 0 < ρ ^ 2 := sq_pos_of_pos hρ
  have hvpos : 0 < v := by dsimp [v]; positivity
  have hvsmall : v ≤ 1 / 8 := by
    dsimp [v]
    apply (div_le_iff₀ hr2).2
    linarith
  have hv_eq : v * ρ ^ 2 = 200 * δ := by
    dsimp [v]; exact div_mul_cancel₀ _ hr2.ne'
  have hl0 : 0 < l := by linarith
  have hlv : 0 < l - v := by linarith
  have hδquarter : δ ≤ 1 / 4 := by nlinarith
  have hrad : 0 < l - 2 * δ := by nlinarith
  rintro y ⟨hsep, hy⟩
  change y ∈ Metric.ball (z + (l - v) • θ) (l - v) at hy
  rw [mem_tangent_ball_iff hθ hlv] at hy
  have hnorm : ρ ^ 2 ≤ ‖y - z‖ ^ 2 :=
    (sq_le_sq₀ hρ.le (norm_nonneg _)).2 hsep
  have hapos : 0 < ⟪y - z, θ⟫ := by
    by_contra ha
    have hmul := mul_nonpos_of_nonneg_of_nonpos
      (show 0 ≤ 2 * (l - v) by positivity) (le_of_not_gt ha)
    nlinarith
  have halower : ρ ^ 2 / 6 < ⟪y - z, θ⟫ := by nlinarith
  have hva := mul_lt_mul_of_pos_left halower hvpos
  have hsqdist : dist y (z + l • θ) ^ 2 < (l - 2 * δ) ^ 2 := by
    rw [dist_eq_norm, show y - (z + l • θ) = (y - z) - l • θ by abel,
      norm_sub_sq_real, real_inner_smul_right, norm_smul, Real.norm_eq_abs,
      abs_of_pos hl0, hθ, mul_one]
    nlinarith [mul_le_mul_of_nonneg_right hl3 hδ.le]
  exact (sq_lt_sq₀ dist_nonneg hrad.le).1 hsqdist

end DiskGeometry

namespace DiskGeometry

/-- Cancellation of translated monotone integrals on a finite interval. -/
theorem monotone_increment_interval {G : ℝ → ℝ} (hG : Monotone G)
    {C v : ℝ} (h0 : ∀ x, 0 ≤ G x) (hC : ∀ x, G x ≤ C) (hv : 0 ≤ v)
    (a b : ℝ) :
    (∫ l in a..b, (G (l + v) - G (l - v))) ≤ 2 * v * C := by
  have hp : Monotone (fun l => G (l + v)) := hG.comp (by intro x y h; dsimp; linarith)
  have hm : Monotone (fun l => G (l - v)) := hG.comp (fun _ _ h => sub_le_sub_right h v)
  rw [intervalIntegral.integral_sub hp.intervalIntegrable hm.intervalIntegrable,
    intervalIntegral.integral_comp_add_right, intervalIntegral.integral_comp_sub_right,
    intervalIntegral.integral_interval_sub_interval_comm' hG.intervalIntegrable
      hG.intervalIntegrable hG.intervalIntegrable]
  have hn : 0 ≤ ∫ l in a - v..a + v, G l :=
    intervalIntegral.integral_nonneg_of_forall (by linarith) h0
  have hb : (∫ l in b - v..b + v, G l) ≤ 2 * v * C := by
    calc
      (∫ l in b - v..b + v, G l) ≤ ∫ l in b - v..b + v, C :=
        intervalIntegral.integral_mono (by linarith) hG.intervalIntegrable
          intervalIntegrable_const hC
      _ = 2 * v * C := by
        rw [intervalIntegral.integral_const]
        change ((b + v) - (b - v)) * C = _
        ring
  linarith

theorem monotone_increment_integrable {G : ℝ → ℝ} (hG : Monotone G)
    {C v : ℝ} (h0 : ∀ x, 0 ≤ G x) (hC : ∀ x, G x ≤ C) (hv : 0 ≤ v) :
    Integrable (fun l => G (l + v) - G (l - v)) ∧
      (∫ l, (G (l + v) - G (l - v))) ≤ 2 * v * C := by
  have hp : Monotone (fun l => G (l + v)) := hG.comp (by intro x y h; dsimp; linarith)
  have hm : Monotone (fun l => G (l - v)) := hG.comp (fun _ _ h => sub_le_sub_right h v)
  have hn (l : ℝ) : 0 ≤ G (l + v) - G (l - v) := sub_nonneg.mpr (hG (by linarith))
  have hi (a b : ℝ) : IntervalIntegrable (fun l => G (l + v) - G (l - v)) volume a b :=
    hp.intervalIntegrable.sub hm.intervalIntegrable
  have htop : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have hbot : Tendsto (fun n : ℕ => -(n : ℝ)) atTop atBot := tendsto_neg_atTop_atBot.comp htop
  have hint : Integrable (fun l => G (l + v) - G (l - v)) := by
    apply integrable_of_intervalIntegral_norm_bounded (2 * v * C)
      (fun n : ℕ => (hi (-(n : ℝ)) n).1) hbot htop
    exact Eventually.of_forall (fun n => by
      simp_rw [Real.norm_of_nonneg (hn _)]
      exact monotone_increment_interval hG h0 hC hv _ _)
  refine ⟨hint, ?_⟩
  exact le_of_tendsto (intervalIntegral_tendsto_integral hint hbot htop)
    (Eventually.of_forall (fun n => monotone_increment_interval hG h0 hC hv (-(n : ℝ)) n))

/-- The permitted jump times have uniformly bounded length, independent of the
size of the original positive measure. Only its truncated distribution is used. -/
theorem monotone_jump_window_measure {H : ℝ → ℝ} (hH : Monotone H)
    (hH0 : ∀ l, 0 ≤ H l) {T U v : ℝ} (hT : 0 ≤ T) (hU : 0 < U) (hv : 0 ≤ v) :
    volume {l | H (l - v) ≤ T ∧ U ≤ H (l + v) - H (l - v)} ≤
      ENNReal.ofReal (2 * v * (1 + T / U)) := by
  let G : ℝ → ℝ := fun l => min (H l) (T + U)
  have hG : Monotone G := hH.min monotone_const
  have hG0 : ∀ l, 0 ≤ G l := fun l => le_min (hH0 l) (by positivity)
  have hGC : ∀ l, G l ≤ T + U := fun l => min_le_right _ _
  obtain ⟨hi, hb⟩ := monotone_increment_integrable hG hG0 hGC hv
  have hn (l : ℝ) : 0 ≤ G (l + v) - G (l - v) := sub_nonneg.mpr (hG (by linarith))
  have hmi : Integrable (fun l => (G (l + v) - G (l - v)) / U) := hi.div_const U
  have hm := hmi.measure_le_integral
    (Eventually.of_forall (fun l => div_nonneg (hn l) hU.le))
    (s := {l | H (l - v) ≤ T ∧ U ≤ H (l + v) - H (l - v)}) (by
      intro l hl
      rw [le_div_iff₀ hU, one_mul]
      have hd : G (l - v) = H (l - v) := min_eq_left (by linarith [hl.1])
      rw [hd]
      change U ≤ min (H (l + v)) (T + U) - H (l - v)
      rw [le_sub_iff_add_le, le_min_iff]
      exact ⟨by linarith [hl.2], by linarith [hl.1]⟩)
  calc
    volume {l | H (l - v) ≤ T ∧ U ≤ H (l + v) - H (l - v)} ≤
        ENNReal.ofReal (∫ l, (G (l + v) - G (l - v)) / U) := hm
    _ ≤ ENNReal.ofReal (2 * v * (1 + T / U)) := by
      apply ENNReal.ofReal_le_ofReal
      rw [integral_div]
      calc
        (∫ l, G (l + v) - G (l - v)) / U ≤ (2 * v * (T + U)) / U :=
          div_le_div_of_nonneg_right hb hU.le
        _ = 2 * v * (1 + T / U) := by field_simp; ring

end DiskGeometry

namespace DiskGeometry

/-- A polar-coordinate area bound from uniform lengths of radial sections. -/
theorem volume_le_radial_sections {s : Set ℂ} (hs : MeasurableSet s)
    (z : ℂ) {R : ℝ} (hR : 0 ≤ R) {B : ℝ≥0∞}
    (hbound : ∀ x ∈ s, ‖x - z‖ ≤ R)
    (hsections : ∀ θ : ℝ, volume {r : ℝ | 0 < r ∧
      z + (r : ℂ) * ((Real.cos θ : ℂ) + (Real.sin θ : ℂ) * Complex.I) ∈ s} ≤ B) :
    volume s ≤ ENNReal.ofReal (2 * Real.pi * R) * B := by
  classical
  let f : ℂ → ℝ≥0∞ := s.indicator 1
  have hf : Measurable f := measurable_const.indicator hs
  have hfc : Measurable (fun p : ℝ × ℝ => f (z + Complex.polarCoord.symm p)) := by
    apply hf.comp
    simp only [Complex.polarCoord_symm_apply]
    fun_prop
  have hpolar : volume s = ∫⁻ p in polarCoord.target,
      ENNReal.ofReal p.1 * f (z + Complex.polarCoord.symm p) := by
    rw [← lintegral_indicator_one hs]
    change (∫⁻ x, f x) = _
    rw [← lintegral_add_left_eq_self f z,
      ← Complex.lintegral_comp_polarCoord_symm (fun x => f (z + x))]
    rfl
  have hinner (θ : ℝ) : (∫⁻ r in Ioi (0 : ℝ), f (z + Complex.polarCoord.symm (r, θ))) ≤ B := by
    let A : Set ℝ := {r | 0 < r ∧
      z + (r : ℂ) * ((Real.cos θ : ℂ) + (Real.sin θ : ℂ) * Complex.I) ∈ s}
    have hA : MeasurableSet A := measurableSet_Ioi.inter (hs.preimage (by fun_prop))
    calc
      _ = ∫⁻ r, A.indicator 1 r := by
        rw [← lintegral_indicator measurableSet_Ioi]
        apply lintegral_congr
        intro r
        by_cases hr : 0 < r <;>
        by_cases hx : z + (r : ℂ) * ((Real.cos θ : ℂ) + (Real.sin θ : ℂ) * Complex.I) ∈ s <;>
        simp only [f, A, Complex.polarCoord_symm_apply, Set.indicator_apply,
          mem_Ioi, mem_ofPred_eq, Pi.one_apply, hr, hx,
          and_true, and_false, ite_true, ite_false]
      _ = volume A := lintegral_indicator_one hA
      _ ≤ B := hsections θ
  calc
    volume s = ∫⁻ p in polarCoord.target,
        ENNReal.ofReal p.1 * f (z + Complex.polarCoord.symm p) := hpolar
    _ ≤ ∫⁻ p in polarCoord.target,
        ENNReal.ofReal R * f (z + Complex.polarCoord.symm p) := by
      apply setLIntegral_mono' polarCoord.open_target.measurableSet
      intro p hp
      by_cases hx : z + Complex.polarCoord.symm p ∈ s
      · gcongr
        have hn := hbound _ hx
        rw [add_sub_cancel_left, Complex.norm_polarCoord_symm, abs_of_pos hp.1] at hn
        exact hn
      · simp only [f, indicator_of_notMem hx, mul_zero, le_refl]
    _ = ENNReal.ofReal R * ∫⁻ θ in Ioo (-Real.pi) Real.pi,
        ∫⁻ r in Ioi (0 : ℝ), f (z + Complex.polarCoord.symm (r, θ)) := by
      rw [lintegral_const_mul _ hfc]
      congr 1
      exact setLIntegral_prod_symm _ hfc.aemeasurable
    _ ≤ ENNReal.ofReal R * ∫⁻ θ in Ioo (-Real.pi) Real.pi, B := by
      gcongr with θ
      exact hinner θ
    _ = ENNReal.ofReal (2 * Real.pi * R) * B := by
      rw [lintegral_const, Measure.restrict_apply_univ, Real.volume_Ioo]
      rw [show Real.pi - -Real.pi = 2 * Real.pi by ring]
      rw [mul_comm (2 * Real.pi) R, ENNReal.ofReal_mul hR]
      ac_rfl

end DiskGeometry

namespace DiskGeometry

/-- Mass in the increasing family of tangent disks, away from its tangency cap. -/
def tangentMass (S : Measure ℂ) (ρ : ℝ) (z θ : ℂ) (L : ℝ) : ℝ :=
  (S ({y : ℂ | ρ ≤ ‖y - z‖} ∩ Metric.ball (z + L • θ) L)).toReal

theorem tangentMass_nonneg (S : Measure ℂ) (ρ : ℝ) (z θ : ℂ) (L : ℝ) :
    0 ≤ tangentMass S ρ z θ L := ENNReal.toReal_nonneg

theorem tangentMass_mono (S : Measure ℂ) [IsFiniteMeasure S] (ρ : ℝ)
    (z θ : ℂ) (hθ : ‖θ‖ = 1) : Monotone (tangentMass S ρ z θ) := by
  intro L L' hLL'
  by_cases hL : 0 < L
  · apply ENNReal.toReal_mono (measure_ne_top S _)
    exact measure_mono (inter_subset_inter_right _ (tangent_ball_mono hθ hL hLL'))
  · have hball : Metric.ball (z + L • θ) L = ∅ := Metric.ball_eq_empty.mpr (le_of_not_gt hL)
    simp only [tangentMass, hball, inter_empty, measure_empty, ENNReal.toReal_zero]
    exact ENNReal.toReal_nonneg

theorem measurable_tangentMass (S : Measure ℂ) [IsFiniteMeasure S] (ρ : ℝ)
    {α : Type*} [MeasurableSpace α] {z θ : α → ℂ} {L : α → ℝ}
    (hz : Measurable z) (hθ : Measurable θ) (hL : Measurable L) :
    Measurable (fun a => tangentMass S ρ (z a) (θ a) (L a)) := by
  have hm : MeasurableSet {p : α × ℂ | ρ ≤ ‖p.2 - z p.1‖ ∧
      dist p.2 (z p.1 + L p.1 • θ p.1) < L p.1} := by
    exact (measurableSet_le measurable_const ((measurable_snd.sub (hz.comp measurable_fst)).norm)).inter
      (measurableSet_lt (measurable_snd.dist ((hz.comp measurable_fst).add
        ((hL.comp measurable_fst).smul (hθ.comp measurable_fst)))) (hL.comp measurable_fst))
  exact (measurable_measure_prodMk_left (ν := S) hm).ennreal_toReal

/-- The measurable condition whose planar cost is bounded by the ray-length estimate. -/
def rayCondition (S : Measure ℂ) (ρ T U v : ℝ) (x z : ℂ) : Prop :=
  1 / 2 ≤ ‖x - z‖ ∧ ‖x - z‖ ≤ 3 ∧
    tangentMass S ρ z (‖x - z‖⁻¹ • (x - z)) (‖x - z‖ - v) ≤ T ∧
    U ≤ tangentMass S ρ z (‖x - z‖⁻¹ • (x - z)) (‖x - z‖ + v) -
      tangentMass S ρ z (‖x - z‖⁻¹ • (x - z)) (‖x - z‖ - v)

theorem measurableSet_rayCondition (S : Measure ℂ) [IsFiniteMeasure S]
    (ρ T U v : ℝ) : MeasurableSet {p : ℂ × ℂ | rayCondition S ρ T U v p.1 p.2} := by
  have hn : Measurable (fun p : ℂ × ℂ => ‖p.1 - p.2‖) := by fun_prop
  have hdir : Measurable (fun p : ℂ × ℂ => ‖p.1 - p.2‖⁻¹ • (p.1 - p.2)) := by fun_prop
  have hm := measurable_tangentMass S ρ measurable_snd hdir (hn.sub_const v)
  have hp := measurable_tangentMass S ρ measurable_snd hdir (hn.add_const v)
  exact (measurableSet_le measurable_const hn).inter
    ((measurableSet_le hn measurable_const).inter
      ((measurableSet_le hm measurable_const).inter (measurableSet_le measurable_const (hp.sub hm))))

/-- Full two-dimensional ray-condition estimate, independent of the chosen radius. -/
theorem volume_rayCondition (S : Measure ℂ) [IsFiniteMeasure S] (ρ : ℝ)
    {T U v : ℝ} (hT : 0 ≤ T) (hU : 0 < U) (hv : 0 ≤ v) (z : ℂ) :
    volume {x : ℂ | rayCondition S ρ T U v x z} ≤
      ENNReal.ofReal (6 * Real.pi) * ENNReal.ofReal (2 * v * (1 + T / U)) := by
  have hs : MeasurableSet {x : ℂ | rayCondition S ρ T U v x z} :=
    (measurableSet_rayCondition S ρ T U v).preimage
      (show Measurable (fun x : ℂ => (x, z)) by fun_prop)
  have hbound : ∀ x ∈ {x : ℂ | rayCondition S ρ T U v x z}, ‖x - z‖ ≤ 3 :=
    fun _ h => h.2.1
  have hsections (a : ℝ) : volume {r : ℝ | 0 < r ∧
      z + (r : ℂ) * ((Real.cos a : ℂ) + (Real.sin a : ℂ) * Complex.I) ∈
        {x : ℂ | rayCondition S ρ T U v x z}} ≤
      ENNReal.ofReal (2 * v * (1 + T / U)) := by
    let θ : ℂ := (Real.cos a : ℂ) + (Real.sin a : ℂ) * Complex.I
    have hθ : ‖θ‖ = 1 := by
      simpa only [θ, Complex.ofReal_cos, Complex.ofReal_sin] using Complex.norm_cos_add_sin_mul_I a
    apply le_trans (measure_mono (t := {l : ℝ | tangentMass S ρ z θ (l - v) ≤ T ∧
      U ≤ tangentMass S ρ z θ (l + v) - tangentMass S ρ z θ (l - v)}) ?_)
      (monotone_jump_window_measure (tangentMass_mono S ρ z θ hθ)
        (tangentMass_nonneg S ρ z θ) hT hU hv)
    rintro r ⟨hr, hx⟩
    have hnorm : ‖z + (r : ℂ) * θ - z‖ = r := by
      rw [add_sub_cancel_left, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr, hθ, mul_one]
    have hdir : ‖z + (r : ℂ) * θ - z‖⁻¹ • (z + (r : ℂ) * θ - z) = θ := by
      rw [hnorm, add_sub_cancel_left, ← Complex.real_smul, smul_smul, inv_mul_cancel₀ hr.ne', one_smul]
    change rayCondition S ρ T U v (z + (r : ℂ) * θ) z at hx
    rw [rayCondition] at hx
    rw [hdir, hnorm] at hx
    exact hx.2.2
  simpa only [show (2 : ℝ) * Real.pi * 3 = 6 * Real.pi by ring] using
    volume_le_radial_sections hs z (by norm_num : (0 : ℝ) ≤ 3) hbound hsections

end DiskGeometry

namespace DiskGeometry

def thinShell (x : ℂ) (r δ : ℝ) : Set ℂ := {y | |‖y - x‖ - r| ≤ δ}

theorem measurableSet_thinShell (x : ℂ) (r δ : ℝ) : MeasurableSet (thinShell x r δ) := by
  exact measurableSet_le (by fun_prop) measurable_const

theorem shell_center_bounds {x z : ℂ} {r δ : ℝ} (hr : r ∈ Icc (1 : ℝ) 2)
    (hδ : δ ≤ 1 / 4) (hz : z ∈ thinShell x r δ) :
    1 / 2 ≤ ‖x - z‖ ∧ ‖x - z‖ ≤ 3 := by
  change |‖z - x‖ - r| ≤ δ at hz
  have hh := abs_le.mp hz
  rw [norm_sub_rev z x] at hh
  constructor <;> linarith [hr.1, hr.2]

theorem shell_pair_close {x y z : ℂ} {r δ : ℝ}
    (hy : y ∈ thinShell x r δ) (hz : z ∈ thinShell x r δ) :
    |‖y - x‖ - ‖x - z‖| ≤ 2 * δ := by
  change |‖y - x‖ - r| ≤ δ at hy
  change |‖z - x‖ - r| ≤ δ at hz
  have hy' := abs_le.mp hy
  have hz' := abs_le.mp hz
  rw [norm_sub_rev z x] at hz'
  exact abs_le.mpr ⟨by linarith [hy'.1, hz'.2], by linarith [hy'.2, hz'.1]⟩

/-- Every distant point of the thin shell crosses the tangent disks in the short window. -/
theorem shell_subset_tangent_difference {z θ : ℂ} (hθ : ‖θ‖ = 1) {l ρ δ : ℝ}
    (hl : 1 / 2 ≤ l) (hl3 : l ≤ 3) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1)
    (hδ : 0 < δ) (hδρ : δ ≤ ρ ^ 2 / 1600) :
    {y : ℂ | ρ ≤ ‖y - z‖ ∧ |‖y - (z + l • θ)‖ - l| ≤ 2 * δ} ⊆
      ({y : ℂ | ρ ≤ ‖y - z‖} ∩
        Metric.ball (z + (l + 200 * δ / ρ ^ 2) • θ) (l + 200 * δ / ρ ^ 2)) \
      ({y : ℂ | ρ ≤ ‖y - z‖} ∩
        Metric.ball (z + (l - 200 * δ / ρ ^ 2) • θ) (l - 200 * δ / ρ ^ 2)) := by
  let v : ℝ := 200 * δ / ρ ^ 2
  have hr2 : 0 < ρ ^ 2 := sq_pos_of_pos hρ
  have hvp : 0 < v := by dsimp [v]; positivity
  have hvs : v ≤ 1 / 8 := by
    dsimp [v]
    apply (div_le_iff₀ hr2).2
    linarith
  have hlm : 0 < l - v := by linarith
  have hlp : 0 < l + v := by linarith
  have h78 : 78 * δ / ρ ^ 2 < v := by
    dsimp [v]
    exact (div_lt_div_iff_of_pos_right hr2).2 (by linarith)
  rintro y ⟨hsep, hclose⟩
  obtain ⟨ha, hw⟩ := shell_entry_window hθ hl hl3 hρ hρ1 hδ hδρ hsep (by
    simpa only [dist_eq_norm] using hclose)
  have ha0 : 0 < ⟪y - z, θ⟫ := lt_of_lt_of_le (by positivity) ha
  have hentrylo : l - v < entryParameter z y θ := by linarith [(abs_le.mp hw).1]
  have hentryhi : entryParameter z y θ < l + v := by linarith [(abs_le.mp hw).2]
  refine ⟨⟨hsep, (mem_tangent_ball_iff_entry hθ hlp ha0).2 hentryhi⟩, ?_⟩
  rintro ⟨_, hm⟩
  have hm' := (mem_tangent_ball_iff_entry hθ hlm ha0).1 hm
  linarith

/-- The shell mass away from a cap is bounded by the one-dimensional tangent-mass jump. -/
theorem shell_mass_le_jump (S : Measure ℂ) [IsFiniteMeasure S]
    {x z : ℂ} {r ρ δ : ℝ} (hr : r ∈ Icc (1 : ℝ) 2) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1)
    (hδ : 0 < δ) (hδρ : δ ≤ ρ ^ 2 / 1600) (hz : z ∈ thinShell x r δ) :
    (S (thinShell x r δ \ Metric.ball z ρ)).toReal ≤
      tangentMass S ρ z (‖x - z‖⁻¹ • (x - z)) (‖x - z‖ + 200 * δ / ρ ^ 2) -
      tangentMass S ρ z (‖x - z‖⁻¹ • (x - z)) (‖x - z‖ - 200 * δ / ρ ^ 2) := by
  let l : ℝ := ‖x - z‖
  let θ : ℂ := l⁻¹ • (x - z)
  have hδquarter : δ ≤ 1 / 4 := by nlinarith
  obtain ⟨hl, hl3⟩ := shell_center_bounds hr hδquarter hz
  have hl0 : 0 < l := by dsimp [l]; linarith
  have hθ : ‖θ‖ = 1 := by
    dsimp only [θ]
    rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hl0.le)]
    exact inv_mul_cancel₀ hl0.ne'
  have hx : z + l • θ = x := by
    dsimp only [θ]
    rw [smul_smul, mul_inv_cancel₀ hl0.ne', one_smul]
    abel
  let A := {y : ℂ | ρ ≤ ‖y - z‖} ∩
      Metric.ball (z + (l - 200 * δ / ρ ^ 2) • θ) (l - 200 * δ / ρ ^ 2)
  let B := {y : ℂ | ρ ≤ ‖y - z‖} ∩
      Metric.ball (z + (l + 200 * δ / ρ ^ 2) • θ) (l + 200 * δ / ρ ^ 2)
  have hAm : MeasurableSet A := (measurableSet_le measurable_const (by fun_prop)).inter
    Metric.isOpen_ball.measurableSet
  have hsub : thinShell x r δ \ Metric.ball z ρ ⊆ B \ A := by
    apply subset_trans _ (shell_subset_tangent_difference hθ hl hl3 hρ hρ1 hδ hδρ)
    rintro y ⟨hy, hyz⟩
    exact ⟨le_of_not_gt (by simpa only [Metric.mem_ball, dist_eq_norm] using hyz),
      by rw [hx]; exact shell_pair_close hy hz⟩
  have hAB : A ⊆ B := by
    apply inter_subset_inter_right
    apply tangent_ball_mono hθ
    · have : 200 * δ / ρ ^ 2 ≤ 1 / 8 := by
        apply (div_le_iff₀ (sq_pos_of_pos hρ)).2
        linarith
      change 0 < l - 200 * δ / ρ ^ 2
      linarith
    · have : 0 ≤ 200 * δ / ρ ^ 2 := by positivity
      linarith
  have hmass := ENNReal.toReal_mono (measure_ne_top S (B \ A)) (measure_mono hsub)
  rw [measure_sdiff hAB hAm.nullMeasurableSet (measure_ne_top S A),
    ENNReal.toReal_sub_of_le (measure_mono hAB) (measure_ne_top S B)] at hmass
  exact hmass

/-- The earlier tangent-disk mass is controlled by the concentric interior mass. -/
theorem earlier_mass_le_interior (S : Measure ℂ) [IsFiniteMeasure S]
    {x z : ℂ} {r ρ δ : ℝ} (hr : r ∈ Icc (1 : ℝ) 2) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1)
    (hδ : 0 < δ) (hδρ : δ ≤ ρ ^ 2 / 1600) (hz : z ∈ thinShell x r δ) :
    tangentMass S ρ z (‖x - z‖⁻¹ • (x - z)) (‖x - z‖ - 200 * δ / ρ ^ 2) ≤
      (S (Metric.ball x (r - δ))).toReal := by
  let l : ℝ := ‖x - z‖
  let θ : ℂ := l⁻¹ • (x - z)
  have hδquarter : δ ≤ 1 / 4 := by nlinarith
  obtain ⟨hl, hl3⟩ := shell_center_bounds hr hδquarter hz
  have hl0 : 0 < l := by dsimp [l]; linarith
  have hθ : ‖θ‖ = 1 := by
    dsimp only [θ]
    rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hl0.le)]
    exact inv_mul_cancel₀ hl0.ne'
  have hx : z + l • θ = x := by
    dsimp only [θ]
    rw [smul_smul, mul_inv_cancel₀ hl0.ne', one_smul]
    abel
  apply ENNReal.toReal_mono (measure_ne_top S _)
  apply measure_mono
  apply (earlier_tangent_disk_subset hθ hl hl3 hρ hρ1 hδ hδρ).trans
  rw [hx]
  apply Metric.ball_subset_ball
  change |‖z - x‖ - r| ≤ δ at hz
  have hh := (abs_le.mp hz).2
  rw [norm_sub_rev z x] at hh
  change l - 2 * δ ≤ r - δ
  dsimp [l]
  linarith

end DiskGeometry

namespace DiskGeometry

/-- Area of a strip with continuously moving interval fibers. -/
theorem volume_interval_fibers (c : ℝ → ℝ) (hc : Continuous c)
    (lo hi w : ℝ) :
    volume {p : ℝ × ℝ | p.2 ∈ Icc lo hi ∧
      p.1 ∈ Icc (c p.2 - w) (c p.2 + w)} =
      ENNReal.ofReal (hi - lo) * ENNReal.ofReal (2 * w) := by
  have hs : MeasurableSet {p : ℝ × ℝ | p.2 ∈ Icc lo hi ∧
      p.1 ∈ Icc (c p.2 - w) (c p.2 + w)} := by
    exact (measurableSet_Icc.preimage continuous_snd.measurable).inter
      ((isClosed_le (hc.comp continuous_snd |>.sub continuous_const) continuous_fst).measurableSet.inter
        (isClosed_le continuous_fst (hc.comp continuous_snd |>.add continuous_const)).measurableSet)
  change (volume.prod volume) _ = _
  rw [Measure.prod_apply_symm hs]
  have hf (y : ℝ) :
      volume ((fun x : ℝ => (x, y)) ⁻¹' {p : ℝ × ℝ | p.2 ∈ Icc lo hi ∧
        p.1 ∈ Icc (c p.2 - w) (c p.2 + w)}) =
      (Icc lo hi).indicator (fun _ => ENNReal.ofReal (2 * w)) y := by
    by_cases hy : y ∈ Icc lo hi
    · simp only [preimage_ofPred_eq, hy, true_and, indicator_of_mem hy]
      change volume (Icc (c y - w) (c y + w)) = _
      rw [Real.volume_Icc]
      congr 1
      ring
    · simp only [preimage_ofPred_eq, hy, false_and, ofPred_false, measure_empty, indicator_of_notMem hy]
  simp_rw [hf]
  rw [lintegral_indicator measurableSet_Icc, lintegral_const, Measure.restrict_apply_univ,
    Real.volume_Icc, mul_comm]

/-- A nonvertical affine strip cut off in the second coordinate. -/
theorem volume_affine_strip {a : ℝ} (ha : a ≠ 0) (b c d R w : ℝ) :
    volume {p : ℝ × ℝ | |p.2 - d| ≤ R ∧ |a * p.1 + b * p.2 + c| ≤ w} =
      ENNReal.ofReal (2 * R) * ENNReal.ofReal (2 * (w / |a|)) := by
  have hs : {p : ℝ × ℝ | |p.2 - d| ≤ R ∧ |a * p.1 + b * p.2 + c| ≤ w} =
      {p : ℝ × ℝ | p.2 ∈ Icc (d - R) (d + R) ∧
        p.1 ∈ Icc (-(b * p.2 + c) / a - w / |a|)
          (-(b * p.2 + c) / a + w / |a|)} := by
    ext p
    simp only [mem_ofPred_eq, mem_Icc]
    have heq : a * p.1 + b * p.2 + c = a * (p.1 - -(b * p.2 + c) / a) := by
      field_simp
      ring
    rw [heq, abs_mul, ← le_div_iff₀' (abs_pos.mpr ha)]
    simp only [abs_le]
    constructor <;> rintro ⟨⟨h1, h2⟩, h3, h4⟩ <;> constructor <;> constructor <;> linarith
  rw [hs]
  rw [volume_interval_fibers (fun y => -(b * y + c) / a) (by fun_prop)]
  congr 2
  ring

/-- At least one coordinate sees half the Euclidean separation. -/
theorem complex_coordinate_separation {z : ℂ} {ρ : ℝ} (hz : ρ ≤ ‖z‖) :
    ρ / 2 ≤ |z.re| ∨ ρ / 2 ≤ |z.im| := by
  by_contra h
  push Not at h
  have hnorm : ‖z‖ ≤ |z.re| + |z.im| := Complex.norm_le_abs_re_add_abs_im z
  linarith

/-- The centers of two separated points lying on an almost common circle form
an affine strip of small area. No selected radius occurs here. -/
theorem volume_two_point_strip {y z : ℂ} {ρ δ : ℝ} (hρ : 0 < ρ) (hδ : 0 ≤ δ)
    (hyz : ρ ≤ ‖y - z‖) :
    volume {x : ℂ | ‖x - z‖ ≤ 3 ∧ |‖x - y‖ ^ 2 - ‖x - z‖ ^ 2| ≤ 13 * δ} ≤
      ENNReal.ofReal (156 * δ / ρ) := by
  let a : ℝ := 2 * (z.re - y.re)
  let b : ℝ := 2 * (z.im - y.im)
  let c : ℝ := ‖y‖ ^ 2 - ‖z‖ ^ 2
  have halg (x : ℂ) : ‖x - y‖ ^ 2 - ‖x - z‖ ^ 2 = a * x.re + b * x.im + c := by
    simp only [Complex.sq_norm, Complex.normSq_apply, Complex.sub_re, Complex.sub_im, a, b, c]
    ring
  have hsplit := complex_coordinate_separation hyz
  have hmain (a b c d : ℝ) (ha : ρ ≤ |a|) :
      volume {p : ℝ × ℝ | |p.2 - d| ≤ 3 ∧ |a * p.1 + b * p.2 + c| ≤ 13 * δ} ≤
        ENNReal.ofReal (156 * δ / ρ) := by
    have hap : 0 < |a| := hρ.trans_le ha
    rw [volume_affine_strip (abs_pos.mp hap)]
    rw [← ENNReal.ofReal_mul (by norm_num)]
    apply ENNReal.ofReal_le_ofReal
    calc
      (2 * 3) * (2 * (13 * δ / |a|)) = 156 * δ / |a| := by ring
      _ ≤ 156 * δ / ρ := div_le_div_of_nonneg_left (by positivity) hρ ha
  rcases hsplit with hre | him
  · have ha : ρ ≤ |a| := by
      dsimp [a]
      rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2), abs_sub_comm]
      simpa only [Complex.sub_re] using (show ρ ≤ 2 * |(y - z).re| by linarith)
    let s : Set (ℝ × ℝ) := {p | |p.2 - z.im| ≤ 3 ∧ |a * p.1 + b * p.2 + c| ≤ 13 * δ}
    have hsub : {x : ℂ | ‖x - z‖ ≤ 3 ∧ |‖x - y‖ ^ 2 - ‖x - z‖ ^ 2| ≤ 13 * δ} ⊆
        Complex.measurableEquivRealProd ⁻¹' s := by
      intro x hx
      exact ⟨(Complex.abs_im_le_norm (x - z)).trans hx.1, by simpa [halg x] using hx.2⟩
    have hs : MeasurableSet s := by
      exact (isClosed_le (show Continuous (fun p : ℝ × ℝ => |p.2 - z.im|) from by fun_prop)
        continuous_const).measurableSet.inter
        (isClosed_le (show Continuous (fun p : ℝ × ℝ => |a * p.1 + b * p.2 + c|) from by fun_prop)
        continuous_const).measurableSet
    calc
      _ ≤ volume (Complex.measurableEquivRealProd ⁻¹' s) := measure_mono hsub
      _ = volume s := Complex.volume_preserving_equiv_real_prod.measure_preimage hs.nullMeasurableSet
      _ ≤ _ := hmain a b c z.im ha
  · have hb : ρ ≤ |b| := by
      dsimp [b]
      rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2), abs_sub_comm]
      simpa only [Complex.sub_im] using (show ρ ≤ 2 * |(y - z).im| by linarith)
    let s : Set (ℝ × ℝ) := {p | |p.2 - z.re| ≤ 3 ∧ |b * p.1 + a * p.2 + c| ≤ 13 * δ}
    have hmp : MeasurePreserving (fun x : ℂ => (x.im, x.re)) :=
      Measure.measurePreserving_swap.comp Complex.volume_preserving_equiv_real_prod
    have hsub : {x : ℂ | ‖x - z‖ ≤ 3 ∧ |‖x - y‖ ^ 2 - ‖x - z‖ ^ 2| ≤ 13 * δ} ⊆
        (fun x : ℂ => (x.im, x.re)) ⁻¹' s := by
      intro x hx
      refine ⟨(Complex.abs_re_le_norm (x - z)).trans hx.1, ?_⟩
      simpa only [halg x, add_comm (a * x.re) (b * x.im)] using hx.2
    have hs : MeasurableSet s := by
      exact (isClosed_le (show Continuous (fun p : ℝ × ℝ => |p.2 - z.re|) from by fun_prop)
        continuous_const).measurableSet.inter
        (isClosed_le (show Continuous (fun p : ℝ × ℝ => |b * p.1 + a * p.2 + c|) from by fun_prop)
        continuous_const).measurableSet
    calc
      _ ≤ volume ((fun x : ℂ => (x.im, x.re)) ⁻¹' s) := measure_mono hsub
      _ = volume s := hmp.measure_preimage hs.nullMeasurableSet
      _ ≤ _ := hmain b a c z.re hb

end DiskGeometry

namespace DiskGeometry

def pairCondition (ρ δ : ℝ) (x z y : ℂ) : Prop :=
  1 / 2 ≤ ‖x - z‖ ∧ ‖x - z‖ ≤ 3 ∧
    |‖y - x‖ - ‖x - z‖| ≤ 2 * δ ∧ ρ ≤ ‖y - z‖

theorem measurableSet_pairCondition (ρ δ : ℝ) :
    MeasurableSet {p : (ℂ × ℂ) × ℂ | pairCondition ρ δ p.1.1 p.1.2 p.2} := by
  have hn : Measurable (fun p : (ℂ × ℂ) × ℂ => ‖p.1.1 - p.1.2‖) := by fun_prop
  have hc : Measurable (fun p : (ℂ × ℂ) × ℂ => |‖p.2 - p.1.1‖ - ‖p.1.1 - p.1.2‖|) := by fun_prop
  have hs : Measurable (fun p : (ℂ × ℂ) × ℂ => ‖p.2 - p.1.2‖) := by fun_prop
  exact (measurableSet_le measurable_const hn).inter
    ((measurableSet_le hn measurable_const).inter
      ((measurableSet_le hc measurable_const).inter (measurableSet_le measurable_const hs)))

theorem volume_pairCondition {ρ δ : ℝ} (hρ : 0 < ρ)
    (hδ : 0 ≤ δ) (hδquarter : δ ≤ 1 / 4) (z y : ℂ) :
    volume {x : ℂ | pairCondition ρ δ x z y} ≤ ENNReal.ofReal (156 * δ / ρ) := by
  by_cases hsep : ρ ≤ ‖y - z‖
  · apply le_trans (measure_mono (t := {x : ℂ | ‖x - z‖ ≤ 3 ∧
      |‖x - y‖ ^ 2 - ‖x - z‖ ^ 2| ≤ 13 * δ}) ?_)
      (volume_two_point_strip hρ hδ hsep)
    intro x hx
    obtain ⟨hl, hl3, hc, _⟩ := hx
    refine ⟨hl3, ?_⟩
    rw [norm_sub_rev x y]
    exact shell_square_error (norm_nonneg _) hl3 hδ hδquarter (norm_nonneg _) hc
  · have he : {x : ℂ | pairCondition ρ δ x z y} = ∅ := by
      ext x
      simp only [mem_ofPred_eq, mem_empty_iff_false, iff_false]
      exact fun h => hsep h.2.2.2
    rw [he, measure_empty]
    exact bot_le

def pairMass (ν : Measure ℂ) (ρ δ : ℝ) (x z : ℂ) : ℝ≥0∞ :=
  ν {y : ℂ | pairCondition ρ δ x z y}

theorem measurable_pairMass (ν : Measure ℂ) [IsFiniteMeasure ν] (ρ δ : ℝ) :
    Measurable (fun p : ℂ × ℂ => pairMass ν ρ δ p.1 p.2) :=
  measurable_measure_prodMk_left (measurableSet_pairCondition ρ δ)

def rayIndicator (S : Measure ℂ) (ρ T U v : ℝ) (x z : ℂ) : ℝ≥0∞ :=
  {p : ℂ × ℂ | rayCondition S ρ T U v p.1 p.2}.indicator 1 (x, z)

theorem measurable_rayIndicator (S : Measure ℂ) [IsFiniteMeasure S] (ρ T U v : ℝ) :
    Measurable (fun p : ℂ × ℂ => rayIndicator S ρ T U v p.1 p.2) :=
  measurable_const.indicator (measurableSet_rayCondition S ρ T U v)

/-- The first contribution to the Borel majorant is controlled by the two-point strip. -/
theorem lintegral_pairMass (ν : Measure ℂ) [IsFiniteMeasure ν] {ρ δ : ℝ}
    (hρ : 0 < ρ) (hδ : 0 ≤ δ) (hδquarter : δ ≤ 1 / 4) :
    (∫⁻ x : ℂ, ∫⁻ z : ℂ, pairMass ν ρ δ x z ∂ν) ≤
      ENNReal.ofReal (156 * δ / ρ) * ν univ * ν univ := by
  rw [lintegral_lintegral_swap (measurable_pairMass ν ρ δ).aemeasurable]
  apply le_trans (lintegral_mono (fun z => ?_))
    (by rw [lintegral_const])
  let A : Set (ℂ × ℂ) := {p | pairCondition ρ δ p.1 z p.2}
  have hA : MeasurableSet A := (measurableSet_pairCondition ρ δ).preimage
    (show Measurable (fun p : ℂ × ℂ => ((p.1, z), p.2)) by fun_prop)
  have he (x : ℂ) : pairMass ν ρ δ x z = ∫⁻ y : ℂ, A.indicator 1 (x, y) ∂ν := by
    rw [show (fun y : ℂ => A.indicator 1 (x, y)) =
      {y : ℂ | pairCondition ρ δ x z y}.indicator 1 by
        ext y; exact (indicator_comp_right (fun y : ℂ => (x, y))).symm]
    exact (lintegral_indicator_one ((measurableSet_pairCondition ρ δ).preimage
      (show Measurable (fun y : ℂ => ((x, z), y)) by fun_prop))).symm
  simp_rw [he]
  rw [lintegral_lintegral_swap (f := fun x y : ℂ => A.indicator 1 (x, y))
    (measurable_const.indicator hA).aemeasurable]
  calc
    _ ≤ ∫⁻ y : ℂ, ENNReal.ofReal (156 * δ / ρ) ∂ν := by
      apply lintegral_mono
      intro y
      have hei : (fun x : ℂ => A.indicator (1 : ℂ × ℂ → ℝ≥0∞) (x, y)) =
          {x : ℂ | pairCondition ρ δ x z y}.indicator 1 := by
        ext x
        exact (indicator_comp_right (fun x : ℂ => (x, y))).symm
      dsimp only
      rw [hei]
      have hsm : MeasurableSet {x : ℂ | pairCondition ρ δ x z y} :=
        (measurableSet_pairCondition ρ δ).preimage
          (show Measurable (fun x : ℂ => ((x, z), y)) by fun_prop)
      exact (lintegral_indicator_one hsm).le.trans (volume_pairCondition hρ hδ hδquarter z y)
    _ = _ := lintegral_const _

/-- The second contribution is controlled by monotone ray jumps and polar coordinates. -/
theorem lintegral_rayIndicator (ν S : Measure ℂ) [IsFiniteMeasure ν] [IsFiniteMeasure S]
    (ρ : ℝ) {T U v : ℝ} (hT : 0 ≤ T) (hU : 0 < U) (hv : 0 ≤ v) :
    (∫⁻ x : ℂ, ∫⁻ z : ℂ, rayIndicator S ρ T U v x z ∂ν) ≤
      (ENNReal.ofReal (6 * Real.pi) * ENNReal.ofReal (2 * v * (1 + T / U))) * ν univ := by
  rw [lintegral_lintegral_swap (measurable_rayIndicator S ρ T U v).aemeasurable]
  calc
    _ ≤ ∫⁻ _z : ℂ,
        ENNReal.ofReal (6 * Real.pi) * ENNReal.ofReal (2 * v * (1 + T / U)) ∂ν := by
      apply lintegral_mono
      intro z
      have he : (fun x : ℂ => rayIndicator S ρ T U v x z) =
          {x : ℂ | rayCondition S ρ T U v x z}.indicator 1 := by
        ext x
        exact (indicator_comp_right (fun x : ℂ => (x, z))).symm
      dsimp only
      rw [he]
      have hsm : MeasurableSet {x : ℂ | rayCondition S ρ T U v x z} :=
        (measurableSet_rayCondition S ρ T U v).preimage
          (show Measurable (fun x : ℂ => (x, z)) by fun_prop)
      exact (lintegral_indicator_one hsm).le.trans (volume_rayCondition S ρ hT hU hv z)
    _ = _ := lintegral_const _

end DiskGeometry

namespace DiskGeometry

/-- Failure of every cap forces the majorant bracket to be at least one. -/
theorem bad_cap_bracket (S ν : Measure ℂ) [IsFiniteMeasure S] [IsFiniteMeasure ν]
    {x z : ℂ} {r ρ δ T U : ℝ} (hr : r ∈ Icc (1 : ℝ) 2)
    (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (hδ : 0 < δ) (hδρ : δ ≤ ρ ^ 2 / 1600)
    (hT : 0 ≤ T) (hU : 0 < U) (hz : z ∈ thinShell x r δ)
    (hi : S (Metric.ball x (r - δ)) ≤ ENNReal.ofReal T)
    (hb : ENNReal.ofReal (2 * U) < (S + ν) (thinShell x r δ \ Metric.ball z ρ)) :
    1 ≤ (ENNReal.ofReal U)⁻¹ * pairMass ν ρ δ x z +
      rayIndicator S ρ T U (200 * δ / ρ ^ 2) x z := by
  have hδquarter : δ ≤ 1 / 4 := by nlinarith
  obtain ⟨hl, hl3⟩ := shell_center_bounds hr hδquarter hz
  have hcases : ENNReal.ofReal U ≤ ν (thinShell x r δ \ Metric.ball z ρ) ∨
      ENNReal.ofReal U ≤ S (thinShell x r δ \ Metric.ball z ρ) := by
    by_contra h
    push Not at h
    have he2 : ENNReal.ofReal (2 * U) = ENNReal.ofReal U + ENNReal.ofReal U := by
      rw [two_mul, ENNReal.ofReal_add hU.le hU.le]
    have hm : (S + ν) (thinShell x r δ \ Metric.ball z ρ) ≤ ENNReal.ofReal (2 * U) := by
      rw [Measure.add_apply, he2]
      exact add_le_add h.2.le h.1.le
    exact (not_le_of_gt hb) hm
  rcases hcases with hν | hS
  · have hp : ENNReal.ofReal U ≤ pairMass ν ρ δ x z := by
      apply hν.trans (measure_mono ?_)
      rintro y ⟨hy, hsep⟩
      exact ⟨hl, hl3, shell_pair_close hy hz,
        le_of_not_gt (by simpa only [Metric.mem_ball, dist_eq_norm] using hsep)⟩
    calc
      1 = (ENNReal.ofReal U)⁻¹ * ENNReal.ofReal U :=
        (ENNReal.inv_mul_cancel (ENNReal.ofReal_pos.mpr hU).ne' ENNReal.ofReal_ne_top).symm
      _ ≤ (ENNReal.ofReal U)⁻¹ * pairMass ν ρ δ x z := mul_le_mul_right hp _
      _ ≤ _ := le_self_add
  · have hi' : (S (Metric.ball x (r - δ))).toReal ≤ T := by
      have := ENNReal.toReal_mono ENNReal.ofReal_ne_top hi
      simpa only [ENNReal.toReal_ofReal hT] using this
    have hS' : U ≤ (S (thinShell x r δ \ Metric.ball z ρ)).toReal :=
      (ENNReal.ofReal_le_iff_le_toReal (measure_ne_top S _)).1 hS
    have hc : rayCondition S ρ T U (200 * δ / ρ ^ 2) x z :=
      ⟨hl, hl3, (earlier_mass_le_interior S hr hρ hρ1 hδ hδρ hz).trans hi',
        hS'.trans (shell_mass_le_jump S hr hρ hρ1 hδ hδρ hz)⟩
    have hone : rayIndicator S ρ T U (200 * δ / ρ ^ 2) x z = 1 :=
      indicator_of_mem hc 1
    rw [hone]
    exact le_add_self

/-- A radius-independent Borel majorant combining separated shell pairs and ray jumps. -/
def shellMajorant (ν S : Measure ℂ) (ρ δ T U : ℝ) (x : ℂ) : ℝ≥0∞ :=
  (ENNReal.ofReal U)⁻¹ ^ 2 * (∫⁻ z, pairMass ν ρ δ x z ∂ν) +
    (ENNReal.ofReal U)⁻¹ * (∫⁻ z, rayIndicator S ρ T U (200 * δ / ρ ^ 2) x z ∂ν)

theorem measurable_shellMajorant (ν S : Measure ℂ) [IsFiniteMeasure ν] [IsFiniteMeasure S]
    (ρ δ T U : ℝ) : Measurable (shellMajorant ν S ρ δ T U) := by
  exact ((measurable_pairMass ν ρ δ).lintegral_prod_right.const_mul _).add
    ((measurable_rayIndicator S ρ T U (200 * δ / ρ ^ 2)).lintegral_prod_right.const_mul _)

theorem shellMajorant_eq_bracket (ν S : Measure ℂ) [IsFiniteMeasure ν] [IsFiniteMeasure S]
    (ρ δ T U : ℝ) (x : ℂ) :
    shellMajorant ν S ρ δ T U x = (ENNReal.ofReal U)⁻¹ * ∫⁻ z,
      ((ENNReal.ofReal U)⁻¹ * pairMass ν ρ δ x z +
        rayIndicator S ρ T U (200 * δ / ρ ^ 2) x z) ∂ν := by
  have hp : Measurable (fun z : ℂ => pairMass ν ρ δ x z) :=
    (measurable_pairMass ν ρ δ).comp (measurable_const.prodMk measurable_id)
  rw [lintegral_add_left (hp.const_mul _), lintegral_const_mul _ hp]
  unfold shellMajorant
  ring

/-- The majorant is integrable uniformly over all radii. -/
theorem lintegral_shellMajorant (ν S : Measure ℂ) [IsFiniteMeasure ν] [IsFiniteMeasure S]
    {ρ δ T U : ℝ} (hρ : 0 < ρ) (hδ : 0 ≤ δ) (hδquarter : δ ≤ 1 / 4)
    (hT : 0 ≤ T) (hU : 0 < U) :
    (∫⁻ x, shellMajorant ν S ρ δ T U x) ≤
      (ENNReal.ofReal U)⁻¹ ^ 2 * (ENNReal.ofReal (156 * δ / ρ) * ν univ * ν univ) +
      (ENNReal.ofReal U)⁻¹ * ((ENNReal.ofReal (6 * Real.pi) *
        ENNReal.ofReal (2 * (200 * δ / ρ ^ 2) * (1 + T / U))) * ν univ) := by
  have hp : Measurable (fun x : ℂ => ∫⁻ z, pairMass ν ρ δ x z ∂ν) :=
    (measurable_pairMass ν ρ δ).lintegral_prod_right
  have hr : Measurable (fun x : ℂ => ∫⁻ z, rayIndicator S ρ T U (200 * δ / ρ ^ 2) x z ∂ν) :=
    (measurable_rayIndicator S ρ T U (200 * δ / ρ ^ 2)).lintegral_prod_right
  simp only [shellMajorant]
  rw [lintegral_add_left (hp.const_mul _), lintegral_const_mul _ hp, lintegral_const_mul _ hr]
  exact add_le_add
    (mul_le_mul_right (lintegral_pairMass ν hρ hδ hδquarter) _)
    (mul_le_mul_right (lintegral_rayIndicator ν S ρ hT hU (by positivity)) _)

/-- The majorant detects simultaneous failure of concentration at every cap. -/
theorem one_le_majorant_of_no_cap (ν S : Measure ℂ) [IsFiniteMeasure ν] [IsFiniteMeasure S]
    {ρ δ T U : ℝ} (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (hδ : 0 < δ)
    (hδρ : δ ≤ ρ ^ 2 / 1600) (hT : 0 ≤ T) (hU : 0 < U)
    {x : ℂ} {r : ℝ} (hr : r ∈ Icc (1 : ℝ) 2)
    (hν : ENNReal.ofReal U ≤ ν (thinShell x r δ))
    (hS : S (Metric.ball x (r - δ)) ≤ ENNReal.ofReal T)
    (hbad : ∀ z ∈ thinShell x r δ,
      ENNReal.ofReal (2 * U) < (S + ν) (thinShell x r δ \ Metric.ball z ρ)) :
    1 ≤ shellMajorant ν S ρ δ T U x := by
  have hu0 : ENNReal.ofReal U ≠ 0 := (ENNReal.ofReal_pos.mpr hU).ne'
  rw [shellMajorant_eq_bracket]
  calc
    1 = (ENNReal.ofReal U)⁻¹ * ENNReal.ofReal U :=
      (ENNReal.inv_mul_cancel hu0 ENNReal.ofReal_ne_top).symm
    _ ≤ (ENNReal.ofReal U)⁻¹ * ν (thinShell x r δ) := mul_le_mul_right hν _
    _ = (ENNReal.ofReal U)⁻¹ * (∫⁻ z, (thinShell x r δ).indicator 1 z ∂ν) := by
      rw [lintegral_indicator_one (measurableSet_thinShell x r δ)]
    _ ≤ _ := by
      apply mul_le_mul_right
      apply lintegral_mono
      intro z
      by_cases hz : z ∈ thinShell x r δ
      · rw [indicator_of_mem hz]
        exact bad_cap_bracket S ν hr hρ hρ1 hδ hδρ hT hU hz hS (hbad z hz)
      · rw [indicator_of_notMem hz]
        exact bot_le

/-- Full radius-independent shell concentration, with explicit absolute constants. -/
theorem shell_concentration (ν S : Measure ℂ) [IsFiniteMeasure ν] [IsFiniteMeasure S]
    {ρ δ T U : ℝ} (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (hδ : 0 < δ)
    (hδρ : δ ≤ ρ ^ 2 / 1600) (hT : 0 ≤ T) (hU : 0 < U) :
    ∃ E : Set ℂ, MeasurableSet E ∧
      volume E ≤
        (ENNReal.ofReal U)⁻¹ ^ 2 * (ENNReal.ofReal (156 * δ / ρ) * ν univ * ν univ) +
        (ENNReal.ofReal U)⁻¹ * ((ENNReal.ofReal (6 * Real.pi) *
          ENNReal.ofReal (2 * (200 * δ / ρ ^ 2) * (1 + T / U))) * ν univ) ∧
      ∀ x ∉ E, ∀ r ∈ Icc (1 : ℝ) 2,
        ENNReal.ofReal U ≤ ν (thinShell x r δ) →
        S (Metric.ball x (r - δ)) ≤ ENNReal.ofReal T →
        ∃ z ∈ thinShell x r δ,
          (S + ν) (thinShell x r δ \ Metric.ball z ρ) ≤ ENNReal.ofReal (2 * U) := by
  let E : Set ℂ := {x | 1 ≤ shellMajorant ν S ρ δ T U x}
  have hE : MeasurableSet E := measurableSet_le measurable_const
    (measurable_shellMajorant ν S ρ δ T U)
  refine ⟨E, hE, ?_, ?_⟩
  · have hm := meas_ge_le_lintegral_div (μ := (volume : Measure ℂ))
      (measurable_shellMajorant ν S ρ δ T U).aemeasurable one_ne_zero ENNReal.one_ne_top
    simp only [div_one] at hm
    refine hm.trans (lintegral_shellMajorant ν S hρ hδ.le ?_ hT hU)
    have hρsq : ρ ^ 2 ≤ 1 := by nlinarith
    linarith
  · intro x hx r hr hν hS
    by_contra h
    push Not at h
    exact hx (one_le_majorant_of_no_cap ν S hρ hρ1 hδ hδρ hT hU hr hν hS h)

end DiskGeometry

open MeasureTheory Set Filter
open scoped Topology RealInnerProductSpace ContDiff

noncomputable section

end
end

end OAI
