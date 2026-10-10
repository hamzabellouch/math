import OAI.Geometry.NodalSets.Charts.MetricNormalizationBounds

namespace OAI

noncomputable section

namespace Yau.Geometry

open Yau.Jets

theorem metric_normalization_uniform_stability {M K : ℝ} (hM : 0 ≤ M) (hK : 0 ≤ K) :
    ∃ ε₀ C : ℝ, 0 < ε₀ ∧ 0 < C ∧
      ∀ (g h : Coord →L[ℝ] Coord →L[ℝ] ℝ) (v w : Coord) (ε : ℝ),
      ‖g‖ ≤ M → ‖w‖ ≤ K → 1 ≤ h w w →
      ‖v-w‖ ≤ ε → ‖g-h‖ ≤ ε → ε ≤ ε₀ →
      1/2 ≤ g v v ∧ v ≠ 0 ∧
        ‖metricNormalize g v-metricNormalize h w‖ ≤ C*ε := by
  let H : ℝ := 2*M*(K+1)+(K+1)^2
  have hH : 0 ≤ H := by dsimp [H]; positivity
  let ε₀ : ℝ := min 1 (1/(2*(H+1)))
  let C : ℝ := 2+8*(K+1)*H
  have hε₀ : 0 < ε₀ := lt_min zero_lt_one (by positivity)
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨ε₀,C,hε₀,hC,?_⟩
  intro g h v w ε hg hw hlen hd hm hε
  have hε0 : 0 ≤ ε := (norm_nonneg _).trans hd
  have hε1 : ε ≤ 1 := hε.trans (min_le_left _ _)
  have hε2 : ε ≤ 1/(2*(H+1)) := hε.trans (min_le_right _ _)
  have hsmall : H*ε ≤ 1/2 := by
    have hh := (le_div_iff₀ (by positivity : 0 < 2*(H+1))).mp hε2
    nlinarith
  have hv : ‖v‖ ≤ K+1 := by
    calc
      ‖v‖ ≤ ‖v-w‖+‖w‖ := norm_le_norm_sub_add _ _
      _ ≤ ε+K := add_le_add hd hw
      _ ≤ K+1 := by linarith
  have hw' : ‖w‖ ≤ K+1 := hw.trans (by linarith)
  have hb := bilinear_diagonal_change_bound g h v w hM (by linarith : 0 ≤ K+1) hg hv hw' hd hm
  have hdiag : |g v v-h w w| ≤ H*ε := hb.trans_eq (by dsimp [H]; ring)
  have hpos : 1/2 ≤ g v v := by
    have hh := (abs_le.mp hdiag).1
    linarith
  have hn : v ≠ 0 := by
    intro hz
    simp only [hz,map_zero] at hpos
    norm_num at hpos
  refine ⟨hpos,hn,?_⟩
  have hnorm := metricNormalize_difference_bound g h v w hM (by linarith : 0 ≤ K+1)
    (by norm_num : (0:ℝ) < 1/2) hg hv hw' hd hm (by linarith) (by linarith)
  apply hnorm.trans_eq
  dsimp [C,H]
  ring

lemma sqrt_difference_bound_of_reference {a b m E : ℝ}
    (ha : 0 ≤ a) (hm : 0 < m) (hb : m^2 ≤ b) (hab : |a-b| ≤ E) :
    |Real.sqrt a-Real.sqrt b| ≤ E/m := by
  have hb0 : 0 ≤ b := (sq_nonneg m).trans hb
  have hmb : m ≤ Real.sqrt b := (Real.le_sqrt hm.le hb0).mpr hb
  have hsum : m ≤ Real.sqrt a+Real.sqrt b := by linarith [Real.sqrt_nonneg a]
  have hid : (Real.sqrt a-Real.sqrt b)*(Real.sqrt a+Real.sqrt b) = a-b := by
    nlinarith [Real.sq_sqrt ha,Real.sq_sqrt hb0]
  have hh : |Real.sqrt a-Real.sqrt b| *(Real.sqrt a+Real.sqrt b) ≤ E := by
    simpa only [abs_mul,abs_of_nonneg (by positivity : 0 ≤ Real.sqrt a+Real.sqrt b)] using
      (show |(Real.sqrt a-Real.sqrt b)*(Real.sqrt a+Real.sqrt b)| ≤ E by rw [hid]; exact hab)
  apply (le_div_iff₀ hm).mpr
  exact (mul_le_mul_of_nonneg_left hsum (abs_nonneg _)).trans hh

lemma metric_speed_smul (g : Coord →L[ℝ] Coord →L[ℝ] ℝ) (v : Coord)
    {s : ℝ} (hs : 0 ≤ s) :
    Real.sqrt (g (s • v) (s • v)) = s*Real.sqrt (g v v) := by
  simp only [map_smul,smul_apply,smul_eq_mul]
  rw [show s*(s*g v v) = s^2*(g v v) by ring,
    Real.sqrt_mul (sq_nonneg s),Real.sqrt_sq_eq_abs,abs_of_nonneg hs]

lemma metric_speed_uniform_stability {M K : ℝ} (hM : 0 ≤ M) (hK : 0 ≤ K)
    (g h : Coord →L[ℝ] Coord →L[ℝ] ℝ) (v w : Coord) {ε : ℝ}
    (hg : ‖g‖ ≤ M) (hw : ‖w‖ ≤ K) (hp : 0 ≤ g v v) (hlen : 1 ≤ h w w)
    (hd : ‖v-w‖ ≤ ε) (hm : ‖g-h‖ ≤ ε) (hε : ε ≤ 1) :
    |Real.sqrt (g v v)-Real.sqrt (h w w)| ≤ (2*M*(K+1)+(K+1)^2)*ε := by
  have hv : ‖v‖ ≤ K+1 := (norm_le_norm_sub_add v w).trans
    ((add_le_add hd hw).trans (by linarith))
  have hb := bilinear_diagonal_change_bound g h v w hM (by linarith : 0 ≤ K+1)
    hg hv (hw.trans (by linarith)) hd hm
  have hh := sqrt_difference_bound_of_reference hp (by norm_num : (0:ℝ)<1)
    (by simpa using hlen) hb
  calc
    _ ≤ (2*M*(K+1)*ε+ε*(K+1)^2)/1 := hh
    _ = _ := by ring

end Yau.Geometry

end

end OAI
