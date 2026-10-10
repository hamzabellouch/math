import OAI.Probability.SLE.Loewner.SlitChartExteriorComparison

namespace OAI

/-! A uniform far-field displacement bound for all slits in one fixed disk. -/
noncomputable section
open Set Filter Function Complex Metric
open scoped Topology

namespace SLEExactGauge

lemma radiusHullMap_im_mul_normSq {R : ℝ} (hR : 0<R) {z : ℂ} (hz : z≠0) :
    (radiusHullMap R z).im*normSq z=z.im*(normSq z-R^2) := by
  rw [radiusHullMap_formula hR]
  simp only [add_im,div_im,← ofReal_pow,ofReal_re,ofReal_im,zero_mul]
  have hn : normSq z≠0 := (normSq_pos.mpr hz).ne'
  field_simp [hn]
  ring

lemma radiusHullMap_im_ge_half {R : ℝ} (hR : 0<R) {z : ℂ} (hz : 2*R≤z.im) :
    z.im/2≤(radiusHullMap R z).im := by
  have hy : 0<z.im := (mul_pos (by norm_num : (0:ℝ)<2) hR).trans_le hz
  have hz0 : z≠0 := by intro he; simp [he] at hy
  have hn : 0<normSq z := normSq_pos.mpr hz0
  have hs : 2*R^2≤normSq z := by
    rw [normSq_apply]
    nlinarith [sq_nonneg z.re]
  have hm := mul_le_mul_of_nonneg_left hs hy.le
  have he := radiusHullMap_im_mul_normSq hR hz0
  exact (mul_le_mul_iff_left₀ hn).mp (by nlinarith)

lemma SimpleSlitChart.far_height_displacement {p : C(unitInterval,ℂ)} (P : SimpleSlitChart p)
    {R : ℝ} (hR : 0<R) (hp : ∀ u : unitInterval, ‖p u‖≤R)
    {z : ℂ} (hz : 2*R≤z.im) : ‖P.forward z-z‖≤3*R^2/z.im := by
  have hy : 0<z.im := (mul_pos (by norm_num : (0:ℝ)<2) hR).trans_le hz
  have hyn : z.im≤‖z‖ := Complex.im_le_norm z
  have hn : 0<‖z‖ := hy.trans_le hyn
  have hzE : z∈exteriorUpperRadius R := ⟨by linarith,hy⟩
  have hh := P.exterior_comparison hR hp hzE
  have hlower := radiusHullMap_im_ge_half hR hz
  have hhpos : 0<(radiusHullMap R z).im := (half_pos hy).trans_le hlower
  have hdiff : ‖radiusHullMap R z-z‖=R^2/‖z‖ := by
    rw [radiusHullMap_formula hR,add_sub_cancel_left,norm_div,norm_pow,
      Complex.norm_real,Real.norm_eq_abs,abs_of_pos hR]
  have htri := dist_triangle (P.forward z) (radiusHullMap R z) z
  simp only [dist_eq_norm] at htri
  calc
    ‖P.forward z-z‖ ≤ ‖P.forward z-radiusHullMap R z‖+‖radiusHullMap R z-z‖ := htri
    _ ≤ (R^2-P.capacity)/(radiusHullMap R z).im+R^2/‖z‖ := by
      rw [hdiff]
      exact add_le_add hh.2 le_rfl
    _ ≤ R^2/(z.im/2)+R^2/z.im := by
      apply add_le_add
      · exact (div_le_div_of_nonneg_right (sub_le_self _ P.capacity_pos.le) hhpos.le).trans
          (div_le_div_of_nonneg_left (sq_nonneg R) (half_pos hy) hlower)
      · exact div_le_div_of_nonneg_left (sq_nonneg R) hy hyn
    _ = 3*R^2/z.im := by field_simp; ring

end SLEExactGauge

end

end OAI
