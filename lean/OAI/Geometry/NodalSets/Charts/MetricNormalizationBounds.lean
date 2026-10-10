import OAI.Geometry.NodalSets.Charts.MetricCoercivity
import OAI.Geometry.NodalSets.Charts.MetricFrameOps

namespace OAI

namespace Yau.Geometry
open Yau.Jets
noncomputable section

lemma bilinear_diagonal_change_bound
    (g h : Coord →L[ℝ] Coord →L[ℝ] ℝ) (v w : Coord)
    {M K δ η : ℝ} (hM : 0 ≤ M) (hK : 0 ≤ K)
    (hg : ‖g‖ ≤ M) (hv : ‖v‖ ≤ K) (hw : ‖w‖ ≤ K)
    (hvw : ‖v-w‖ ≤ δ) (hgh : ‖g-h‖ ≤ η) :
    |g v v-h w w| ≤ 2*M*K*δ+η*K^2 := by
  have hδ : 0 ≤ δ := (norm_nonneg _).trans hvw
  have hη : 0 ≤ η := (norm_nonneg (g-h)).trans hgh
  have h1 : |g (v-w) v| ≤ M*δ*K := (bilinear_pairing_bound g _ _).trans (by gcongr)
  have h2 : |g w (v-w)| ≤ M*K*δ := (bilinear_pairing_bound g _ _).trans (by gcongr)
  have h3 : |(g-h) w w| ≤ η*K*K := (bilinear_pairing_bound _ _ _).trans (by gcongr)
  have hid : g v v-h w w = g (v-w) v+g w (v-w)+(g-h) w w := by
    simp only [map_sub,sub_apply]
    ring
  rw [hid]
  calc
    _ ≤ (|g (v-w) v|+|g w (v-w)|)+|(g-h) w w| := (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
    _ ≤ (M*δ*K+M*K*δ)+η*K*K := add_le_add (add_le_add h1 h2) h3
    _ = _ := by ring

lemma inverse_sqrt_difference_bound {a b m E : ℝ} (hm : 0 < m)
    (ha : m^2 ≤ a) (hb : m^2 ≤ b) (hab : |a-b| ≤ E) :
    |(Real.sqrt a)⁻¹-(Real.sqrt b)⁻¹| ≤ E/m^3 := by
  have ha0 : 0 < a := (sq_pos_of_pos hm).trans_le ha
  have hb0 : 0 < b := (sq_pos_of_pos hm).trans_le hb
  have hu : 0 < Real.sqrt a := Real.sqrt_pos.mpr ha0
  have hv : 0 < Real.sqrt b := Real.sqrt_pos.mpr hb0
  have hmu : m ≤ Real.sqrt a := (Real.le_sqrt hm.le ha0.le).mpr ha
  have hmv : m ≤ Real.sqrt b := (Real.le_sqrt hm.le hb0.le).mpr hb
  have hden : m^3 ≤ Real.sqrt a*Real.sqrt b*(Real.sqrt a+Real.sqrt b) := by
    calc
      m^3 = m*m*m := by ring
      _ ≤ Real.sqrt a*Real.sqrt b*(Real.sqrt a+Real.sqrt b) :=
        mul_le_mul (mul_le_mul hmu hmv hm.le hu.le) (by linarith) hm.le (mul_nonneg hu.le hv.le)
  have hid : (Real.sqrt a)⁻¹-(Real.sqrt b)⁻¹ =
      (b-a)/(Real.sqrt a*Real.sqrt b*(Real.sqrt a+Real.sqrt b)) := by
    have h1 := Real.sq_sqrt ha0.le
    have h2 := Real.sq_sqrt hb0.le
    field_simp
    nlinarith only [h1,h2]
  rw [hid,abs_div,abs_of_pos (by positivity : 0 < Real.sqrt a*Real.sqrt b*(Real.sqrt a+Real.sqrt b)),abs_sub_comm]
  exact div_le_div₀ ((abs_nonneg _).trans hab) hab (by positivity) hden

lemma metricNormalize_difference_bound
    (g h : Coord →L[ℝ] Coord →L[ℝ] ℝ) (v w : Coord)
    {M K m δ η : ℝ} (hM : 0 ≤ M) (hK : 0 ≤ K) (hm : 0 < m)
    (hg : ‖g‖ ≤ M) (hv : ‖v‖ ≤ K) (hw : ‖w‖ ≤ K)
    (hvw : ‖v-w‖ ≤ δ) (hgh : ‖g-h‖ ≤ η)
    (hlenv : m^2 ≤ g v v) (hlenw : m^2 ≤ h w w) :
    ‖metricNormalize g v-metricNormalize h w‖ ≤
      δ/m+K*(2*M*K*δ+η*K^2)/m^3 := by
  have ha0 : 0 < g v v := (sq_pos_of_pos hm).trans_le hlenv
  have ha := Real.sqrt_pos.mpr ha0
  have hma : m ≤ Real.sqrt (g v v) := (Real.le_sqrt hm.le ha0.le).mpr hlenv
  have hinv : (Real.sqrt (g v v))⁻¹ ≤ m⁻¹ := inv_anti₀ hm hma
  have hdiag := bilinear_diagonal_change_bound g h v w hM hK hg hv hw hvw hgh
  have hdiff := inverse_sqrt_difference_bound hm hlenv hlenw hdiag
  have hE : 0 ≤ 2*M*K*δ+η*K^2 := (abs_nonneg _).trans hdiag
  have hid : metricNormalize g v-metricNormalize h w =
      (Real.sqrt (g v v))⁻¹ • (v-w)+
      ((Real.sqrt (g v v))⁻¹-(Real.sqrt (h w w))⁻¹) • w := by
    unfold metricNormalize
    module
  rw [hid]
  calc
    _ ≤ ‖(Real.sqrt (g v v))⁻¹ • (v-w)‖+
        ‖((Real.sqrt (g v v))⁻¹-(Real.sqrt (h w w))⁻¹) • w‖ := norm_add_le _ _
    _ ≤ m⁻¹*δ+((2*M*K*δ+η*K^2)/m^3)*K := by
      simp only [norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr ha)]
      exact add_le_add (mul_le_mul hinv hvw (norm_nonneg _) (by positivity))
        (mul_le_mul hdiff hw (norm_nonneg _) (by positivity))
    _ = _ := by ring

end
end Yau.Geometry

end OAI
