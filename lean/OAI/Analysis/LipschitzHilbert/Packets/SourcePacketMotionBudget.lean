import OAI.Analysis.LipschitzHilbert.Phase.SourcePredictablePacketMotion

namespace OAI

/-! The explicit packet-motion coefficient at the angular averaging scale.
All three spatial ratios are bounded before applying polynomial absorption. -/

noncomputable section
namespace LipschitzHilbert.AngularGrid

theorem source_packet_displacement_ratios (g : AngularGrid) (T : SlopeBox)
    {w B : ℝ} (hw : 0 < w) (hB : 1 ≤ B) (hwidth : B^2*w ≤ T.width)
    (h start : ℕ) (sR b : ℝ)
    (hs : g.index h sR = g.index h T.slope)
    (hblock : g.width h ≤ B*g.width start)
    (he : g.eligible (g.rootWidth/B^2) (w/T.length) start)
    (hb : |b| ≤ w/(g.width start*Real.sqrt (g.branching:ℝ))) :
    let r := B^2*w/g.width start
    |b|/r ≤ 1/Real.sqrt (g.branching:ℝ) ∧
    |b|/T.length ≤ 1/Real.sqrt (g.branching:ℝ) ∧
    |(sR-T.slope)*b|/T.width ≤ 1/Real.sqrt (g.branching:ℝ) ∧
    |b| ≤ T.length ∧ |(sR-T.slope)*b| ≤ T.width := by
  dsimp only
  have hB0 : 0 < B := zero_lt_one.trans_le hB
  have hG : (1:ℝ) ≤ g.branching := by
    exact_mod_cast (show 1 ≤ g.branching by have := g.branching_ge_two; omega)
  have hsqrt : 0 < Real.sqrt (g.branching:ℝ) :=
    Real.sqrt_pos.mpr (zero_lt_one.trans_le hG)
  have hsqrt1 : 1 ≤ Real.sqrt (g.branching:ℝ) := by
    simpa only [Real.sqrt_one] using Real.sqrt_le_sqrt hG
  have hc := g.width_pos start
  have hBsq : 1 ≤ B^2 := by nlinarith
  have hBsqw : 0 < B^2*w := mul_pos (sq_pos_of_pos hB0) hw
  have hr : 0 < B^2*w/g.width start := div_pos hBsqw hc
  have hlen := g.source_eligible_length_lower hw hB0 T.length_pos start he
  have hsmall : 1/Real.sqrt (g.branching:ℝ) ≤ 1 :=
    (div_le_one hsqrt).mpr hsqrt1
  have hratio : |b|/(B^2*w/g.width start) ≤ 1/Real.sqrt (g.branching:ℝ) := by
    calc
      _ ≤ (w/(g.width start*Real.sqrt (g.branching:ℝ)))/(B^2*w/g.width start) :=
        div_le_div_of_nonneg_right hb hr.le
      _ = (1/B^2)/Real.sqrt (g.branching:ℝ) := by
        field_simp [hw.ne',hc.ne',hB0.ne',hsqrt.ne']
      _ ≤ 1/Real.sqrt (g.branching:ℝ) :=
        div_le_div_of_nonneg_right ((div_le_one (sq_pos_of_pos hB0)).mpr hBsq) hsqrt.le
  have hlenratio : |b|/T.length ≤ 1/Real.sqrt (g.branching:ℝ) :=
    (div_le_div_of_nonneg_left (abs_nonneg b) hr hlen).trans hratio
  have hslope : |sR-T.slope| ≤ B*g.width start :=
    (g.same_cell_diameter h hs).trans hblock
  have htrans : |(sR-T.slope)*b|/T.width ≤ 1/Real.sqrt (g.branching:ℝ) := by
    rw [abs_mul]
    calc
      _ ≤ ((B*g.width start)*(w/(g.width start*Real.sqrt (g.branching:ℝ))))/T.width :=
        div_le_div_of_nonneg_right
          (mul_le_mul hslope hb (abs_nonneg b) (mul_nonneg hB0.le hc.le)) T.width_pos.le
      _ ≤ ((B*g.width start)*(w/(g.width start*Real.sqrt (g.branching:ℝ))))/(B^2*w) :=
        div_le_div_of_nonneg_left (by positivity) hBsqw hwidth
      _ = (1/B)/Real.sqrt (g.branching:ℝ) := by
        field_simp [hw.ne',hc.ne',hB0.ne',hsqrt.ne']
      _ ≤ 1/Real.sqrt (g.branching:ℝ) :=
        div_le_div_of_nonneg_right ((div_le_one hB0).mpr hB) hsqrt.le
  refine ⟨hratio,hlenratio,htrans,?_,?_⟩
  · exact (div_le_one T.length_pos).mp (hlenratio.trans hsmall)
  · exact (div_le_one T.width_pos).mp (htrans.trans hsmall)

theorem source_packet_motion_coefficient (g : AngularGrid) (T : SlopeBox)
    {w B L A F Cfreq : ℝ} (hw : 0 < w) (hB : 1 ≤ B) (hL : 0 < L)
    (hA : 0 ≤ A) (hCfreq : 0 ≤ Cfreq) (hF : F ≤ Cfreq/w)
    (hwidth : B^2*w ≤ T.width) (h start : ℕ) (sR b : ℝ)
    (hs : g.index h sR = g.index h T.slope)
    (hblock : g.width h ≤ B*g.width start)
    (he : g.eligible (g.rootWidth/B^2) (w/T.length) start)
    (hb : |b| ≤ w/(g.width start*Real.sqrt (g.branching:ℝ)))
    (p maskExponent D : ℝ) :
    let r := B^2*w/g.width start
    let center := g.center start (g.index start T.slope)
    (L^(2*p+4)/r)*Real.exp (16*D)*|b|+(A/T.width)*|(sR-T.slope)*b|+
      (2*(⌈L⌉₊:ℝ)/L^maskExponent)*
        (|b|/T.length+|(sR-T.slope)*b|/T.width)*A+
      F*A*|T.slope-center| * |b| ≤
    (L^(2*p+4)*Real.exp (16*D)+A+(4*(⌈L⌉₊:ℝ)/L^maskExponent)*A+Cfreq*A)/
      Real.sqrt (g.branching:ℝ) := by
  dsimp only
  obtain ⟨hratio,hlenratio,htrans,-,-⟩ :=
    g.source_packet_displacement_ratios T hw hB hwidth h start sR b hs hblock he hb
  have hc := g.width_pos start
  have hG : (0:ℝ) < g.branching := by
    exact_mod_cast (show 0 < g.branching by have := g.branching_ge_two; omega)
  have hsqrt := Real.sqrt_pos.mpr hG
  have hcenter : |T.slope-g.center start (g.index start T.slope)| ≤ g.width start :=
    (g.slope_dist_center_le start T.slope).trans (by linarith)
  have hcarrier : F*|T.slope-g.center start (g.index start T.slope)| * |b| ≤
      Cfreq/Real.sqrt (g.branching:ℝ) := by
    calc
      _ ≤ (Cfreq/w)*g.width start*(w/(g.width start*Real.sqrt (g.branching:ℝ))) :=
        mul_le_mul (mul_le_mul hF hcenter (abs_nonneg _) (div_nonneg hCfreq hw.le))
          hb (abs_nonneg _) (mul_nonneg (div_nonneg hCfreq hw.le) hc.le)
      _ = _ := by field_simp [hw.ne',hc.ne',hsqrt.ne']
  have hfirst := mul_le_mul_of_nonneg_left hratio
    (mul_nonneg (Real.rpow_nonneg hL.le (2*p+4)) (Real.exp_pos (16*D)).le)
  have hsecond := mul_le_mul_of_nonneg_left htrans hA
  have hthird := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left (add_le_add hlenratio htrans)
      (show 0 ≤ 2*(⌈L⌉₊:ℝ)/L^maskExponent by positivity)) hA
  have hfourth := mul_le_mul_of_nonneg_right hcarrier hA
  calc
    _ = (L^(2*p+4)*Real.exp (16*D))*(|b|/(B^2*w/g.width start))+
        A*(|(sR-T.slope)*b|/T.width)+
        (2*(⌈L⌉₊:ℝ)/L^maskExponent)*
          (|b|/T.length+|(sR-T.slope)*b|/T.width)*A+
        (F*|T.slope-g.center start (g.index start T.slope)| * |b|)*A := by ring
    _ ≤ (L^(2*p+4)*Real.exp (16*D))*(1/Real.sqrt (g.branching:ℝ))+
        A*(1/Real.sqrt (g.branching:ℝ))+
        (2*(⌈L⌉₊:ℝ)/L^maskExponent)*
          (1/Real.sqrt (g.branching:ℝ)+1/Real.sqrt (g.branching:ℝ))*A+
        (Cfreq/Real.sqrt (g.branching:ℝ))*A :=
      add_le_add (add_le_add (add_le_add hfirst hsecond) hthird) hfourth
    _ = _ := by ring

end LipschitzHilbert.AngularGrid

end

end OAI
