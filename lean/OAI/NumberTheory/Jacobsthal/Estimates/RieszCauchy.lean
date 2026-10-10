import OAI.NumberTheory.Jacobsthal.Partitions.RieszRectangle

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

namespace Erdos970Dependency.SiegelWalfisz
open _root_.Set _root_.Complex _root_.MeasureTheory

lemma cauchy_vertical_shift (f : ℂ → ℂ) (left right T : ℝ)
    (hlr : left ≤ right) (hT : 0 ≤ T)
    (hf : _root_.Erdos970.HolomorphicOn f (Icc left right ×ℂ Icc (-T) T)) :
    _root_.Erdos970.VIntegral f right (-T) T = _root_.Erdos970.VIntegral f left (-T) T -
      _root_.Erdos970.HIntegral f left right (-T) + _root_.Erdos970.HIntegral f left right T := by
  let z : ℂ := (left:ℂ)-(T:ℂ)*Complex.I
  let w : ℂ := (right:ℂ)+(T:ℂ)*Complex.I
  have hzr : z.re = left := by simp [z]
  have hzi : z.im = -T := by simp [z]
  have hwr : w.re = right := by simp [w]
  have hwi : w.im = T := by simp [w]
  have he : Rectangle z w = Icc left right ×ℂ Icc (-T) T := by
    simp only [Rectangle,hzr,hzi,hwr,hwi,uIcc_of_le hlr,uIcc_of_le (by linarith : -T ≤ T)]
  have hz := hf.vanishesOnRectangle (z := z) (w := w) (fun s hs => by simpa only [he] using hs)
  simp only [_root_.Erdos970.RectangleIntegral,hzr,hzi,hwr,hwi] at hz
  linear_combination hz

lemma norm_cauchy_vertical_le (f : ℂ → ℂ) (left right T : ℝ)
    (hlr : left ≤ right) (hT : 0 ≤ T)
    (hf : _root_.Erdos970.HolomorphicOn f (Icc left right ×ℂ Icc (-T) T)) :
    ‖_root_.Erdos970.VIntegral f right (-T) T‖ ≤ ‖_root_.Erdos970.VIntegral f left (-T) T‖ +
      ‖_root_.Erdos970.HIntegral f left right (-T)‖ + ‖_root_.Erdos970.HIntegral f left right T‖ := by
  rw [cauchy_vertical_shift f left right T hlr hT hf]
  calc
    _ ≤ ‖_root_.Erdos970.VIntegral f left (-T) T - _root_.Erdos970.HIntegral f left right (-T)‖ +
      ‖_root_.Erdos970.HIntegral f left right T‖ := norm_add_le _ _
    _ ≤ _ := by gcongr; exact norm_sub_le _ _

lemma norm_verticalIntegral_eq (f : ℂ → ℂ) (sigma : ℝ) :
    ‖_root_.Erdos970.VerticalIntegral f sigma‖ = ‖∫ t:ℝ, f ((sigma:ℂ)+(t:ℂ)*Complex.I)‖ := by
  simp only [_root_.Erdos970.VerticalIntegral,norm_smul,Complex.norm_I,one_mul]

lemma norm_VIntegral_eq (f : ℂ → ℂ) (sigma lo hi : ℝ) :
    ‖_root_.Erdos970.VIntegral f sigma lo hi‖ = ‖∫ t in lo..hi, f ((sigma:ℂ)+(t:ℂ)*Complex.I)‖ := by
  simp only [_root_.Erdos970.VIntegral,norm_smul,Complex.norm_I,one_mul]

lemma norm_full_vertical_shift_le (f : ℂ → ℂ) (left right T : ℝ)
    (hlr : left ≤ right) (hT : 0 ≤ T)
    (hf : _root_.Erdos970.HolomorphicOn f (Icc left right ×ℂ Icc (-T) T))
    (hi : Integrable (fun t:ℝ => f ((right:ℂ)+(t:ℂ)*Complex.I))) :
    ‖_root_.Erdos970.VerticalIntegral f right‖ ≤
      ‖∫ t in Iic (-T), f ((right:ℂ)+(t:ℂ)*Complex.I)‖ +
      ‖_root_.Erdos970.VIntegral f left (-T) T‖ + ‖_root_.Erdos970.HIntegral f left right (-T)‖ +
      ‖_root_.Erdos970.HIntegral f left right T‖ +
      ‖∫ t in Ici T, f ((right:ℂ)+(t:ℂ)*Complex.I)‖ := by
  rw [_root_.Erdos970.verticalIntegral_split_three (-T) T hi]
  have h1 := norm_add_le (Complex.I • (∫ t in Iic (-T), f ((right:ℂ)+(t:ℂ)*Complex.I)) +
    _root_.Erdos970.VIntegral f right (-T) T) (Complex.I • ∫ t in Ici T, f ((right:ℂ)+(t:ℂ)*Complex.I))
  have h2 := norm_add_le (Complex.I • ∫ t in Iic (-T), f ((right:ℂ)+(t:ℂ)*Complex.I))
    (_root_.Erdos970.VIntegral f right (-T) T)
  simp only [norm_smul,Complex.norm_I,one_mul] at h1 h2
  have h3 := norm_cauchy_vertical_le f left right T hlr hT hf
  linarith

end Erdos970Dependency.SiegelWalfisz

end

end Erdos970

end OAI
