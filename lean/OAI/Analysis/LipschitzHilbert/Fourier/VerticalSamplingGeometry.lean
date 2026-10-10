import OAI.Analysis.LipschitzHilbert.Estimates.PlanarChangeVariables

namespace OAI

/-! Short sampling maps and the interpolation between the two orders of
vertical convolution and directional sampling. -/
noncomputable section
open MeasureTheory
namespace LipschitzHilbert.PacketRepresentation

def verticalSampling (u : (ℝ×ℝ) → ℝ) (t a b : ℝ) (z : ℝ×ℝ) : ℝ×ℝ :=
  (z.1-a,z.2-b-t*u z)

theorem verticalSampling_measurable (u : (ℝ×ℝ) → ℝ) (hu : Measurable u) (t a b : ℝ) :
    Measurable (verticalSampling u t a b) := by
  unfold verticalSampling
  fun_prop

theorem verticalSampling_antilipschitz (u : (ℝ×ℝ) → ℝ) (hu : LipschitzWith 2 u)
    (t a b : ℝ) (ht : |t|≤1/4) : AntilipschitzWith 2 (verticalSampling u t a b) := by
  apply AntilipschitzWith.of_le_mul_dist
  intro z w
  have hu' := hu.dist_le_mul z w
  rw [Real.dist_eq] at hu'
  have hx : |z.1-w.1|≤dist (verticalSampling u t a b z) (verticalSampling u t a b w) := by
    have h := le_max_left |z.1-w.1| |(z.2-b-t*u z)-(w.2-b-t*u w)|
    simpa only [verticalSampling,Prod.dist_eq,Real.dist_eq,sub_sub_sub_cancel_right] using h
  have hy : |z.2-w.2|≤dist (verticalSampling u t a b z) (verticalSampling u t a b w)+
      |t| *(2*dist z w) := by
    have hid : z.2-w.2=((z.2-b-t*u z)-(w.2-b-t*u w))+t*(u z-u w) := by ring
    calc
      _ = |((z.2-b-t*u z)-(w.2-b-t*u w))+t*(u z-u w)| := congrArg abs hid
      _ ≤ |(z.2-b-t*u z)-(w.2-b-t*u w)| +|t| *|u z-u w| := by
        simpa only [abs_mul] using abs_add_le ((z.2-b-t*u z)-(w.2-b-t*u w)) (t*(u z-u w))
      _ ≤ dist (verticalSampling u t a b z) (verticalSampling u t a b w)+|t| *(2*dist z w) := by
        apply add_le_add
        · exact le_max_right _ _
        · exact mul_le_mul_of_nonneg_left hu' (abs_nonneg t)
  have hd : dist z w≤dist (verticalSampling u t a b z) (verticalSampling u t a b w)+
      |t| *(2*dist z w) := by
    rw [Prod.dist_eq,Real.dist_eq,Real.dist_eq]
    exact max_le (hx.trans (le_add_of_nonneg_right (mul_nonneg (abs_nonneg t)
      (mul_nonneg (by norm_num) (dist_nonneg (x:=z) (y:=w)))))) hy
  change dist z w≤2*dist (verticalSampling u t a b z) (verticalSampling u t a b w)
  nlinarith [dist_nonneg (x:=z) (y:=w)]

theorem verticalSampling_energy (u : (ℝ×ℝ) → ℝ) (hu : LipschitzWith 2 u)
    (t a b : ℝ) (ht : |t|≤1/4) (f : (ℝ×ℝ) → ℂ) (hfm : Measurable f)
    (hf : MemLp f 2 planeMeasure) :
    MemLp (f ∘ verticalSampling u t a b) 2 planeMeasure ∧
      (∫ z, ‖f (verticalSampling u t a b z)‖^2 ∂planeMeasure)≤4*∫ z, ‖f z‖^2 ∂planeMeasure :=
  planar_memLp_comp_bound _ (verticalSampling_measurable u hu.continuous.measurable t a b)
    (verticalSampling_antilipschitz u hu t a b ht) f hfm hf

theorem verticalTranslation_isometry (s : ℝ) : Isometry (verticalTranslation s) := by
  apply Isometry.of_dist_eq
  intro z w
  change dist (z.1,z.2-s) (w.1,w.2-s)=dist z w
  simp only [Prod.dist_eq,Real.dist_eq,sub_sub_sub_cancel_right]

def verticalBlend (u : (ℝ×ℝ) → ℝ) (s theta : ℝ) (z : ℝ×ℝ) : ℝ :=
  (1-theta)*u z+theta*u (verticalTranslation s z)

theorem verticalBlend_lipschitz (u : (ℝ×ℝ) → ℝ) (hu : LipschitzWith 2 u)
    (s theta : ℝ) (h0 : 0≤theta) (h1 : theta≤1) : LipschitzWith 2 (verticalBlend u s theta) := by
  apply LipschitzWith.of_dist_le_mul
  intro z w
  have hz := hu.dist_le_mul z w
  have hs := hu.dist_le_mul (verticalTranslation s z) (verticalTranslation s w)
  rw [(verticalTranslation_isometry s).dist_eq z w] at hs
  rw [Real.dist_eq] at hz hs ⊢
  have hid : verticalBlend u s theta z-verticalBlend u s theta w=
      (1-theta)*(u z-u w)+theta*(u (verticalTranslation s z)-u (verticalTranslation s w)) := by
    unfold verticalBlend
    ring
  rw [hid]
  calc
    _ ≤ |1-theta| *|u z-u w| +|theta| *|u (verticalTranslation s z)-u (verticalTranslation s w)| := by
      simpa only [abs_mul] using abs_add_le ((1-theta)*(u z-u w))
        (theta*(u (verticalTranslation s z)-u (verticalTranslation s w)))
    _ ≤ (1-theta)*(2*dist z w)+theta*(2*dist z w) := by
      rw [abs_of_nonneg (sub_nonneg.mpr h1),abs_of_nonneg h0]
      exact add_le_add (mul_le_mul_of_nonneg_left hz (sub_nonneg.mpr h1))
        (mul_le_mul_of_nonneg_left hs h0)
    _ = _ := by norm_num; ring

end LipschitzHilbert.PacketRepresentation

end

end OAI
