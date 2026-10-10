import OAI.Geometry.TranslativeCovering.BlockSets

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
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal Topology

universe u_1

namespace BlockWeightMeasure
open MeasureTheory
variable {Ω : Type u_1} [MeasurableSpace Ω]

lemma denom_at_least {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    Real.sqrt (x*y) ≤ Real.sqrt (x*(1+x)*y*(1+y)) := by
  apply Real.sqrt_le_sqrt
  have hxy : 0 ≤ x*y := mul_nonneg hx.le hy.le
  have h1 : 1 ≤ (1+x)*(1+y) := by nlinarith
  nlinarith [mul_le_mul_of_nonneg_left h1 hxy]

lemma normalized_le_basic {z x y : ℝ} (hz : 0 ≤ z) (hx : 0 < x) (hy : 0 < y) :
    z / Real.sqrt (x*(1+x)*y*(1+y)) ≤ z / Real.sqrt (x*y) :=
  div_le_div_of_nonneg_left hz (Real.sqrt_pos.mpr (mul_pos hx hy)) (denom_at_least hx hy)

lemma trivial_bound {z q s : ℝ} (hz : 0 ≤ z)
    (hzq : z ≤ Real.exp (-q)) (hzs : z ≤ Real.exp (-s)) :
    z / Real.sqrt (Real.exp (-q)*(1+Real.exp (-q))*
      Real.exp (-s)*(1+Real.exp (-s))) ≤ Real.exp (-|q-s|/2) := by
  apply (normalized_le_basic hz (Real.exp_pos _) (Real.exp_pos _)).trans
  rw [← Real.exp_add, ← Real.exp_half]
  rw [div_le_iff₀ (Real.exp_pos _), ← Real.exp_add]
  rcases le_total q s with hqs | hsq
  · rw [abs_of_nonpos (sub_nonpos.mpr hqs)]
    convert hzs using 1
    congr 1
    ring_nf
  · rw [abs_of_nonneg (sub_nonneg.mpr hsq)]
    convert hzq using 1
    congr 1
    ring_nf

lemma affine_bound {z b b' ell ell' H c D : ℝ}
    (hz : 0 ≤ z) (hb : 0 < b) (hb' : 0 < b')
    (h : z / Real.sqrt (b*b') ≤ H*Real.exp (-c*D)) :
    z / Real.sqrt ((Real.exp (-ell)*b)*(1+Real.exp (-ell)*b)*
      (Real.exp (-ell')*b')*(1+Real.exp (-ell')*b')) ≤
      H*Real.exp ((ell+ell')/2-c*D) := by
  apply (normalized_le_basic hz (mul_pos (Real.exp_pos _) hb)
    (mul_pos (Real.exp_pos _) hb')).trans
  have heq : (Real.exp (-ell)*b)*(Real.exp (-ell')*b') =
      Real.exp (-(ell+ell'))*(b*b') := by rw [neg_add,Real.exp_add]; ring
  rw [heq, Real.sqrt_mul (Real.exp_pos _).le, ← Real.exp_half]
  have hepos := Real.exp_pos ((ell+ell')/2)
  have hid : z/(Real.exp (-(ell+ell')/2)*Real.sqrt (b*b')) =
      (z/Real.sqrt (b*b'))*Real.exp ((ell+ell')/2) := by
    rw [show -(ell+ell')/2 = -((ell+ell')/2) by ring, Real.exp_neg]
    field_simp
  rw [hid]
  calc
    _ ≤ (H*Real.exp (-c*D))*Real.exp ((ell+ell')/2) := mul_le_mul_of_nonneg_right h hepos.le
    _ = _ := by rw [mul_assoc, ← Real.exp_add]; congr 2; ring

lemma measure_trivial (μ : Measure Ω) [IsFiniteMeasure μ] {E F : Set Ω}
    (hE : 0 < μ.real E) (hF : 0 < μ.real F) :
    μ.real (E ∩ F) /
      Real.sqrt (μ.real E*(1+μ.real E)*μ.real F*(1+μ.real F)) ≤
      Real.exp (-|(-Real.log (μ.real E))-(-Real.log (μ.real F))|/2) := by
  have he : Real.exp (-(-Real.log (μ.real E))) = μ.real E := by rw [neg_neg,Real.exp_log hE]
  have hf : Real.exp (-(-Real.log (μ.real F))) = μ.real F := by rw [neg_neg,Real.exp_log hF]
  have hmE : μ.real (E ∩ F) ≤ μ.real E := measureReal_mono Set.inter_subset_left
  have hmF : μ.real (E ∩ F) ≤ μ.real F := measureReal_mono Set.inter_subset_right
  simpa only [he,hf] using trivial_bound (q := -Real.log (μ.real E)) (s := -Real.log (μ.real F))
    (measureReal_nonneg) (by simpa only [he] using hmE)
    (by simpa only [hf] using hmF)

end BlockWeightMeasure

end OAI
