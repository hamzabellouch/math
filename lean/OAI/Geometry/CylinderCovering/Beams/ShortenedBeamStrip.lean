import OAI.Geometry.CylinderCovering.Beams.StripFinite
import OAI.Geometry.CylinderCovering.Beams.sDefinitions

namespace OAI

noncomputable section
open Set MeasureTheory
namespace ShortenedBeam
open CylinderCovering

lemma strip_subset_generic (a : ℝ) :
    strip a ⊆ BeamStrip.strip (1/Real.sqrt 2) 2 (-1) 1
      (width a) (fun t => drift a t/2) := by
  rintro z ⟨x,y,t,ht,hx,hy,hgap,rfl⟩
  refine ⟨x,y,t,?_,abs_le.mp ht,?_,?_,?_⟩
  · ext i
    fin_cases i <;> simp [point,BeamStrip.vec,div_eq_mul_inv,mul_comm]
  · linarith [(abs_le.mp ht).1]
  · linarith [(abs_le.mp ht).2]
  · convert hgap using 1
    congr 1
    ring

lemma width_continuous (a : ℝ) : Continuous (width a) := by
  unfold width
  fun_prop

lemma half_drift_continuous (a : ℝ) : Continuous (fun t => drift a t/2) := by
  unfold drift
  fun_prop

lemma strip_integrand_identity (a t : ℝ) :
    2*(1/Real.sqrt 2)*width a t/BeamStrip.denominator (drift a t/2) =
      width a t/Real.sqrt (1+(a*t-a^2*t^3)^2) := by
  have hd : drift a t/2 = a*t-a^2*t^3 := by unfold drift; ring
  rw [hd,BeamStrip.denominator,Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 2)]
  have hs : 0 < Real.sqrt (1+(a*t-a^2*t^3)^2) := by positivity
  have htwo : 0 < Real.sqrt (2:ℝ) := by positivity
  have hsq : Real.sqrt (2:ℝ)^2 = 2 := Real.sq_sqrt (by norm_num)
  field_simp
  linear_combination -(width a t)*hsq

theorem finite_strip_actual (a : ℝ) {ε : ℝ} (hε : 0 < ε) :
    RuledApproximation.HasFiniteCover BeamStrip.IsHorizontalRectangle (strip a)
      ((∫ t in (-1:ℝ)..1, width a t/Real.sqrt (1+(a*t-a^2*t^3)^2)) + ε) := by
  have h := BeamStrip.finite_strip_cover
    (β := 1/Real.sqrt 2) (M := 2) (a := -1) (b := 1)
    (W := width a) (q := fun t => drift a t/2)
    (by positivity) (by norm_num) (by norm_num)
    (width_continuous a).continuousOn (half_drift_continuous a).continuousOn
    (fun t _ => le_max_right _ _) hε
  obtain ⟨N,C,hC,hcover,hcost⟩ := h
  refine ⟨N,C,hC,(strip_subset_generic a).trans hcover,?_⟩
  convert hcost using 1
  congr 1
  apply intervalIntegral.integral_congr
  intro t _
  exact (strip_integrand_identity a t).symm

theorem finite_strip_normalized (a : ℝ) {η : ℝ} (hη : 0 < η) :
    ∃ N : ℕ, ∃ C : Fin N → RuledApproximation.Cylinder,
      (∀ i, BeamStrip.IsHorizontalRectangle (C i)) ∧
      strip a ⊆ RuledApproximation.familySet C ∧
      RuledApproximation.familyArea C / ((1/Real.sqrt 2)^2/Real.sqrt 2) ≤
        2*Real.sqrt 2*(∫ t in (-1:ℝ)..1, width a t/Real.sqrt (1+(a*t-a^2*t^3)^2)) + η := by
  have hs : 0 < Real.sqrt (2:ℝ) := by positivity
  have hsq : Real.sqrt (2:ℝ)^2 = 2 := Real.sq_sqrt (by norm_num)
  have hε : 0 < η/(2*Real.sqrt 2) := by positivity
  obtain ⟨N,C,hC,hcover,hcost⟩ := finite_strip_actual a hε
  refine ⟨N,C,hC,hcover,?_⟩
  have hunit : (1/Real.sqrt 2)^2/Real.sqrt 2 = 1/(2*Real.sqrt 2) := by
    rw [div_pow,one_pow,hsq]
    ring
  rw [hunit,div_le_iff₀ (by positivity)]
  convert hcost using 1
  first | rfl | field_simp

end ShortenedBeam

end

end OAI
