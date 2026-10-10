import Mathlib
import OAI.Analysis.HardSphere.Bridges.SegmentMeasurable

namespace OAI

noncomputable section
open MeasureTheory Set Filter ProbabilityTheory
open scoped ENNReal NNReal Topology BigOperators
namespace HardSphere.Bridge
open Wiener GaussianPacking

def hitConstant : ℝ := 256*(packingConstant+1)*(8+3072*normCubeMean)
lemma hitConstant_pos : 0<hitConstant := by
  have hn : 0≤normCubeMean := integral_nonneg (fun _ ↦ by positivity)
  have hk := packingConstant_pos
  unfold hitConstant
  positivity

lemma cubic_noise_le {A : ℝ} (hA : 0≤A) :
    (2+A)^3+3072*normCubeMean ≤ (8+3072*normCubeMean)*(1+A)^3 := by
  have hn : 0≤normCubeMean := integral_nonneg (fun _ ↦ by positivity)
  have ha : (2+A)^3 ≤ (2*(1+A))^3 := pow_le_pow_left₀ (by linarith) (by linarith) 3
  have hb : 1≤(1+A)^3 := one_le_pow₀ (by linarith)
  have hc := mul_le_mul_of_nonneg_left hb (mul_nonneg (by norm_num : (0:ℝ)≤3072) hn)
  nlinarith

lemma inverse_density_le {t : ℝ} (ht : 0<t) {s : Time} (hs : 0<(s:ℝ)) (hs1 : (s:ℝ)≤1/2) :
    (Real.sqrt ((2*(legVariance t s:ℝ))⁻¹))^3 ≤ 1/((t*(s:ℝ))*Real.sqrt (t*(s:ℝ))) := by
  have hx : 0<t*(s:ℝ) := mul_pos ht hs
  have hv : t*(s:ℝ) ≤ 2*(legVariance t s:ℝ) := by
    rw [legVariance_val ht.le]
    have := mul_le_mul_of_nonneg_left hs1 (mul_nonneg ht.le hs.le)
    nlinarith
  have hvpos : 0<2*(legVariance t s:ℝ) := hx.trans_le hv
  have hle := Real.sqrt_le_sqrt (inv_anti₀ hx hv)
  apply (pow_le_pow_left₀ (Real.sqrt_nonneg _) hle 3).trans_eq
  rw [Real.sqrt_inv]
  have he := Real.sq_sqrt hx.le
  field_simp
  nlinarith [Real.sqrt_pos.mpr hx]

lemma packed_scale_le {ε : ℝ} (hε : 0<ε) {s : Time} (hs : (s:ℝ)≤1/2) :
    ((1-(s:ℝ))*ε)⁻¹^3 ≤ 8*ε⁻¹^3 := by
  have h : ε/2 ≤ (1-(s:ℝ))*ε := by nlinarith
  have hp : 0<ε/2 := by positivity
  have hi := inv_anti₀ hp h
  have hspos : 0<(1-(s:ℝ))*ε := hp.trans_le h
  have hc := pow_le_pow_left₀ (inv_nonneg.mpr hspos.le) hi 3
  have he : (ε/2)⁻¹^3=8*ε⁻¹^3 := by
    simp only [inv_div,div_pow]
    norm_num
    ring
  exact hc.trans_eq he

lemma segment_sum_simplified {m : ℕ} (y : Fin m → Point) (v : Point) (s w : Time)
    (c : Time → Point) {t r C A ε : ℝ} (ht : 0<t) (hr : 0<r) (hC : 0≤C) (hA0 : 0≤A)
    (hs : 0<(s:ℝ)) (hs1 : (s:ℝ)≤1/2) (hε : 0<ε)
    (hsep : ∀i j,i≠j → ε^2 ≤ square (y i-y j))
    (hA : ∀q : Time,(q:ℝ)≤(w:ℝ) → ‖c q-c 0‖≤r*A)
    (hdrift : (w:ℝ)*C≤r) (hscale : t*(1-(s:ℝ))*(w:ℝ)≤r^2) :
    (∑i,law (segmentHit t (y i) v s w c r C)) ≤
      ENNReal.ofReal (hitConstant*r^3*(1+A)^3*(ε⁻¹^3+1/((t*(s:ℝ))*Real.sqrt (t*(s:ℝ))))) := by
  have hslt : (s:ℝ)<1 := by linarith
  apply (segment_sum_bound y v s w c ht hr hC hA0 hs hslt hε hsep hA hdrift hscale).trans
  apply ENNReal.ofReal_le_ofReal
  have hden := add_le_add (packed_scale_le hε hs1) (inverse_density_le ht hs hs1)
  have hd0 : 0≤1/((t*(s:ℝ))*Real.sqrt (t*(s:ℝ))) := by positivity
  have he0 : 0≤ε⁻¹^3 := by positivity
  have hn := cubic_noise_le hA0
  have hn0 : 0≤(2+A)^3+3072*normCubeMean := by
    have : 0≤normCubeMean := integral_nonneg (fun _ ↦ by positivity)
    positivity
  have hnon : 0≤8+3072*normCubeMean := by
    have : 0≤normCubeMean := integral_nonneg (fun _ ↦ by positivity)
    positivity
  have hk := packingConstant_pos.le
  calc
    _ ≤ 32*(packingConstant*(8*ε⁻¹^3+1/((t*(s:ℝ))*Real.sqrt (t*(s:ℝ)))))*r^3*
        ((8+3072*normCubeMean)*(1+A)^3) := by
      apply mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hden packingConstant_pos.le) (by norm_num))
        (pow_nonneg hr.le _)) hn0 |>.trans
      exact mul_le_mul_of_nonneg_left hn (by positivity)
    _ ≤ _ := by
      unfold hitConstant
      have ha0 : 0≤(1+A)^3 := by positivity
      have hh : 32*(packingConstant*(8*ε⁻¹^3+1/((t*(s:ℝ))*Real.sqrt (t*(s:ℝ))))) ≤
          256*(packingConstant+1)*(ε⁻¹^3+1/((t*(s:ℝ))*Real.sqrt (t*(s:ℝ)))) := by
        nlinarith [mul_nonneg hk hd0]
      have hmul := mul_le_mul_of_nonneg_right hh (mul_nonneg (pow_nonneg hr.le 3) (mul_nonneg hnon ha0))
      simpa only [mul_assoc,mul_comm,mul_left_comm] using hmul

lemma joint_segment_sum_bound {m : ℕ} (y : Fin m → Point) (s w : Time)
    (c : C(Time,Point)) {t r C A ε : ℝ} (ht : 0<t) (hr : 0<r) (hC : 0≤C) (hA0 : 0≤A)
    (hs : 0<(s:ℝ)) (hs1 : (s:ℝ)≤1/2) (hε : 0<ε)
    (hsep : ∀i j,i≠j → ε^2 ≤ square (y i-y j))
    (hA : ∀q : Time,(q:ℝ)≤(w:ℝ) → ‖c q-c 0‖≤r*A)
    (hdrift : (w:ℝ)*C≤r) (hscale : t*(1-(s:ℝ))*(w:ℝ)≤r^2)
    {B : Set Point} (hB : (volume : Measure Point) B≤1) :
    (∑i,((volume.restrict B).prod law) (jointSegmentHit t (y i) s w c r C)) ≤
      ENNReal.ofReal (hitConstant*r^3*(1+A)^3*(ε⁻¹^3+1/((t*(s:ℝ))*Real.sqrt (t*(s:ℝ))))) := by
  have hE i := (jointSegmentHit_closed t (y i) s w c r C).measurableSet
  simp_rw [Measure.prod_apply (hE _)]
  rw [←lintegral_finsetSum Finset.univ (fun i _ ↦ measurable_measure_prodMk_left (hE i))]
  have hp := lintegral_mono (μ:=volume.restrict B) fun v ↦
    segment_sum_simplified y v s w c ht hr hC hA0 hs hs1 hε hsep hA hdrift hscale
  apply hp.trans
  rw [lintegral_const,Measure.restrict_apply_univ]
  calc
    _ ≤ _*1 := mul_le_mul' le_rfl hB
    _ = _ := mul_one _

lemma uniform_segment_simplified (y : Point) (s w : Time) (c : Time → Point) (B : Set Point)
    {t r C A : ℝ} (ht : 0<t) (hr : 0<r) (hC : 0≤C) (hA0 : 0≤A)
    (hs : (1:ℝ)/2≤(s:ℝ)) (hB : ∀v∈B,‖v-y‖≤C)
    (hA : ∀q : Time,(q:ℝ)≤(w:ℝ) → ‖c q-c 0‖≤r*A)
    (hdrift : ((1-(s:ℝ))*(w:ℝ))*C≤r) (hscale : t*(1-(s:ℝ))*(w:ℝ)≤r^2) :
    (law.prod ((volume : Measure Point).restrict B)) (uniformSegmentHit t y s w c r B) ≤
      ENNReal.ofReal (hitConstant*r^3*(1+A)^3) := by
  have hs0 : 0<(s:ℝ) := by linarith
  apply (uniform_segment_bound y s w c B ht hr hC hA0 hs0 hB hA hdrift hscale).trans
  apply ENNReal.ofReal_le_ofReal
  have hi : (s:ℝ)⁻¹^3≤8 := by
    have hh := pow_le_pow_left₀ (inv_nonneg.mpr hs0.le) (inv_anti₀ (by norm_num : (0:ℝ)<1/2) hs) 3
    norm_num at hh
    simpa only [inv_pow] using hh
  have hc := cubic_noise_le hA0
  have hN := normCubeMean_nonneg
  have hK := packingConstant_pos.le
  calc
    _ ≤ 32*8*r^3*((8+3072*normCubeMean)*(1+A)^3) := by gcongr
    _ ≤ _ := by
      unfold hitConstant
      have hp := mul_le_mul_of_nonneg_right (show (1:ℝ)≤packingConstant+1 by linarith)
        (show 0≤256*(8+3072*normCubeMean)*r^3*(1+A)^3 by positivity)
      norm_num only [show (32:ℝ)*8=256 by norm_num]
      simpa only [one_mul,mul_assoc,mul_comm,mul_left_comm] using hp

end HardSphere.Bridge

end

end OAI
