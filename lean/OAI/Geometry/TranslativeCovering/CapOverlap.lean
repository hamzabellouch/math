import OAI.Geometry.TranslativeCovering.CapLens

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

namespace CapOverlap
open Set MeasureTheory Metric SphericalLaw CapGeometry CapLens

lemma cap_antimono {n : ℕ} [NeZero n] (e : Sphere n) {t s : ℝ} (hts : t ≤ s) :
    (σ n).real (halfcap e.val s) ≤ (σ n).real (halfcap e.val t) :=
  measureReal_mono (fun _ hw => hts.trans_lt hw) (measure_ne_top _ _)

lemma cap_ratio_decay {n : ℕ} [NeZero n] (e : Sphere n) {l u t s : ℝ}
    (hl : 0 < l) (hu : u < 1) (hlt : l ≤ t) (hts : t ≤ s) (hsu : s ≤ u)
    (hdim : 2*(1/l+1/(1-u^2)) ≤ (n:ℝ)*l) :
    (σ n).real (halfcap e.val s) ≤ Real.exp (-(n:ℝ)*l*(s-t)/2) *
      (σ n).real (halfcap e.val t) := by
  have hp : 0 < (σ n).real (halfcap e.val t) :=
    ENNReal.toReal_pos (ne_of_gt (halfcap_positive e ((hts.trans hsu).trans_lt hu)))
      (measure_ne_top _ _)
  have hc : ((1/l+1/(1-u^2))-(n:ℝ)*l)*(s-t) ≤ -(n:ℝ)*l*(s-t)/2 := by
    nlinarith [mul_nonneg (by linarith : 0 ≤ (n:ℝ)*l/2-(1/l+1/(1-u^2)))
      (sub_nonneg.mpr hts)]
  exact ((div_le_iff₀ hp).mp (halfcap_ratio e hl hu hlt hts hsu).2).trans
    (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr hc) hp.le)

lemma inter_subset_bisector {n : ℕ} (e f : Sphere n) {l t s k : ℝ}
    (hl : 0 < l) (hlt : l ≤ t) (hts : t ≤ s) (hk : 0 ≤ k) (hkl : k ≤ l/16)
    (hgap : s-t ≤ l*‖e.val-f.val‖^2/8) (hz : e.val+f.val ≠ 0) :
    halfcap e.val t ∩ halfcap f.val s ⊆
      halfcap (unit (e.val+f.val) hz).val (s+k*‖e.val-f.val‖^2) := by
  have he := mem_sphere_zero_iff_norm.mp e.property
  have hf := mem_sphere_zero_iff_norm.mp f.property
  have hr : ‖e.val+f.val‖ ≤ 2 := by
    have hh := norm_add_le e.val f.val
    rw [he, hf] at hh
    linarith
  have hd : ‖e.val-f.val‖^2 + ‖e.val+f.val‖^2 = 4 := by
    rw [norm_sub_sq_real, norm_add_sq_real, he, hf]; ring
  have hdr : ‖e.val-f.val‖^2 ≤ 4*(2-‖e.val+f.val‖) := by
    nlinarith [sq_nonneg (2-‖e.val+f.val‖)]
  have hs : 0 ≤ s := (hl.trans_le (hlt.trans hts)).le
  have hsr : s*‖e.val+f.val‖ ≤ 2*s-l*‖e.val-f.val‖^2/4 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr (hlt.trans hts)) (sub_nonneg.mpr hr),
      mul_nonneg hl.le (sub_nonneg.mpr hdr)]
  have hkr : k*‖e.val-f.val‖^2*‖e.val+f.val‖ ≤ 2*k*‖e.val-f.val‖^2 :=
    by nlinarith [mul_nonneg (mul_nonneg hk (sq_nonneg ‖e.val-f.val‖)) (sub_nonneg.mpr hr)]
  have hbd : (s+k*‖e.val-f.val‖^2)*‖e.val+f.val‖ ≤ t+s := by
    nlinarith [mul_nonneg (by linarith : 0 ≤ l-16*k) (sq_nonneg ‖e.val-f.val‖)]
  intro w hw
  change s+k*‖e.val-f.val‖^2 < inner ℝ w.val (unit (e.val+f.val) hz).val
  rw [inner_unit, lt_div_iff₀ (norm_pos_iff.mpr hz), inner_add_right]
  exact hbd.trans_lt (add_lt_add hw.1 hw.2)

lemma halfcap_overlap_sq_ordered {n : ℕ} [NeZero n] (e f : Sphere n)
    {l u U t s k : ℝ} (hl : 0 < l) (hU : U < 1)
    (hlt : l ≤ t) (hts : t ≤ s) (hsu : s ≤ u) (huU : u ≤ U)
    (hk : 0 ≤ k) (hkl : k ≤ l/16) (hku : 4*k ≤ U-u)
    (hdim : 2*(1/l+1/(1-U^2)) ≤ (n:ℝ)*l) :
    ((σ n).real (halfcap e.val t ∩ halfcap f.val s))^2 ≤
      Real.exp (-(n:ℝ)*l*k*‖e.val-f.val‖^2) *
        (σ n).real (halfcap e.val t) * (σ n).real (halfcap f.val s) := by
  let A := (σ n).real (halfcap e.val t)
  let B := (σ n).real (halfcap f.val s)
  let I := (σ n).real (halfcap e.val t ∩ halfcap f.val s)
  let d := ‖e.val-f.val‖^2
  have hA : 0 ≤ A := measureReal_nonneg
  have hB : 0 ≤ B := measureReal_nonneg
  have hI : 0 ≤ I := measureReal_nonneg
  have heq (r : ℝ) : (σ n).real (halfcap f.val r) = (σ n).real (halfcap e.val r) :=
    congrArg ENNReal.toReal (halfcap_equal_norm
      ((mem_sphere_zero_iff_norm.mp f.property).trans (mem_sphere_zero_iff_norm.mp e.property).symm) r)
  have hBA : B ≤ A := by dsimp [B, A]; rw [heq]; exact cap_antimono e hts
  have hIB : I ≤ B := measureReal_mono inter_subset_right (measure_ne_top _ _)
  have hd : 0 ≤ d := sq_nonneg _
  have hd4 : d ≤ 4 := by
    have hh : ‖e.val-f.val‖ ≤ 2 := by
      have hh := norm_sub_le e.val f.val
      rw [mem_sphere_zero_iff_norm.mp e.property, mem_sphere_zero_iff_norm.mp f.property] at hh
      linarith
    dsimp [d]; nlinarith [norm_nonneg (e.val-f.val)]
  change I^2 ≤ Real.exp (-(n:ℝ)*l*k*d)*A*B
  by_cases hgap : s-t ≤ l*d/8
  · by_cases hz : e.val+f.val = 0
    · have hemt : halfcap e.val t ∩ halfcap f.val s = ∅ := by
        apply eq_empty_iff_forall_notMem.mpr
        intro w hw
        have ht : t < inner ℝ w.val e.val := hw.1
        have hs : s < inner ℝ w.val f.val := hw.2
        have hh := add_lt_add ht hs
        rw [← inner_add_right, hz, inner_zero_right] at hh
        linarith
      dsimp [I]; rw [hemt, measureReal_empty, zero_pow (by decide : 2 ≠ 0)]
      positivity
    · have hqU : s+k*d ≤ U := by nlinarith [mul_nonneg hk (sub_nonneg.mpr hd4)]
      have hsub := inter_subset_bisector e f hl hlt hts hk hkl hgap hz
      have hm := measureReal_mono hsub (measure_ne_top (σ n) _)
      have heq2 : (σ n).real (halfcap (unit (e.val+f.val) hz).val (s+k*d)) =
          (σ n).real (halfcap f.val (s+k*d)) :=
        congrArg ENNReal.toReal (halfcap_equal_norm
          ((mem_sphere_zero_iff_norm.mp (unit (e.val+f.val) hz).property).trans
            (mem_sphere_zero_iff_norm.mp f.property).symm) _)
      change I ≤ (σ n).real (halfcap (unit (e.val+f.val) hz).val (s+k*d)) at hm
      rw [heq2] at hm
      have hr := cap_ratio_decay f hl hU (hlt.trans hts)
        (by nlinarith [mul_nonneg hk hd] : s ≤ s+k*d) hqU hdim
      have hi : I ≤ Real.exp (-(n:ℝ)*l*k*d/2)*B := by
        have he : -(n:ℝ)*l*((s+k*d)-s)/2 = -(n:ℝ)*l*k*d/2 := by ring
        rw [he] at hr
        exact hm.trans hr
      have hisq : I^2 ≤ (Real.exp (-(n:ℝ)*l*k*d/2)*B)^2 :=
        pow_le_pow_left₀ hI hi 2
      have hE : (Real.exp (-(n:ℝ)*l*k*d/2))^2 = Real.exp (-(n:ℝ)*l*k*d) := by
        rw [sq, ← Real.exp_add]; congr 1; ring
      calc
        I^2 ≤ _ := hisq
        _ = Real.exp (-(n:ℝ)*l*k*d)*B*B := by rw [mul_pow,hE]; ring
        _ ≤ Real.exp (-(n:ℝ)*l*k*d)*A*B :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hBA (Real.exp_nonneg _)) hB
  · have hbig : 2*k*d ≤ s-t := by
      nlinarith [mul_nonneg (by linarith : 0 ≤ l-16*k) hd]
    have hr := cap_ratio_decay e hl hU hlt hts (hsu.trans huU) hdim
    rw [← heq s] at hr
    have hE : Real.exp (-(n:ℝ)*l*(s-t)/2) ≤ Real.exp (-(n:ℝ)*l*k*d) := by
      apply Real.exp_le_exp.mpr
      nlinarith [mul_nonneg (mul_nonneg (Nat.cast_nonneg n) hl.le) (sub_nonneg.mpr hbig)]
    have hBexp : B ≤ Real.exp (-(n:ℝ)*l*k*d)*A :=
      hr.trans (mul_le_mul_of_nonneg_right hE hA)
    exact (pow_le_pow_left₀ hI hIB 2).trans (by
      simpa [sq] using mul_le_mul_of_nonneg_right hBexp hB)

end CapOverlap

end OAI
