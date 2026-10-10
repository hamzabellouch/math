import OAI.Geometry.Kahler.BaseProfiles

namespace OAI

open Complex
open scoped ContDiff Matrix Matrix.Norms.Elementwise
open scoped ContDiff Matrix Matrix.Norms.Elementwise ComplexOrder
open scoped ContDiff ComplexOrder
open scoped ContDiff ENNReal
open Set Filter Topology
open scoped ContDiff ENNReal Pointwise
open Set Filter Topology MeasureTheory
open scoped ContDiff
noncomputable section

open Set Filter Topology MeasureTheory
open scoped ContDiff ENNReal Pointwise
namespace PinchedHartogs.BaseConstruction

def phaseDerivative (W : Base → ℝ) (z : Base) : ℝ := fderiv ℝ W z (Complex.I • z)

def centralPoint (p : Sphere) (z : Base) : Base :=
  (bracket z (p:Base) / (‖bracket z (p:Base)‖:ℂ)) • (p:Base)

def densityHeight (k : ℕ) (p : Sphere) (z : Base) : ℝ :=
  -(k:ℝ)*Real.log ‖bracket z (p:Base)‖

def densityCorrectionRaw (k : ℕ) (f b : ℝ → ℝ) (W : Base → ℝ) (p : Sphere) (z : Base) : ℝ :=
  let c := bracket z (p:Base)
  let phase := c/(‖c‖:ℂ)
  let y := densityHeight k p z
  (‖c‖^2)⁻¹ * (f y * W (centralPoint p z) * (phase^k).re -
    b y / k * phaseDerivative W (centralPoint p z) * (phase^k).im)

def densityCorrection (k : ℕ) (R : ℝ) (f b : ℝ → ℝ) (W : Base → ℝ) (p : Sphere) (z : Base) : ℝ :=
  if Real.exp (-R/k) < ‖bracket z (p:Base)‖ then densityCorrectionRaw k f b W p z else 0

def density (Q : ℕ) (R : ℝ) (f b : ℝ → ℝ) (P : ℕ → Finset Sphere) : ℕ → Base → ℝ
  | 0 => fun _ => 1
  | j+1 => fun z => density Q R f b P j z +
      ∑ p ∈ P (Q^(j+1)), densityCorrection (Q^(j+1)) R f b (density Q R f b P j) p z

lemma phaseDerivative_smooth {W : Base → ℝ} (hW : ContDiff ℝ ∞ W) :
    ContDiff ℝ ∞ (phaseDerivative W) := by
  exact (hW.fderiv_right (by simp)).clm_apply ((Complex.I • (1 : Base →L[ℂ] Base)).restrictScalars ℝ).contDiff

lemma centralPoint_smoothAt (p : Sphere) {z : Base} (hz : bracket z (p:Base) ≠ 0) :
    ContDiffAt ℝ ∞ (centralPoint p) z := by
  have hc : ContDiff ℝ ∞ (fun z : Base => bracket z (p:Base)) := (bracket_analytic (p:Base)).contDiff.restrict_scalars ℝ
  have hn : ContDiffAt ℝ ∞ (fun z : Base => ‖bracket z (p:Base)‖) z := hc.contDiffAt.norm ℂ hz
  simpa only [centralPoint,div_eq_mul_inv,Function.comp_def,Complex.ofRealCLM_apply] using!
    ((hc.contDiffAt.mul ((Complex.ofRealCLM.contDiff.comp_contDiffAt z hn).inv
      (by simpa only [Function.comp_def,Complex.ofRealCLM_apply,ne_eq,Complex.ofReal_eq_zero] using norm_ne_zero_iff.mpr hz))).smul (contDiffAt_const (c := (p:Base))))

lemma densityHeight_smoothAt (k : ℕ) (p : Sphere) {z : Base} (hz : bracket z (p:Base) ≠ 0) :
    ContDiffAt ℝ ∞ (densityHeight k p) z := by
  have hc : ContDiff ℝ ∞ (fun z : Base => bracket z (p:Base)) := (bracket_analytic (p:Base)).contDiff.restrict_scalars ℝ
  exact contDiffAt_const.mul ((hc.contDiffAt.norm ℂ hz).log (norm_ne_zero_iff.mpr hz))

lemma densityCorrectionRaw_smoothAt (k : ℕ) {f b : ℝ → ℝ} {W : Base → ℝ}
    (hf : ContDiff ℝ ∞ f) (hb : ContDiff ℝ ∞ b) (hW : ContDiff ℝ ∞ W)
    (p : Sphere) {z : Base} (hz : bracket z (p:Base) ≠ 0) :
    ContDiffAt ℝ ∞ (densityCorrectionRaw k f b W p) z := by
  have hc : ContDiff ℝ ∞ (fun z : Base => bracket z (p:Base)) := (bracket_analytic (p:Base)).contDiff.restrict_scalars ℝ
  have hn := hc.contDiffAt.norm ℂ hz
  have hn0 := norm_ne_zero_iff.mpr hz
  have hphase : ContDiffAt ℝ ∞ (fun z : Base => bracket z (p:Base)/(‖bracket z (p:Base)‖:ℂ)) z := by
    simpa only [div_eq_mul_inv,Function.comp_def,Complex.ofRealCLM_apply] using! hc.contDiffAt.mul ((Complex.ofRealCLM.contDiff.comp_contDiffAt z hn).inv
      (by exact_mod_cast hn0 : (‖bracket z (p:Base)‖:ℂ) ≠ 0))
  have hy := densityHeight_smoothAt k p hz
  have hs := centralPoint_smoothAt p hz
  have hreal := Complex.reCLM.contDiff.comp_contDiffAt z (hphase.pow k)
  have him := Complex.imCLM.contDiff.comp_contDiffAt z (hphase.pow k)
  exact ((hn.pow 2).inv (pow_ne_zero 2 hn0)).mul
    ((((hf.contDiffAt.comp z hy).mul (hW.contDiffAt.comp z hs)).mul hreal).sub
      ((((hb.contDiffAt.comp z hy).div_const (k:ℝ)).mul ((phaseDerivative_smooth hW).contDiffAt.comp z hs)).mul him))

lemma densityCorrection_zero_low {k : ℕ} (hk : 0 < k) {R E : ℝ} {f b : ℝ → ℝ}
    (htail : ∀ y, E ≤ y → f y=0 ∧ b y=0) (W : Base → ℝ) (p : Sphere) (z : Base)
    (hz : ‖bracket z (p:Base)‖ ≤ Real.exp (-E/k)) : densityCorrection k R f b W p z=0 := by
  unfold densityCorrection
  split_ifs with hc
  · have hn : 0 < ‖bracket z (p:Base)‖ := lt_trans (Real.exp_pos _) hc
    have hh := Real.log_le_log hn hz
    rw [Real.log_exp] at hh
    have hk0 : (0:ℝ) < k := by exact_mod_cast hk
    have hhy : E ≤ densityHeight k p z := by
      have hm := (le_div_iff₀ hk0).mp hh
      unfold densityHeight
      nlinarith
    obtain ⟨hf,hb⟩ := htail _ hhy
    simp [densityCorrectionRaw,hf,hb]
  · rfl

lemma densityCorrection_smooth {k : ℕ} (hk : 0 < k) {R E : ℝ} (hER : E < R)
    {f b : ℝ → ℝ} {W : Base → ℝ}
    (hf : ContDiff ℝ ∞ f) (hb : ContDiff ℝ ∞ b) (hW : ContDiff ℝ ∞ W)
    (htail : ∀ y, E ≤ y → f y=0 ∧ b y=0) (p : Sphere) :
    ContDiff ℝ ∞ (densityCorrection k R f b W p) := by
  rw [contDiff_iff_contDiffAt]
  intro z
  have hc : Continuous (fun z : Base => ‖bracket z (p:Base)‖) := (bracket_analytic (p:Base)).continuous.norm
  by_cases hz : Real.exp (-R/k) < ‖bracket z (p:Base)‖
  · have he : densityCorrection k R f b W p =ᶠ[𝓝 z] densityCorrectionRaw k f b W p := by
      filter_upwards [(isOpen_lt continuous_const hc).mem_nhds hz] with v hv
      exact ite_eq_left hv
    exact (densityCorrectionRaw_smoothAt k hf hb hW p (norm_pos_iff.mp (lt_trans (Real.exp_pos _) hz))).congr_of_eventuallyEq he
  · have hk0 : (0:ℝ) < k := by exact_mod_cast hk
    have hcut : Real.exp (-R/k) < Real.exp (-E/k) := Real.exp_lt_exp.mpr ((div_lt_div_iff_of_pos_right hk0).mpr (neg_lt_neg hER))
    have hzE : ‖bracket z (p:Base)‖ < Real.exp (-E/k) := lt_of_le_of_lt (le_of_not_gt hz) hcut
    have he : densityCorrection k R f b W p =ᶠ[𝓝 z] (fun _ => 0) := by
      filter_upwards [(isOpen_lt hc continuous_const).mem_nhds hzE] with v hv
      exact densityCorrection_zero_low hk htail W p v hv.le
    exact contDiffAt_const.congr_of_eventuallyEq he

lemma density_smooth {Q : ℕ} (hQ : 0 < Q) {R E : ℝ} (hER : E < R)
    {f b : ℝ → ℝ} (hf : ContDiff ℝ ∞ f) (hb : ContDiff ℝ ∞ b)
    (htail : ∀ y, E ≤ y → f y=0 ∧ b y=0) (P : ℕ → Finset Sphere) (j : ℕ) :
    ContDiff ℝ ∞ (density Q R f b P j) := by
  induction j with
  | zero => exact contDiff_const
  | succ j ih =>
    exact ih.add (ContDiff.sum (fun p hp => densityCorrection_smooth (pow_pos hQ _) hER hf hb ih htail p))

end PinchedHartogs.BaseConstruction

end

end OAI
