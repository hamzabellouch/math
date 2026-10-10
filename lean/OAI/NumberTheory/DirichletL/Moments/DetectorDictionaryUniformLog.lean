import OAI.NumberTheory.DirichletL.Moments.DetectorDictionaryUniform
import OAI.NumberTheory.DirichletL.Moments.Lattice

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff Topology
open Set

namespace SevenEighths.CenteredMomentDetectorDictionary
open HeckeInverseAmplification HeckeDyadic

def realInterpolatedLog (W : ℝ→ℂ) (p : ℝ×ℝ) (x : ℝ) : ℂ :=
  Real.exp (-p.1*x) • W (Real.exp x)

lemma realInterpolatedLog_smooth (W : ℝ→ℂ) (hW : ContDiff ℝ ∞ W) :
    ContDiff ℝ ∞ (Function.uncurry (realInterpolatedLog W)) := by
  unfold realInterpolatedLog Function.uncurry
  exact (by fun_prop : ContDiff ℝ ∞ (fun p : (ℝ×ℝ)×ℝ=>Real.exp (-p.1.1*p.2))).smul
    (hW.comp (by fun_prop))

lemma realInterpolatedLog_support (W : ℝ→ℂ) (a b : ℝ) (ha : 0<a)
    (hs : Function.support W⊆Icc a b) (p : ℝ×ℝ) :
    Function.support (realInterpolatedLog W p)⊆Icc (-(|Real.log a|+|Real.log b|)) (|Real.log a|+|Real.log b|) := by
  intro x hx
  have hw : W (Real.exp x)≠0 := by intro hw;exact hx (by simp [realInterpolatedLog,hw])
  have hlo : Real.log a≤x := by simpa only [Real.log_exp] using Real.log_le_log ha (hs hw).1
  have hhi : x≤Real.log b := by simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos x) (hs hw).2
  constructor <;> linarith [neg_abs_le (Real.log a),le_abs_self (Real.log b),abs_nonneg (Real.log a),abs_nonneg (Real.log b)]

def realInterpolatedLogSchwartz (W : ℝ→ℂ) (a b : ℝ) (ha : 0<a)
    (hs : Function.support W⊆Icc a b) (hW : ContDiff ℝ ∞ W) (p : ℝ×ℝ) : 𝓢(ℝ,ℂ) :=
  CubicReflectionKernel.logSchwartz (twistProfile W p.1 0) a b ha
    ((twistProfile_support _ _ _).trans hs) (twistProfile_smooth W p.1 0 a b ha hs hW)

lemma realInterpolatedLogSchwartz_apply (W : ℝ→ℂ) (a b : ℝ) (ha : 0<a)
    (hs : Function.support W⊆Icc a b) (hW : ContDiff ℝ ∞ W) (p : ℝ×ℝ) (x : ℝ) :
    realInterpolatedLogSchwartz W a b ha hs hW p x=realInterpolatedLog W p x := by
  rw [realInterpolatedLogSchwartz,CubicReflectionKernel.logSchwartz_apply]
  unfold twistProfile realInterpolatedLog
  rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr (Real.exp_pos x).ne'),
    ←Complex.ofReal_log (Real.exp_pos x).le,Real.log_exp]
  simp only [HeckeDyadic.shift,Complex.ofReal_zero,zero_mul,sub_zero]
  change W (Real.exp x)*Complex.exp ((x:ℂ)*-(p.1:ℂ))=
    ((Real.exp (-p.1*x):ℝ):ℂ)*W (Real.exp x)
  rw [Complex.ofReal_exp,Complex.ofReal_mul,Complex.ofReal_neg]
  have he : (x:ℂ)*-(p.1:ℂ)=-(p.1:ℂ)*(x:ℂ) := by ring
  rw [he,mul_comm]

def interpolatedProfile (W : ℝ→ℂ) (a b : ℝ) (ha : 0<a)
    (hs : Function.support W⊆Icc a b) (hW : ContDiff ℝ ∞ W) (σ t : ℝ) : 𝓢(ℝ,ℂ) :=
  CenteredMomentLattice.normPowerProfile (twistProfile W σ 0) a b ha
    ((twistProfile_support _ _ _).trans hs) (twistProfile_smooth W σ 0 a b ha hs hW) t

lemma interpolatedProfile_apply (W : ℝ→ℂ) (a b : ℝ) (ha : 0<a)
    (hs : Function.support W⊆Icc a b) (hW : ContDiff ℝ ∞ W) (σ t x : ℝ) :
    interpolatedProfile W a b ha hs hW σ t x=twistProfile W σ t x := by
  rw [interpolatedProfile,CenteredMomentLattice.normPowerProfile_apply]
  unfold twistProfile
  by_cases hw : W x=0
  · simp [hw]
  · have hx : 0<x := ha.trans_le (hs hw).1
    calc
      _=W x*((x:ℂ)^(Complex.I*t)*(x:ℂ)^(-HeckeDyadic.shift σ 0)) := by ring
      _=W x*(x:ℂ)^(Complex.I*t-HeckeDyadic.shift σ 0) := by
        rw [←Complex.cpow_add _ _ (Complex.ofReal_ne_zero.mpr hx.ne')];rfl
      _=_ := by congr 2;unfold HeckeDyadic.shift;simp only [Complex.ofReal_zero,zero_mul,sub_zero];ring

end SevenEighths.CenteredMomentDetectorDictionary

end

end OAI
