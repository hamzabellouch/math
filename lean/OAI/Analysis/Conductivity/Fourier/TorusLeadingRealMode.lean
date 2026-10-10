import Mathlib
import OAI.Analysis.Conductivity.Branching.PhysicalAttachedAssembly

namespace OAI

section

noncomputable section
namespace ScalarConductivity
open Set Filter Topology MeasureTheory UnitAddTorus Real Complex

lemma torusQuadratic_neg_mode (s : Fin 3 → ℝ) (h : Fin 2 → ℤ) :
    torusQuadratic s (-h)=torusQuadratic s h := by
  simp only [torusQuadratic,Pi.neg_apply,Int.cast_neg]
  ring

lemma torusRate_neg_mode (s : Fin 3 → ℝ) (h : Fin 2 → ℤ) :
    torusRate s (-h)=torusRate s h := by
  simp only [torusRate,torusQuadratic_neg_mode]

lemma torusAngular_neg_mode (h : Fin 2 → ℤ) (x : Fin 3 → ℝ) :
    torusAngular (-h) x= -torusAngular h x := by
  simp only [torusAngular,Pi.neg_apply,Int.cast_neg,add_apply,
    smul_apply,ContinuousLinearMap.proj_apply,smul_eq_mul]
  ring

lemma polar_real_cosine (c : ℂ) (t : ℝ) :
    ‖c‖*Real.cos (t+c.arg)=c.re*Real.cos t-c.im*Real.sin t := by
  by_cases hc : c=0
  · simp [hc]
  · rw [Real.cos_add,Complex.cos_arg hc,Complex.sin_arg]
    field_simp

def realTorusCoeff (f : TorusL2) (h : Fin 2 → ℤ) : ℂ :=
  (mFourierCoeff f h+star (mFourierCoeff f (-h)))/2

lemma realTorusCoeff_neg (f : TorusL2) (h : Fin 2 → ℤ) :
    realTorusCoeff f (-h)=star (realTorusCoeff f h) := by
  simp [realTorusCoeff,star_div₀,star_add,add_comm]

lemma realTorusCoeff_bound (f : TorusL2) (h : Fin 2 → ℤ) :
    ‖realTorusCoeff f h‖≤‖f‖ := by
  unfold realTorusCoeff
  rw [norm_div]
  change ‖mFourierCoeff f h+star (mFourierCoeff f (-h))‖ / ‖(2:ℂ)‖ ≤ ‖f‖

  have hh := norm_add_le (mFourierCoeff f h) (star (mFourierCoeff f (-h)))
  have ha := torusFourierCoeff_bound f h
  have hb := torusFourierCoeff_bound f (-h)
  simp only [norm_star] at hh
  norm_num only [Complex.norm_ofNat] at *
  linarith

lemma realTorusCoeff_polar_mode (s : Fin 3 → ℝ) (f : TorusL2)
    (h : Fin 2 → ℤ) (x : Fin 3 → ℝ) :
    ‖realTorusCoeff f h‖*flatPhaseMode s h (realTorusCoeff f h).arg x=
      (((Real.exp (-torusRate s h*x 0):ℂ)*mFourierCoeff f h*
        Complex.exp ((torusAngular h x:ℂ)*Complex.I)).re+
       ((Real.exp (-torusRate s (-h)*x 0):ℂ)*mFourierCoeff f (-h)*
        Complex.exp ((torusAngular (-h) x:ℂ)*Complex.I)).re)/2 := by
  rw [torusRate_neg_mode,torusAngular_neg_mode]
  rw [complex_mode_real,complex_mode_real]
  simp only [flatPhaseMode,Real.cos_add_pi_div_two,Real.cos_neg,Real.sin_neg]
  rw [←mul_assoc,mul_comm ‖realTorusCoeff f h‖,mul_assoc,polar_real_cosine]
  simp only [realTorusCoeff,Complex.div_ofNat_re,Complex.div_ofNat_im,Complex.add_re,
    Complex.add_im,Complex.star_def,Complex.conj_re,Complex.conj_im]
  ring

lemma torusRealContinuation_polar {s : Fin 3 → ℝ}
    (hs : ∀ x y : ℝ,(1/2)*(x^2+y^2)≤ s 0*x^2+2*s 1*x*y+s 2*y^2)
    (f : TorusL2) {x : Fin 3 → ℝ} (hx : 0<x 0) :
    torusRealContinuation s f x=
      flatFourier s (fun h => ‖realTorusCoeff f h‖) (fun h => (realTorusCoeff f h).arg) x := by
  let F := fun h : Fin 2 → ℤ =>
    (((Real.exp (-torusRate s h*x 0):ℂ)*mFourierCoeff f h)*
      Complex.exp ((torusAngular h x:ℂ)*Complex.I)).re
  have hc := (ContinuousMap.evalCLM ℂ (torusAngles x)).hasSum
    (poisson_series_norm_summable hs hx f).of_norm.hasSum
  have hr := Complex.reCLM.hasSum hc
  change HasSum (fun h => ((Real.exp (-torusRate s h*x 0):ℂ)*mFourierCoeff f h*
    mFourier h (torusAngles x)).re) (torusRealContinuation s f x) at hr
  simp_rw [mFourier_torusAngles] at hr
  change HasSum F (torusRealContinuation s f x) at hr
  have hn : HasSum (fun h => F (-h)) (torusRealContinuation s f x) :=
    (Equiv.neg (Fin 2 → ℤ)).hasSum_iff.mpr hr
  have hh := (hr.add hn).div_const 2
  have he : (torusRealContinuation s f x+torusRealContinuation s f x)/2=
      torusRealContinuation s f x := by ring
  rw [he] at hh
  exact hh.tsum_eq.symm.trans (by
    unfold flatFourier
    apply tsum_congr
    intro h
    exact (realTorusCoeff_polar_mode s f h x).symm)

lemma realTorusCoeff_zero_re (f : TorusL2) :
    (realTorusCoeff f 0).re=(mFourierCoeff f 0).re := by
  simp only [realTorusCoeff,neg_zero,Complex.div_ofNat_re,Complex.add_re,
    Complex.star_def,Complex.conj_re]
  ring

lemma realTorusCoeff_polar_zero (s : Fin 3 → ℝ) (f : TorusL2) (x : Fin 3 → ℝ) :
    ‖realTorusCoeff f 0‖*flatPhaseMode s 0 (realTorusCoeff f 0).arg x=
      (mFourierCoeff f 0).re := by
  simp [flatPhaseMode,torusRate,torusQuadratic,torusAngular,realTorusCoeff_zero_re]

lemma realTorusCoeff_polar_neg (s : Fin 3 → ℝ) (f : TorusL2)
    (h : Fin 2 → ℤ) (x : Fin 3 → ℝ) :
    ‖realTorusCoeff f (-h)‖*flatPhaseMode s (-h) (realTorusCoeff f (-h)).arg x=
      ‖realTorusCoeff f h‖*flatPhaseMode s h (realTorusCoeff f h).arg x := by
  dsimp only [flatPhaseMode]
  rw [←mul_assoc,mul_comm ‖realTorusCoeff f (-h)‖,mul_assoc,polar_real_cosine,
    ←mul_assoc,mul_comm ‖realTorusCoeff f h‖,mul_assoc,polar_real_cosine,
    torusRate_neg_mode,torusAngular_neg_mode,realTorusCoeff_neg]
  simp [Real.cos_neg,Real.sin_neg]

def realTorusAmplitude (f : TorusL2) (h : Fin 2 → ℤ) : ℝ :=
  if h=0 then 0 else ‖realTorusCoeff f h‖

def realTorusPhase (f : TorusL2) (h : Fin 2 → ℤ) : ℝ := (realTorusCoeff f h).arg

lemma realTorusAmplitude_bound (f : TorusL2) (h : Fin 2 → ℤ) :
    |realTorusAmplitude f h|≤‖f‖ := by
  unfold realTorusAmplitude
  split_ifs
  · simp
  · simpa only [abs_of_nonneg (norm_nonneg _)] using realTorusCoeff_bound f h

lemma torusRealContinuation_mean_free {s : Fin 3 → ℝ}
    (hs : ∀ x y : ℝ,(1/2)*(x^2+y^2) ≤ s 0*x^2+2*s 1*x*y+s 2*y^2)
    (f : TorusL2) {x : Fin 3 → ℝ} (hx : 0<x 0) :
    torusRealContinuation s f x=(mFourierCoeff f 0).re+
      flatFourier s (realTorusAmplitude f) (realTorusPhase f) x := by
  classical
  rw [torusRealContinuation_polar hs f hx]
  have hb (h) : |‖realTorusCoeff f h‖|≤‖f‖ := by
    simpa only [abs_of_nonneg (norm_nonneg _)] using realTorusCoeff_bound f h
  rw [flatFourier,(flatFourier_summable hs hb hx).tsum_eq_add_tsum_ite 0,
    realTorusCoeff_polar_zero]
  congr 1
  unfold flatFourier
  apply tsum_congr
  intro h
  simp only [realTorusAmplitude,realTorusPhase]
  split_ifs <;> simp

lemma torusRate_uniform_positive {s : Fin 3 → ℝ}
    (hs : ∀ x y : ℝ,(1/2)*(x^2+y^2) ≤ s 0*x^2+2*s 1*x*y+s 2*y^2) :
    ∃ g>0,∀ h : Fin 2 → ℤ,h≠0 → g≤torusRate s h := by
  have he : ({h : Fin 2 → ℤ | h≠0} : Set (Fin 2 → ℤ)).Nonempty := by
    refine ⟨![1,0],?_⟩
    intro he
    have := congrFun he 0
    norm_num at this
  obtain ⟨h,hh,hmin⟩ := torus_modes_have_first hs he
  refine ⟨torusRate s h,Real.sqrt_pos.mpr (torusQuadratic_pos hs hh),?_⟩
  intro l hl
  exact Real.sqrt_le_sqrt (hmin l hl)

lemma torus_leading_rate_gap {s : Fin 3 → ℝ}
    (hs : ∀ x y : ℝ,(1/2)*(x^2+y^2) ≤ s 0*x^2+2*s 1*x*y+s 2*y^2)
    (hres : ∀ h l : Fin 2 → ℤ,torusQuadratic s h=torusQuadratic s l → l=h ∨ l= -h)
    {M : Set (Fin 2 → ℤ)} (hne : M.Nonempty) (hzero : 0∉M) :
    ∃ h∈M,0<torusRate s h ∧ ∃ g>0,
      ∀ l∈M,l≠h → l≠-h → torusRate s h+g≤torusRate s l := by
  obtain ⟨h,hh,hq,d,hd,hmin⟩ := torus_leading_pair_gap hs hres hne hzero
  refine ⟨h,hh,Real.sqrt_pos.mpr hq,Real.sqrt (torusQuadratic s h+d)-torusRate s h,
    sub_pos.mpr (Real.sqrt_lt_sqrt hq.le (by linarith)),?_⟩
  intro l hl hne hn
  have hle := Real.sqrt_le_sqrt (hmin l hl hne hn)
  change Real.sqrt (torusQuadratic s h)+(Real.sqrt (torusQuadratic s h+d)-
    Real.sqrt (torusQuadratic s h))≤Real.sqrt (torusQuadratic s l)
  linarith

end ScalarConductivity

end
end

end OAI
