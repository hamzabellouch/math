import Mathlib

namespace OAI

noncomputable section
open MeasureTheory Set
open scoped ENNReal

namespace CubicTorus

end CubicTorus
end

section

noncomputable section
open MeasureTheory Set Complex
open scoped ENNReal Real
namespace CubicTorus

theorem periodic_wirtinger {f g : ℝ → ℂ}
    (hf : ∀ x ∈ Icc (0 : ℝ) 1, HasDerivAt f (g x) x)
    (hg : IntervalIntegrable g volume 0 1)
    (hf2 : MemLp f 2 (volume.restrict (Ioc (0 : ℝ) 1)))
    (hg2 : MemLp g 2 (volume.restrict (Ioc (0 : ℝ) 1)))
    (hp : f 1=f 0) (hm : ∫ x in (0 : ℝ)..1,f x=0) :
    4*Real.pi^2*(∫ x in (0 : ℝ)..1,‖f x‖^2) ≤ ∫ x in (0 : ℝ)..1,‖g x‖^2 := by
  have h01 : (0 : ℝ)<1 := by norm_num
  have hcf0 : fourierCoeffOn h01 f 0=0 := by
    rw [fourierCoeffOn_eq_integral]
    simpa using hm
  have hcoef (n : ℤ) :
      4*Real.pi^2*‖fourierCoeffOn h01 f n‖^2 ≤ ‖fourierCoeffOn h01 g n‖^2 := by
    by_cases hn : n=0
    · subst n
      rw [hcf0]
      simp
    have he := fourierCoeffOn_of_hasDerivAt h01 hn (by simpa using hf) hg
    have he' : fourierCoeffOn h01 g n=
        (2*(Real.pi : ℂ)*Complex.I*(n : ℂ))*fourierCoeffOn h01 f n := by
      simp only [hp,sub_self,mul_zero,sub_zero,zero_sub,Complex.ofReal_one,Complex.ofReal_zero,sub_zero,one_mul] at he
      have hp0 : (Real.pi : ℂ)≠0 := by exact_mod_cast Real.pi_ne_zero
      have hn0 : (n : ℂ)≠0 := by exact_mod_cast hn
      field_simp at he
      linear_combination -he
    have hen := congrArg (fun z : ℂ => ‖z‖^2) he'
    simp only [norm_mul,Complex.norm_ofNat,Complex.norm_real,Real.norm_eq_abs,
      abs_of_pos Real.pi_pos,Complex.norm_I,mul_one,Complex.norm_intCast] at hen
    have hn1 : (1 : ℝ)≤|(n : ℝ)| := by
      exact_mod_cast (Int.one_le_abs hn)
    have hsq : 1≤|(n : ℝ)|^2 := by nlinarith [sq_nonneg (|(n : ℝ)|-1)]
    nlinarith [mul_nonneg (sq_nonneg (2*Real.pi*‖fourierCoeffOn h01 f n‖))
      (sub_nonneg.mpr hsq)]
  have hfs := hasSum_sq_fourierCoeffOn h01 hf2
  have hgs := hasSum_sq_fourierCoeffOn h01 hg2
  have hle := hasSum_le hcoef (hfs.mul_left (4*Real.pi^2)) hgs
  simpa using hle

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Complex
open scoped ENNReal Real
namespace CubicTorus

theorem mean_zero_curve_area_energy {f g : ℝ → ℂ}
    (hf : ∀ x ∈ Icc (0 : ℝ) 1, HasDerivAt f (g x) x)
    (hg : IntervalIntegrable g volume 0 1)
    (hf2 : MemLp f 2 (volume.restrict (Ioc (0 : ℝ) 1)))
    (hg2 : MemLp g 2 (volume.restrict (Ioc (0 : ℝ) 1)))
    (hp : f 1=f 0) (hm : ∫ x in (0 : ℝ)..1,f x=0) :
    2*Real.pi*|∫ x in (0 : ℝ)..1,(star (f x)*g x).im| ≤
      ∫ x in (0 : ℝ)..1,‖g x‖^2 := by
  have hw := periodic_wirtinger hf hg hf2 hg2 hp hm
  have hfs := hf2.integrable_norm_pow (by norm_num : (2 : ℕ)≠0)
  have hgs := hg2.integrable_norm_pow (by norm_num : (2 : ℕ)≠0)
  have hmul : Integrable (fun x => (star (f x)*g x).im)
      (volume.restrict (Ioc (0 : ℝ) 1)) := (hf2.star.integrable_mul hg2).im
  have hyp (x : ℝ) : 4*Real.pi*|(star (f x)*g x).im| ≤
      4*Real.pi^2*‖f x‖^2+‖g x‖^2 := by
    have hi := Complex.abs_im_le_norm (star (f x)*g x)
    simp only [norm_mul,norm_star] at hi
    have hi' := mul_le_mul_of_nonneg_left hi (by positivity : 0≤4*Real.pi)
    nlinarith [sq_nonneg (2*Real.pi*‖f x‖-‖g x‖)]
  have hle := integral_mono (hmul.abs.const_mul (4*Real.pi))
    ((hfs.const_mul (4*Real.pi^2)).add hgs) hyp
  have habs := norm_integral_le_integral_norm (μ := volume.restrict (Ioc (0 : ℝ) 1))
    (fun x => (star (f x)*g x).im)
  simp only [Real.norm_eq_abs] at habs
  simp only [Pi.add_apply] at hle
  rw [integral_const_mul,integral_add (hfs.const_mul _) hgs,integral_const_mul] at hle
  simp only [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ)≤1)] at hw ⊢
  have hh := mul_le_mul_of_nonneg_left habs (by positivity : 0≤4*Real.pi)
  linarith

theorem closed_curve_area_energy {f g : ℝ → ℂ}
    (hf : ∀ x ∈ Icc (0 : ℝ) 1, HasDerivAt f (g x) x)
    (hg : IntervalIntegrable g volume 0 1)
    (hf2 : MemLp f 2 (volume.restrict (Ioc (0 : ℝ) 1)))
    (hg2 : MemLp g 2 (volume.restrict (Ioc (0 : ℝ) 1)))
    (hp : f 1=f 0) :
    4*Real.pi*|(1/2 : ℝ)*(∫ x in (0 : ℝ)..1,(star (f x)*g x).im)| ≤
      ∫ x in (0 : ℝ)..1,‖g x‖^2 := by
  let c : ℂ := ∫ x in (0 : ℝ)..1,f x
  let F : ℝ → ℂ := fun x => f x-c
  have hF : ∀ x ∈ Icc (0 : ℝ) 1,HasDerivAt F (g x) x :=
    fun x hx => (hf x hx).sub_const c
  have hfi : IntervalIntegrable f volume 0 1 := by
    apply ContinuousOn.intervalIntegrable
    simpa only [uIcc_of_le (by norm_num : (0 : ℝ)≤1)] using
      (show ContinuousOn f (Icc (0 : ℝ) 1) from fun x hx => (hf x hx).continuousAt.continuousWithinAt)
  have hmean : ∫ x in (0 : ℝ)..1,F x=0 := by
    rw [show F=(fun x => f x-c) from rfl,intervalIntegral.integral_sub hfi intervalIntegrable_const]
    simp [c]
  have hFp : F 1=F 0 := by simp only [F,hp]
  have hF2 : MemLp F 2 (volume.restrict (Ioc (0 : ℝ) 1)) := hf2.sub (memLp_const c)
  have hg0 : ∫ x in (0 : ℝ)..1,g x=0 := by
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (by simpa using hf) hg,hp,sub_self]
  have htrans : (∫ x in (0 : ℝ)..1,(star (F x)*g x).im)=
      ∫ x in (0 : ℝ)..1,(star (f x)*g x).im := by
    have hmi := hf2.star.integrable_mul hg2
    have hgi : Integrable g (volume.restrict (Ioc (0 : ℝ) 1)) := hg.1
    simp only [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ)≤1)] at hg0 ⊢
    have hA := integral_im (hF2.star.integrable_mul hg2)
    have hB := integral_im hmi
    change (∫ x in Ioc (0 : ℝ) 1,(star (F x)*g x).im)=
      (∫ x in Ioc (0 : ℝ) 1,star (F x)*g x).im at hA
    change (∫ x in Ioc (0 : ℝ) 1,(star (f x)*g x).im)=
      (∫ x in Ioc (0 : ℝ) 1,star (f x)*g x).im at hB
    rw [hA,hB]
    congr 1
    simp only [F,star_sub,sub_mul]
    change Integrable (fun x => star (f x)*g x) (volume.restrict (Ioc (0 : ℝ) 1)) at hmi
    rw [integral_sub hmi (hgi.const_mul _),integral_const_mul,hg0,mul_zero,sub_zero]
  have hh := mean_zero_curve_area_energy hF hg hF2 hg2 hFp hmean
  rw [htrans] at hh
  rw [abs_mul,abs_of_pos (by norm_num : (0 : ℝ)<1/2)]
  nlinarith only [hh]

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped Topology Real
namespace CubicTorus

theorem positive_periodic_primitive_inverse {h : ℝ → ℝ} (hc : Continuous h)
    (hp : Function.Periodic h 1) (hpos : ∀ x,0<h x) :
    ∃ e : ℝ ≃o ℝ, (∀ x,e x=∫ t in (0 : ℝ)..x,h t) ∧
      (∀ x,HasDerivAt e (h x) x) ∧
      (∀ x,HasDerivAt e.symm (h (e.symm x))⁻¹ x) := by
  let A : ℝ → ℝ := fun x => ∫ t in (0 : ℝ)..x,h t
  have hA (x : ℝ) : HasDerivAt A (h x) x := (hc.integral_hasStrictDerivAt 0 x).hasDerivAt
  have hAc : Continuous A := continuous_iff_continuousAt.mpr fun x => (hA x).continuousAt
  have hmon : StrictMono A := strictMono_of_deriv_pos fun x => by rw [(hA x).deriv]; exact hpos x
  have hsurj : Function.Surjective A := hAc.surjective
    (hp.tendsto_atTop_intervalIntegral_of_pos' (hc.intervalIntegrable 0 1) hpos (by norm_num))
    (hp.tendsto_atBot_intervalIntegral_of_pos' (hc.intervalIntegrable 0 1) hpos (by norm_num))
  let e : ℝ ≃o ℝ := hmon.orderIsoOfSurjective A hsurj
  refine ⟨e,fun _ => rfl,hA,?_⟩
  intro x
  exact HasDerivAt.of_local_left_inverse e.symm.continuous.continuousAt (hA (e.symm x))
    (hpos _).ne' (Eventually.of_forall fun y => e.apply_symm_apply y)

theorem positive_periodic_arclength_parameter {h : ℝ → ℝ} (hc : Continuous h)
    (hp : Function.Periodic h 1) (hpos : ∀ x,0<h x) :
    ∃ q d : ℝ → ℝ, Continuous q ∧ Continuous d ∧ StrictMono q ∧
      (∀ x,HasDerivAt q (d x) x) ∧ q 0=0 ∧ q 1=1 ∧
      (∀ x,0<d x) ∧ (∀ x,d x*h (q x)=∫ t in (0 : ℝ)..1,h t) := by
  obtain ⟨e,he,heD,heI⟩ := positive_periodic_primitive_inverse hc hp hpos
  let L : ℝ := ∫ t in (0 : ℝ)..1,h t
  have hL : 0<L := intervalIntegral.intervalIntegral_pos_of_pos (hc.intervalIntegrable 0 1) hpos (by norm_num)
  let q : ℝ → ℝ := fun x => e.symm (L*x)
  let d : ℝ → ℝ := fun x => L/h (q x)
  have hqc : Continuous q := e.symm.continuous.comp (continuous_const.mul continuous_id)
  have hdc : Continuous d := continuous_const.div (hc.comp hqc) (fun x => (hpos _).ne')
  have hqD (x : ℝ) : HasDerivAt q (d x) x := by
    simpa only [Function.comp_def,mul_one,one_mul,d,q,div_eq_mul_inv,mul_comm] using
      (heI (L*x)).comp x ((hasDerivAt_id x).const_mul L)
  have hq0 : q 0=0 := by
    apply e.injective
    change e (e.symm (L*0))=e 0
    rw [e.apply_symm_apply,he]
    simp
  have hq1 : q 1=1 := by
    apply e.injective
    change e (e.symm (L*1))=e 1
    rw [e.apply_symm_apply,he]
    simp [L]
  refine ⟨q,d,hqc,hdc,?_,hqD,hq0,hq1,fun x => div_pos hL (hpos _),?_⟩
  · intro x y hxy
    exact e.symm.strictMono (mul_lt_mul_of_pos_left hxy hL)
  · intro x
    dsimp [d]
    exact div_mul_cancel₀ L (hpos _).ne'

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Complex
open scoped ENNReal Real
namespace CubicTorus

lemma continuous_memLp_two_Ioc {f : ℝ → ℂ} (hf : Continuous f) :
    MemLp f 2 (volume.restrict (Ioc (0 : ℝ) 1)) := by
  apply (memLp_two_iff_integrable_sq_norm hf.aestronglyMeasurable).2
  exact ((hf.norm.pow 2).continuousOn.integrableOn_compact isCompact_Icc).mono_set Ioc_subset_Icc_self

theorem planar_curve_isoperimetric {f g : ℝ → ℂ}
    (hf : ∀ x,HasDerivAt f (g x) x) (hgc : Continuous g)
    (hp : Function.Periodic f 1) (hreg : ∀ x,g x≠0) :
    4*Real.pi*|(1/2 : ℝ)*(∫ x in (0 : ℝ)..1,(star (f x)*g x).im)| ≤
      (∫ x in (0 : ℝ)..1,‖g x‖)^2 := by
  have hfc : Continuous f := continuous_iff_continuousAt.mpr fun x => (hf x).continuousAt
  have hgp : Function.Periodic g 1 := by
    intro x
    have hd : HasDerivAt f (g (x+1)) x := by
      have hh := (hf (x+1)).scomp x ((hasDerivAt_id x).add_const 1)
      have hpeq : (fun x => f (x+1))=f := funext hp
      simpa only [Function.comp_def,id_eq,hpeq,one_smul] using hh
    exact hd.unique (hf x)
  have hspeedp : Function.Periodic (fun x => ‖g x‖) 1 := fun x => congrArg norm (hgp x)
  obtain ⟨q,d,hqc,hdc,hmon,hqD,hq0,hq1,hdpos,hsp⟩ :=
    positive_periodic_arclength_parameter hgc.norm hspeedp (fun x => norm_pos_iff.mpr (hreg x))
  let F : ℝ → ℂ := f ∘ q
  let G : ℝ → ℂ := fun t => d t • g (q t)
  have hF : ∀ x,HasDerivAt F (G x) x := fun x => (hf (q x)).scomp x (hqD x)
  have hFc : Continuous F := hfc.comp hqc
  have hGc : Continuous G := hdc.smul (hgc.comp hqc)
  have hFp : F 1=F 0 := by simpa only [F,Function.comp_def,hq0,hq1,zero_add] using hp 0
  have hW := closed_curve_area_energy (fun x _ => hF x) (hGc.intervalIntegrable 0 1)
    (continuous_memLp_two_Ioc hFc) (continuous_memLp_two_Ioc hGc) hFp
  have hnG (x : ℝ) : ‖G x‖=(∫ t in (0 : ℝ)..1,‖g t‖) := by
    dsimp only [G]
    rw [norm_smul,Real.norm_eq_abs,abs_of_pos (hdpos x)]
    exact hsp x
  have henergy : (∫ x in (0 : ℝ)..1,‖G x‖^2)=(∫ t in (0 : ℝ)..1,‖g t‖)^2 := by
    simp only [hnG,intervalIntegral.integral_const,sub_zero,one_smul]
  have harea : (∫ x in (0 : ℝ)..1,(star (F x)*G x).im)=
      ∫ x in (0 : ℝ)..1,(star (f x)*g x).im := by
    have hareaC : Continuous (fun x => (star (f x)*g x).im) :=
      Complex.continuous_im.comp (hfc.star.mul hgc)
    have hsub := intervalIntegral.integral_deriv_smul_comp
      (fun x (_ : x∈uIcc (0 : ℝ) 1) => hqD x) hdc.continuousOn hareaC
    rw [hq0,hq1] at hsub
    convert hsub using 1
    apply intervalIntegral.integral_congr
    intro x hx
    simp only [F,G,Function.comp_def,Complex.real_smul,smul_eq_mul]
    simp
    ring
  rwa [henergy,harea] at hW

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Complex
open scoped ENNReal Real
namespace CubicTorus

def unitAngle (t : ℝ) : ℂ := Complex.exp ((2*Real.pi*t : ℝ)*Complex.I)

lemma unitAngle_norm (t : ℝ) : ‖unitAngle t‖=1 := by simp [unitAngle,Complex.norm_exp]

lemma unitAngle_periodic : Function.Periodic unitAngle 1 := by
  intro x
  change Complex.exp ((2*Real.pi*(x+1) : ℝ)*Complex.I)=_
  rw [show ((2*Real.pi*(x+1) : ℝ) : ℂ)*Complex.I=
    ((2*Real.pi*x : ℝ) : ℂ)*Complex.I+2*(Real.pi : ℂ)*Complex.I by push_cast; ring]
  exact Complex.exp_periodic _

lemma unitAngle_deriv (t : ℝ) :
    HasDerivAt unitAngle (((2*Real.pi : ℝ)*Complex.I)*unitAngle t) t := by
  have hd := ((((hasDerivAt_id t).const_mul (2*Real.pi)).ofReal_comp).mul_const Complex.I).cexp
  convert! hd using 1
  simp [unitAngle,id_eq,mul_comm]

lemma unitAngle_continuous : Continuous unitAngle :=
  continuous_iff_continuousAt.mpr fun t => (unitAngle_deriv t).continuousAt

def radialCurve (r : ℝ → ℝ) (t : ℝ) : ℂ := (r t : ℂ)*unitAngle t

def radialVelocity (r dr : ℝ → ℝ) (t : ℝ) : ℂ :=
  ((dr t : ℂ)+(2*Real.pi*r t : ℝ)*Complex.I)*unitAngle t

lemma radialCurve_deriv {r dr : ℝ → ℝ} (hr : ∀ t,HasDerivAt r (dr t) t) (t : ℝ) :
    HasDerivAt (radialCurve r) (radialVelocity r dr t) t := by
  convert! ((hr t).ofReal_comp).mul (unitAngle_deriv t) using 1
  simp only [radialVelocity,Complex.ofReal_mul]
  ring

lemma radialVelocity_norm_sq (r dr : ℝ → ℝ) (t : ℝ) :
    ‖radialVelocity r dr t‖^2=(dr t)^2+(2*Real.pi*r t)^2 := by
  rw [radialVelocity,norm_mul,unitAngle_norm,mul_one,Complex.sq_norm]
  simp [Complex.normSq_apply,pow_two]

lemma radialCurve_area_integrand (r dr : ℝ → ℝ) (t : ℝ) :
    (star (radialCurve r t)*radialVelocity r dr t).im=2*Real.pi*(r t)^2 := by
  have hu : star (unitAngle t)*unitAngle t=1 := by
    rw [Complex.star_def,Complex.conj_mul',unitAngle_norm]
    norm_num
  have he : star (radialCurve r t)*radialVelocity r dr t=
      (r t : ℂ)*((dr t : ℂ)+(2*Real.pi*r t : ℝ)*Complex.I) := by
    simp only [radialCurve,radialVelocity,star_mul,Complex.star_def,Complex.conj_ofReal]
    calc
      _ = (r t : ℂ)*((dr t : ℂ)+(2*Real.pi*r t : ℝ)*Complex.I)*
          (star (unitAngle t)*unitAngle t) := by simp only [Complex.star_def]; ring
      _ = _ := by rw [hu,mul_one]
  rw [he]
  simp only [Complex.mul_im,Complex.ofReal_re,Complex.add_im,Complex.ofReal_im,
    Complex.I_re,Complex.I_im,mul_zero,zero_mul,zero_add,mul_one,add_zero]
  ring

theorem radial_curve_isoperimetric {r dr : ℝ → ℝ}
    (hr : ∀ t,HasDerivAt r (dr t) t) (hdc : Continuous dr)
    (hp : Function.Periodic r 1) (hpos : ∀ t,0<r t) :
    4*Real.pi^2*(∫ t in (0 : ℝ)..1,(r t)^2) ≤
      (∫ t in (0 : ℝ)..1,Real.sqrt ((dr t)^2+(2*Real.pi*r t)^2))^2 := by
  have hrc : Continuous r := continuous_iff_continuousAt.mpr fun t => (hr t).continuousAt
  have hvc : Continuous (radialVelocity r dr) := by
    exact ((Complex.continuous_ofReal.comp hdc).add
      ((Complex.continuous_ofReal.comp (continuous_const.mul hrc)).mul continuous_const)).mul unitAngle_continuous
  have hreg (t : ℝ) : radialVelocity r dr t≠0 := by
    intro hz
    have hn := radialVelocity_norm_sq r dr t
    rw [hz,norm_zero,zero_pow (by norm_num : (2 : ℕ)≠0)] at hn
    have hrt := hpos t
    have hh : 0<(2*Real.pi*r t)^2 := sq_pos_of_pos (by positivity)
    nlinarith [sq_nonneg (dr t)]
  have hperiod : Function.Periodic (radialCurve r) 1 := by
    intro x; simp only [radialCurve,hp x,unitAngle_periodic x]
  have hh := planar_curve_isoperimetric (radialCurve_deriv hr) hvc hperiod hreg
  have hspeed (t : ℝ) : ‖radialVelocity r dr t‖=
      Real.sqrt ((dr t)^2+(2*Real.pi*r t)^2) := by
    rw [← radialVelocity_norm_sq,Real.sqrt_sq (norm_nonneg _)]
  simp only [radialCurve_area_integrand,hspeed] at hh
  rw [intervalIntegral.integral_const_mul] at hh
  have hi : 0≤∫ t in (0 : ℝ)..1,(r t)^2 :=
    intervalIntegral.integral_nonneg (by norm_num) (fun t _ => sq_nonneg (r t))
  rw [abs_of_nonneg (by positivity)] at hh
  nlinarith

end CubicTorus

end
end

section

noncomputable section
open Set Complex
open scoped Topology Real
namespace CubicTorus

def complexSquareGauge (z : ℂ) : ℝ := max |z.re| |z.im|
def complexFold (z : ℂ) : ℂ := ⟨|z.re|,|z.im|⟩
def unitSquareScale (t : ℝ) : ℝ := 1/(2*complexSquareGauge (unitAngle t))
def unitSquareEnd (t : ℝ) : ℂ := unitSquareScale t • complexFold (unitAngle t)

lemma complexSquareGauge_pos {z : ℂ} (hz : z≠0) : 0<complexSquareGauge z := by
  by_contra hh
  have hl : max |z.re| |z.im|≤0 := le_of_not_gt hh
  have h1 : z.re=0 := abs_eq_zero.mp (le_antisymm ((le_max_left _ _).trans hl) (abs_nonneg _))
  have h2 : z.im=0 := abs_eq_zero.mp (le_antisymm ((le_max_right _ _).trans hl) (abs_nonneg _))
  exact hz (Complex.ext h1 h2)

lemma unitAngle_ne_zero (t : ℝ) : unitAngle t≠0 := by
  intro hz
  have hh := unitAngle_norm t
  simp [hz] at hh

lemma unitSquareScale_pos (t : ℝ) : 0<unitSquareScale t :=
  one_div_pos.mpr (mul_pos (by norm_num) (complexSquareGauge_pos (unitAngle_ne_zero t)))

lemma complexSquareGauge_continuous : Continuous complexSquareGauge :=
  Complex.continuous_re.abs.max Complex.continuous_im.abs

lemma complexFold_continuous : Continuous complexFold := by
  exact Complex.equivRealProdCLM.symm.continuous.comp (Complex.continuous_re.abs.prodMk Complex.continuous_im.abs)

lemma unitSquareScale_continuous : Continuous unitSquareScale :=
  continuous_const.div (continuous_const.mul (complexSquareGauge_continuous.comp unitAngle_continuous))
    (fun t => (mul_pos (by norm_num) (complexSquareGauge_pos (unitAngle_ne_zero t))).ne')

lemma unitSquareEnd_continuous : Continuous unitSquareEnd :=
  unitSquareScale_continuous.smul (complexFold_continuous.comp unitAngle_continuous)

lemma unitSquareScale_periodic : Function.Periodic unitSquareScale 1 := by
  intro t
  simp only [unitSquareScale,unitAngle_periodic t]

lemma unitSquareEnd_periodic : Function.Periodic unitSquareEnd 1 := by
  intro t
  simp only [unitSquareEnd,unitSquareScale_periodic t,unitAngle_periodic t]

lemma complexFold_smul {r : ℝ} (hr : 0≤r) (z : ℂ) : complexFold (r • z)=r • complexFold z := by
  apply Complex.ext <;> simp [complexFold,abs_mul,abs_of_nonneg hr]

lemma complexSquareGauge_smul {r : ℝ} (hr : 0≤r) (z : ℂ) :
    complexSquareGauge (r • z)=r*complexSquareGauge z := by
  simp only [complexSquareGauge,Complex.smul_re,Complex.smul_im,smul_eq_mul,abs_mul,abs_of_nonneg hr]
  exact (mul_max_of_nonneg _ _ hr).symm

lemma unitSquareEnd_gauge (t : ℝ) : complexSquareGauge (unitSquareEnd t)=1/2 := by
  rw [unitSquareEnd,complexSquareGauge_smul (unitSquareScale_pos t).le]
  have he : complexSquareGauge (complexFold (unitAngle t))=complexSquareGauge (unitAngle t) := by
    simp [complexFold,complexSquareGauge]
  rw [he,unitSquareScale]
  field_simp [(complexSquareGauge_pos (unitAngle_ne_zero t)).ne']

lemma unitSquareEnd_coordinates (t : ℝ) :
    0≤(unitSquareEnd t).re ∧ 0≤(unitSquareEnd t).im ∧
      (unitSquareEnd t).re≤1/2 ∧ (unitSquareEnd t).im≤1/2 ∧
      ((unitSquareEnd t).re=1/2 ∨ (unitSquareEnd t).im=1/2) := by
  have h0 : 0≤(unitSquareEnd t).re := by
    simp only [unitSquareEnd,Complex.smul_re,smul_eq_mul,complexFold]
    exact mul_nonneg (unitSquareScale_pos t).le (abs_nonneg _)
  have h1 : 0≤(unitSquareEnd t).im := by
    simp only [unitSquareEnd,Complex.smul_im,smul_eq_mul,complexFold]
    exact mul_nonneg (unitSquareScale_pos t).le (abs_nonneg _)
  have hg := unitSquareEnd_gauge t
  rw [complexSquareGauge,abs_of_nonneg h0,abs_of_nonneg h1] at hg
  refine ⟨h0,h1,?_,?_,?_⟩
  · exact (le_max_left _ _).trans_eq hg
  · exact (le_max_right _ _).trans_eq hg
  · rcases le_total (unitSquareEnd t).re (unitSquareEnd t).im with h|h
    · exact Or.inr (by rwa [max_eq_right h] at hg)
    · exact Or.inl (by rwa [max_eq_left h] at hg)

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set
open scoped ENNReal

namespace CubicTorus

end CubicTorus
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Interval
namespace CubicTorus

lemma integral_square_le_mass {X : Type*} [MeasurableSpace X]
    {μ : Measure X} [IsFiniteMeasure μ] {f : X → ℝ}
    (hf : Integrable f μ) (hfsq : Integrable (fun x ↦ f x ^ 2) μ) :
    (∫ x, f x ∂μ) ^ 2 ≤ μ.real univ * ∫ x, f x ^ 2 ∂μ := by
  let m := μ.real univ
  let q := ∫ x, f x ∂μ
  have hm : 0 ≤ m := measureReal_nonneg
  by_cases hm0 : m = 0
  · have hμ0 : μ = 0 := by
      apply Measure.measure_univ_eq_zero.mp
      exact (ENNReal.toReal_eq_zero_iff _).mp hm0 |>.resolve_right (measure_ne_top μ univ)
    simp [hμ0]
  have hmpos : 0 < m := lt_of_le_of_ne hm (Ne.symm hm0)
  have hi : Integrable (fun x ↦ f x ^ 2 - (2 * (q / m)) * f x) μ :=
    hfsq.sub (hf.const_mul _)
  have hp : 0 ≤ ∫ x, f x ^ 2 - (2 * (q / m)) * f x + (q / m) ^ 2 ∂μ := by
    apply integral_nonneg
    intro x
    change 0 ≤ f x ^ 2 - 2 * (q / m) * f x + (q / m) ^ 2
    nlinarith [sq_nonneg (f x - q / m)]
  rw [integral_add hi (integrable_const ((q / m) ^ 2)),
    integral_sub hfsq (hf.const_mul (2 * (q / m))), integral_const_mul, integral_const,
    smul_eq_mul] at hp
  change 0 ≤ (∫ x, f x ^ 2 ∂μ) - 2 * (q / m) * q + m * (q / m) ^ 2 at hp
  have heq : (∫ x, f x ^ 2 ∂μ) - 2 * (q / m) * q + m * (q / m) ^ 2 =
      (∫ x, f x ^ 2 ∂μ) - q ^ 2 / m := by field_simp; ring
  rw [heq] at hp
  exact (div_le_iff₀ hmpos).mp (by linarith : q ^ 2 / m ≤ ∫ x, f x ^ 2 ∂μ) |>.trans_eq (mul_comm _ _)

lemma lipschitz_deriv_sq_integrableOn {f : ℝ → ℝ} {K : ℝ≥0}
    (hf : LipschitzWith K f) (a b : ℝ) :
    IntegrableOn (fun x ↦ deriv f x ^ 2) (Icc a b) := by
  apply (integrable_const ((K : ℝ) ^ 2)).mono'
  · exact (aestronglyMeasurable_deriv f (volume.restrict (Icc a b))).pow 2
  · exact ae_of_all _ fun x ↦ by
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      have h := norm_deriv_le_of_lipschitz hf (x₀ := x)
      rw [Real.norm_eq_abs] at h
      nlinarith [sq_abs (deriv f x), abs_nonneg (deriv f x), NNReal.coe_nonneg K]

lemma lipschitz_sq_sub_le_interval_energy {f : ℝ → ℝ} {K : ℝ≥0}
    (hf : LipschitzWith K f) {a b : ℝ} (hab : a ≤ b) :
    (f b - f a) ^ 2 ≤ (b - a) * ∫ x in Icc a b, deriv f x ^ 2 := by
  have hAC := hf.lipschitzOnWith.absolutelyContinuousOnInterval (a := a) (b := b)
  have hid : IntegrableOn (deriv f) (Icc a b) := by
    rw [integrableOn_Icc_iff_integrableOn_Ioc]
    exact hAC.intervalIntegrable_deriv.1
  have hcs := integral_square_le_mass hid (lipschitz_deriv_sq_integrableOn hf a b)
  have hFTC : (∫ x in Icc a b, deriv f x) = f b - f a := by
    rw [integral_Icc_eq_integral_Ioc]
    rw [← intervalIntegral.integral_of_le hab]
    exact hAC.integral_deriv_eq_sub
  simpa only [hFTC, Measure.restrict_apply_univ, measureReal_def,
    Real.volume_Icc, ENNReal.toReal_ofReal (sub_nonneg.mpr hab)] using hcs

lemma integrable_square_sub_const {X : Type*} [MeasurableSpace X]
    {μ : Measure X} [IsFiniteMeasure μ] {f : X → ℝ}
    (hf : Integrable f μ) (hfsq : Integrable (fun x ↦ f x ^ 2) μ) (c : ℝ) :
    Integrable (fun x ↦ (c - f x) ^ 2) μ := by
  have h : (fun x ↦ (c - f x) ^ 2) =
      (fun x ↦ c ^ 2 - (2 * c) * f x + f x ^ 2) := by funext x; ring
  rw [h]
  exact ((integrable_const _).sub (hf.const_mul _)).add hfsq

lemma square_sub_average_le {X : Type*} [MeasurableSpace X]
    {μ : Measure X} [IsFiniteMeasure μ] {f : X → ℝ}
    (hm : 0 < μ.real univ) (hf : Integrable f μ)
    (hfsq : Integrable (fun x ↦ f x ^ 2) μ) (c : ℝ) :
    (c - (∫ x, f x ∂μ) / μ.real univ) ^ 2 ≤
      (∫ x, (c - f x) ^ 2 ∂μ) / μ.real univ := by
  have hcs := integral_square_le_mass hf hfsq
  have hi : Integrable (fun x ↦ c ^ 2 - (2 * c) * f x) μ :=
    (integrable_const _).sub (hf.const_mul _)
  have he : (∫ x, (c - f x) ^ 2 ∂μ) =
      μ.real univ * c ^ 2 - (2 * c) * (∫ x, f x ∂μ) + ∫ x, f x ^ 2 ∂μ := by
    calc
      _ = ∫ x, c ^ 2 - (2 * c) * f x + f x ^ 2 ∂μ := integral_congr_ae (ae_of_all _ fun x ↦ by ring)
      _ = _ := by
        rw [integral_add hi hfsq, integral_sub (integrable_const (c ^ 2)) (hf.const_mul (2 * c)),
          integral_const, integral_const_mul, smul_eq_mul]
  rw [he]
  have halg : (μ.real univ * c ^ 2 - (2 * c) * (∫ x, f x ∂μ) + ∫ x, f x ^ 2 ∂μ) /
      μ.real univ - (c - (∫ x, f x ∂μ) / μ.real univ) ^ 2 =
      (μ.real univ * (∫ x, f x ^ 2 ∂μ) - (∫ x, f x ∂μ) ^ 2) / (μ.real univ) ^ 2 := by
    field_simp
    ring
  have hnonneg : 0 ≤ (μ.real univ * (∫ x, f x ^ 2 ∂μ) - (∫ x, f x ∂μ) ^ 2) /
      (μ.real univ) ^ 2 := div_nonneg (sub_nonneg.mpr hcs) (sq_nonneg _)
  linarith

lemma lipschitz_sq_sub_le_common_interval_energy {f : ℝ → ℝ} {K : ℝ≥0}
    (hf : LipschitzWith K f) {a b u v : ℝ} (hu : u ∈ Icc a b) (hv : v ∈ Icc a b) :
    (f u - f v) ^ 2 ≤ (b - a) * ∫ x in Icc a b, deriv f x ^ 2 := by
  have hab : a ≤ b := hu.1.trans hu.2
  have he (u v : ℝ) (hu : u ∈ Icc a b) (hv : v ∈ Icc a b) (huv : u ≤ v) :
      (f v - f u) ^ 2 ≤ (b - a) * ∫ x in Icc a b, deriv f x ^ 2 := by
    apply (lipschitz_sq_sub_le_interval_energy hf huv).trans
    apply mul_le_mul (by linarith [hu.1, hv.2] : v - u ≤ b - a)
      (setIntegral_mono_set (lipschitz_deriv_sq_integrableOn hf a b)
        (ae_of_all _ fun x ↦ sq_nonneg (deriv f x)) (ae_of_all _ fun _ hx ↦ Icc_subset_Icc hu.1 hv.2 hx))
      (integral_nonneg fun x ↦ sq_nonneg _) (sub_nonneg.mpr hab)
  rcases le_total u v with huv | hvu
  · simpa only [show (f v - f u) ^ 2 = (f u - f v) ^ 2 by ring] using he u v hu hv huv
  · exact he v u hv hu hvu

lemma lipschitz_interval_poincare {f : ℝ → ℝ} {K : ℝ≥0}
    (hf : LipschitzWith K f) {a b : ℝ} (hab : a < b) :
    (∫ x in Icc a b, (f x - (∫ y in Icc a b, f y) / (b - a)) ^ 2) ≤
      (b - a) ^ 2 * ∫ x in Icc a b, deriv f x ^ 2 := by
  have hmass : (volume.restrict (Icc a b)).real univ = b - a := by
    simp [measureReal_def, Real.volume_Icc, hab.le]
  have hi : IntegrableOn f (Icc a b) := hf.continuous.continuousOn.integrableOn_Icc
  have hi₂ : IntegrableOn (fun x ↦ f x ^ 2) (Icc a b) :=
    (hf.continuous.pow 2).continuousOn.integrableOn_Icc
  have hpoint (x : ℝ) (hx : x ∈ Icc a b) :
      (f x - (∫ y in Icc a b, f y) / (b - a)) ^ 2 ≤
        (b - a) * ∫ y in Icc a b, deriv f y ^ 2 := by
    have hj := square_sub_average_le (by rw [hmass]; linarith) hi hi₂ (f x)
    rw [hmass] at hj
    apply hj.trans
    apply (div_le_iff₀ (sub_pos.mpr hab)).mpr
    calc
      _ ≤ ∫ _y in Icc a b, (b - a) * ∫ z in Icc a b, deriv f z ^ 2 := by
        apply setIntegral_mono_on (integrable_square_sub_const hi hi₂ _) (integrable_const _)
          measurableSet_Icc
        intro y hy
        exact lipschitz_sq_sub_le_common_interval_energy hf hx hy
      _ = _ := by rw [integral_const, smul_eq_mul, hmass]; ring
  calc
    _ ≤ ∫ _x in Icc a b, (b - a) * ∫ y in Icc a b, deriv f y ^ 2 := by
      apply setIntegral_mono_on
        (((hf.continuous.sub continuous_const).pow 2).continuousOn.integrableOn_Icc)
        (integrable_const _) measurableSet_Icc hpoint
    _ = _ := by rw [integral_const, smul_eq_mul, hmass]; ring

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology
namespace CubicTorus

lemma variance_le_separated_pairwise {X : Type*} [MeasurableSpace X]
    {μ : Measure X} [IsFiniteMeasure μ] {f A B : X → ℝ}
    (hm : 0 < μ.real univ) (hf : Integrable f μ)
    (hfsq : Integrable (fun x ↦ f x ^ 2) μ) (hA : Integrable A μ) (hB : Integrable B μ)
    (hpair : ∀ᵐ x ∂μ, ∀ᵐ y ∂μ, (f x - f y) ^ 2 ≤ A x + B y) :
    (∫ x, (f x - (∫ y, f y ∂μ) / μ.real univ) ^ 2 ∂μ) ≤
      (∫ x, A x ∂μ) + ∫ y, B y ∂μ := by
  let m := (∫ y, f y ∂μ) / μ.real univ
  have hpoint : ∀ᵐ x ∂μ, (f x - m) ^ 2 ≤ A x + (∫ y, B y ∂μ) / μ.real univ := by
    filter_upwards [hpair] with x hx
    have hj := square_sub_average_le hm hf hfsq (f x)
    apply hj.trans
    apply (div_le_iff₀ hm).mpr
    calc
      _ ≤ ∫ y, A x + B y ∂μ :=
        integral_mono_ae (integrable_square_sub_const hf hfsq _) ((integrable_const _).add hB) hx
      _ = (A x + (∫ y, B y ∂μ) / μ.real univ) * μ.real univ := by
        rw [integral_add (integrable_const _) hB, integral_const, smul_eq_mul]
        field_simp
  have hisq : Integrable (fun x ↦ (f x - m) ^ 2) μ := by
    convert integrable_square_sub_const hf hfsq m using 1
    funext x
    ring
  have hh := integral_mono_ae hisq
    (hA.add (integrable_const ((∫ y, B y ∂μ) / μ.real univ))) hpoint
  change (∫ x, (f x - m) ^ 2 ∂μ) ≤ ∫ x, A x + (∫ y, B y ∂μ) / μ.real univ ∂μ at hh
  rw [integral_add hA (integrable_const _), integral_const, smul_eq_mul,
    mul_div_cancel₀ _ (ne_of_gt hm)] at hh
  exact hh

lemma lipschitz_product_partial_measurable {f : ℝ × ℝ → ℝ} {K : ℝ≥0}
    (hf : LipschitzWith K f) :
    Measurable (fun p : ℝ × ℝ ↦ deriv (fun x ↦ f (x, p.2)) p.1) ∧
      Measurable (fun p : ℝ × ℝ ↦ deriv (fun y ↦ f (p.1, y)) p.2) := by
  constructor
  · exact (measurable_deriv_with_param (f := fun y x ↦ f (x, y))
      (hf.continuous.comp continuous_swap)).comp measurable_swap
  · exact measurable_deriv_with_param (f := fun x y ↦ f (x, y)) hf.continuous

lemma lipschitz_product_partial_integrable {f : ℝ × ℝ → ℝ} {K : ℝ≥0}
    (hf : LipschitzWith K f) (a b : ℝ) :
    Integrable (fun p : ℝ × ℝ ↦ deriv (fun x ↦ f (x, p.2)) p.1 ^ 2)
      ((volume.restrict (Icc a b)).prod (volume.restrict (Icc a b))) ∧
    Integrable (fun p : ℝ × ℝ ↦ deriv (fun y ↦ f (p.1, y)) p.2 ^ 2)
      ((volume.restrict (Icc a b)).prod (volume.restrict (Icc a b))) := by
  have hm := lipschitz_product_partial_measurable hf
  constructor
  · apply (integrable_const ((K : ℝ) ^ 2)).mono' (hm.1.pow_const 2).aestronglyMeasurable
    exact ae_of_all _ fun p ↦ by
      have hl : LipschitzWith K (fun x ↦ f (x, p.2)) := by simpa only [Function.comp_def, mul_one] using hf.comp (LipschitzWith.prodMk_right p.2)
      have hb := norm_deriv_le_of_lipschitz hl (x₀ := p.1)
      rw [Real.norm_eq_abs] at hb ⊢
      rw [abs_of_nonneg (sq_nonneg _)]
      nlinarith [sq_abs (deriv (fun x ↦ f (x, p.2)) p.1), NNReal.coe_nonneg K, abs_nonneg (deriv (fun x ↦ f (x, p.2)) p.1)]
  · apply (integrable_const ((K : ℝ) ^ 2)).mono' (hm.2.pow_const 2).aestronglyMeasurable
    exact ae_of_all _ fun p ↦ by
      have hl : LipschitzWith K (fun y ↦ f (p.1, y)) := by simpa only [Function.comp_def, mul_one] using hf.comp (LipschitzWith.prodMk_left p.1)
      have hb := norm_deriv_le_of_lipschitz hl (x₀ := p.2)
      rw [Real.norm_eq_abs] at hb ⊢
      rw [abs_of_nonneg (sq_nonneg _)]
      nlinarith [sq_abs (deriv (fun y ↦ f (p.1, y)) p.2), NNReal.coe_nonneg K, abs_nonneg (deriv (fun y ↦ f (p.1, y)) p.2)]

theorem lipschitz_box_poincare {f : ℝ × ℝ → ℝ} {K : ℝ≥0}
    (hf : LipschitzWith K f) {a b : ℝ} (hab : a < b) :
    let μ := (volume.restrict (Icc a b)).prod (volume.restrict (Icc a b))
    (∫ p, (f p - (∫ q, f q ∂μ) / (b - a) ^ 2) ^ 2 ∂μ) ≤
      2 * (b - a) ^ 2 *
        ((∫ p, deriv (fun x ↦ f (x, p.2)) p.1 ^ 2 ∂μ) +
          ∫ p, deriv (fun y ↦ f (p.1, y)) p.2 ^ 2 ∂μ) := by
  dsimp only
  let ν : Measure ℝ := volume.restrict (Icc a b)
  let μ := ν.prod ν
  let Ex : ℝ → ℝ := fun y ↦ ∫ x, deriv (fun t ↦ f (t, y)) x ^ 2 ∂ν
  let Ey : ℝ → ℝ := fun x ↦ ∫ y, deriv (fun t ↦ f (x, t)) y ^ 2 ∂ν
  have hν : ν.real univ = b - a := by simp [ν, measureReal_def, Real.volume_Icc, hab.le]
  have hμ : μ.real univ = (b - a) ^ 2 := by
    change ((ν.prod ν) univ).toReal = _
    rw [← Set.univ_prod_univ, Measure.prod_prod, ENNReal.toReal_mul]
    change ν.real univ * ν.real univ = _
    rw [hν]
    ring
  have hi : Integrable f μ := by
    rw [show μ = volume.restrict (Icc a b ×ˢ Icc a b) from by
      simp only [μ, ν, Measure.prod_restrict, ← Measure.volume_eq_prod]]
    exact ContinuousOn.integrableOn_compact (isCompact_Icc.prod isCompact_Icc) hf.continuous.continuousOn
  have hisq : Integrable (fun p ↦ f p ^ 2) μ := by
    rw [show μ = volume.restrict (Icc a b ×ˢ Icc a b) from by
      simp only [μ, ν, Measure.prod_restrict, ← Measure.volume_eq_prod]]
    exact ContinuousOn.integrableOn_compact (isCompact_Icc.prod isCompact_Icc) (hf.continuous.pow 2).continuousOn
  have hip := lipschitz_product_partial_integrable hf a b
  have hiEx : Integrable Ex ν := hip.1.integral_prod_right
  have hiEy : Integrable Ey ν := hip.2.integral_prod_left
  have hmem : ∀ᵐ p ∂μ, p.1 ∈ Icc a b ∧ p.2 ∈ Icc a b := by
    rw [show μ = volume.restrict (Icc a b ×ˢ Icc a b) from by
      simp only [μ, ν, Measure.prod_restrict, ← Measure.volume_eq_prod]]
    exact ae_restrict_mem (measurableSet_Icc.prod measurableSet_Icc)
  have hpair : ∀ᵐ p ∂μ, ∀ᵐ q ∂μ,
      (f p - f q) ^ 2 ≤ 2 * (b - a) * Ex p.2 + 2 * (b - a) * Ey q.1 := by
    filter_upwards [hmem] with p hp
    filter_upwards [hmem] with q hq
    have hx : (f p - f (q.1, p.2)) ^ 2 ≤ (b - a) * Ex p.2 :=
      lipschitz_sq_sub_le_common_interval_energy (by
        simpa using hf.comp (LipschitzWith.prodMk_right p.2)) hp.1 hq.1
    have hy : (f (q.1, p.2) - f q) ^ 2 ≤ (b - a) * Ey q.1 :=
      lipschitz_sq_sub_le_common_interval_energy (by
        simpa using hf.comp (LipschitzWith.prodMk_left q.1)) hp.2 hq.2
    nlinarith [sq_nonneg (f p - 2 * f (q.1, p.2) + f q)]
  have hh := variance_le_separated_pairwise (μ := μ) (by rw [hμ]; positivity) hi hisq
    ((hiEx.comp_snd ν).const_mul (2 * (b - a)))
    ((hiEy.comp_fst ν).const_mul (2 * (b - a))) hpair
  rw [hμ] at hh
  have hex : (∫ p, Ex p.2 ∂μ) = (b - a) * ∫ y, Ex y ∂ν := by
    rw [integral_prod _ (hiEx.comp_snd ν)]
    simp only [integral_const, smul_eq_mul, hν]
  have hey : (∫ p, Ey p.1 ∂μ) = (b - a) * ∫ x, Ey x ∂ν := by
    rw [integral_prod _ (hiEy.comp_fst ν)]
    simp only [integral_const, smul_eq_mul, hν, integral_const_mul]
  have hEx : (∫ y, Ex y ∂ν) = ∫ p, deriv (fun x ↦ f (x, p.2)) p.1 ^ 2 ∂μ :=
    (integral_prod_symm _ hip.1).symm
  have hEy : (∫ x, Ey x ∂ν) = ∫ p, deriv (fun y ↦ f (p.1, y)) p.2 ^ 2 ∂μ :=
    (integral_prod _ hip.2).symm
  rw [integral_const_mul, integral_const_mul, hex, hey, hEx, hEy] at hh
  convert hh using 1
  ring

lemma differentiableAt_partial_sq_le {f : ℝ × ℝ → ℝ} {p : ℝ × ℝ}
    (hf : DifferentiableAt ℝ f p) :
    deriv (fun x ↦ f (x, p.2)) p.1 ^ 2 + deriv (fun y ↦ f (p.1, y)) p.2 ^ 2 ≤
      2 * ‖fderiv ℝ f p‖ ^ 2 := by
  have hx : deriv (fun x ↦ f (x, p.2)) p.1 = fderiv ℝ f p (1, 0) := by
    exact (hf.hasFDerivAt.comp_hasDerivAt p.1
      ((hasDerivAt_id p.1).prodMk (hasDerivAt_const p.1 p.2))).deriv
  have hy : deriv (fun y ↦ f (p.1, y)) p.2 = fderiv ℝ f p (0, 1) := by
    exact (hf.hasFDerivAt.comp_hasDerivAt p.2
      ((hasDerivAt_const p.2 p.1).prodMk (hasDerivAt_id p.2))).deriv
  rw [hx, hy]
  have hb₁ : |fderiv ℝ f p (1, 0)| ≤ ‖fderiv ℝ f p‖ := by
    simpa [Prod.norm_def] using (fderiv ℝ f p).le_opNorm (1, 0)
  have hb₂ : |fderiv ℝ f p (0, 1)| ≤ ‖fderiv ℝ f p‖ := by
    simpa [Prod.norm_def] using (fderiv ℝ f p).le_opNorm (0, 1)
  nlinarith [sq_abs (fderiv ℝ f p (1, 0)), sq_abs (fderiv ℝ f p (0, 1)),
    abs_nonneg (fderiv ℝ f p (1, 0)), abs_nonneg (fderiv ℝ f p (0, 1))]

lemma lipschitz_fderiv_sq_integrable {X : Type*} [NormedAddCommGroup X]
    [NormedSpace ℝ X] [MeasurableSpace X] [OpensMeasurableSpace X]
    {μ : Measure X} [IsFiniteMeasure μ] {f : X → ℝ} {K : ℝ≥0}
    (hf : LipschitzWith K f) : Integrable (fun x ↦ ‖fderiv ℝ f x‖ ^ 2) μ := by
  apply (integrable_const ((K : ℝ) ^ 2)).mono'
    ((measurable_fderiv ℝ f).norm.pow_const 2).aestronglyMeasurable
  exact ae_of_all _ fun x ↦ by
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    have hh := norm_fderiv_le_of_lipschitz ℝ hf (x₀ := x)
    nlinarith [norm_nonneg (fderiv ℝ f x), NNReal.coe_nonneg K]

theorem lipschitz_box_poincare_fderiv {f : ℝ × ℝ → ℝ} {K : ℝ≥0}
    (hf : LipschitzWith K f) {a b : ℝ} (hab : a < b) :
    let μ := (volume.restrict (Icc a b)).prod (volume.restrict (Icc a b))
    (∫ p, (f p - (∫ q, f q ∂μ) / (b - a) ^ 2) ^ 2 ∂μ) ≤
      4 * (b - a) ^ 2 * (∫ p, ‖fderiv ℝ f p‖ ^ 2 ∂μ) := by
  dsimp only
  let μ := (volume.restrict (Icc a b)).prod (volume.restrict (Icc a b))
  have hdiff : ∀ᵐ p ∂μ, DifferentiableAt ℝ f p := by
    rw [show μ = volume.restrict (Icc a b ×ˢ Icc a b) from by
      simp only [μ, Measure.prod_restrict, ← Measure.volume_eq_prod]]
    exact ae_restrict_of_ae hf.ae_differentiableAt
  have hip := lipschitz_product_partial_integrable hf a b
  have hb := integral_mono_ae (hip.1.add hip.2)
    ((lipschitz_fderiv_sq_integrable (μ := μ) hf).const_mul 2)
    (hdiff.mono fun _ h ↦ differentiableAt_partial_sq_le h)
  change (∫ p, deriv (fun x ↦ f (x, p.2)) p.1 ^ 2 +
    deriv (fun y ↦ f (p.1, y)) p.2 ^ 2 ∂μ) ≤ ∫ p, 2 * ‖fderiv ℝ f p‖ ^ 2 ∂μ at hb
  rw [integral_add hip.1 hip.2, integral_const_mul] at hb
  apply (lipschitz_box_poincare hf hab).trans
  have hh := mul_le_mul_of_nonneg_left hb (by positivity : 0 ≤ 2 * (b - a) ^ 2)
  convert hh using 1
  ring

end CubicTorus

end
end

end

end OAI
