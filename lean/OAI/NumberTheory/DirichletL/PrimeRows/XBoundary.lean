import OAI.NumberTheory.DirichletL.PrimeRows.XGrowth
import OAI.NumberTheory.DirichletL.PrimeRows.BufferedContour
import OAI.NumberTheory.DirichletL.ContinuationShiftedGaussian

namespace OAI

noncomputable section
open scoped Classical BigOperators
open MeasureTheory Set Complex
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical ProbeMellinBoundary
local notation "O" => HeckeFamily.O

def xRowScalar {K : ℕ} (P : Fin K→PrimeIdeal) (u : FreeRow)
    (W0 W1 : SchwartzMap ℝ ℂ) (X Y : ℝ) (w z : ℂ) : ℂ :=
  (X:ℂ)^(1/2-z)*(Y:ℂ)^(w-1)*
    mellin (EisensteinSchwartzPoisson.paperRadialFourier W0) z*mellin W1 w*
    (∏i,(elementNorm (CompletedGauss.primaryGenerator (P i).val):ℂ)^(z-1))*
    frequencyWeight z ⟨u.val,u.property.1⟩

lemma continuedPhysicalRowKernel_x_factor {K : ℕ}
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hmax : ∀P∈S,P.IsMaximal)
    (P : Fin K→PrimeIdeal) (hPS : ∀i,(P i).val∉S) (η : Character) (u : FreeRow)
    (W0 W1 : SchwartzMap ℝ ℂ) (X Y Z : ℝ) (x w z : ℂ) :
    continuedPhysicalRowKernel S hS hmax P hPS η u W0 W1 X Y Z x w z=
      xRowScalar P u W0 W1 X Y w z*(Z:ℂ)^(x+z-1)*Complex.exp ((x+z-1)^2)*
        (star ((calibrationForSet S hmax).residueMonoid u.val)*
          physicalCompensatedRow S hS (Finset.univ.image P) (contourTupleOutside S P hPS) η u x w z) := by
  unfold continuedPhysicalRowKernel xRowScalar sourceMellinWeight
  ring

lemma coupled_gaussian_bound (z : ℂ) {l r v : ℝ} (hl : 0<l) (hv : v∈Icc l r) (t : ℝ) :
    ‖Complex.exp ((((v:ℂ)+t*I)+z-1)^2)‖≤
      Real.exp ((|z.re|+r+1)^2)*Real.exp (-((t+z.im)^2)) := by
  rw [Complex.norm_exp,←Real.exp_add]
  apply Real.exp_le_exp.mpr
  have hre : ((((v:ℂ)+t*I)+z-1)^2).re=(v+z.re-1)^2-(t+z.im)^2 := by simp [pow_two]
  rw [hre]
  have hvp : 0<v := hl.trans_le hv.1
  have hA : |v+z.re-1|≤|z.re|+r+1 := by
    rw [abs_le]
    constructor <;> linarith [neg_abs_le z.re,le_abs_self z.re,hv.2]
  have hh := pow_le_pow_left₀ (abs_nonneg (v+z.re-1)) hA 2
  rw [sq_abs] at hh
  linarith

theorem continuedPhysicalRowKernel_x_gaussian {K : ℕ}
    (e eps : ℝ) (he : 0<e) (he' : e<1/1000)
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hfirst : FirstTail eps S)
    (hmax : ∀P∈S,P.IsMaximal) (P : Fin K→PrimeIdeal) (hPS : ∀i,(P i).val∉S)
    (η : Character) (u : FreeRow) (W0 W1 : SchwartzMap ℝ ℂ)
    (X Y Z : ℝ) (hZ : 0<Z) (w z : ℂ) (l r : ℝ)
    (hl : (51/100:ℝ)≤l) (hlβ : HeckeZeroSupremum.beta+8*e≤l)
    (hw : -(1/100:ℝ)≤w.re) (hz : (17/50:ℝ)≤z.re)
    (hlw : 1+eps≤l+w.re) :
    ∃B : ℝ,0≤B ∧ ∀v∈Icc l r,∀t : ℝ,
      ‖continuedPhysicalRowKernel S hS hmax P hPS η u W0 W1 X Y Z ((v:ℂ)+t*I) w z‖≤
        B*Continuation.polynomialGaussian 2 (t+z.im) := by
  obtain ⟨C,hC,hrow⟩ := physicalRow_first_x_growth e eps he he' S hS hfirst _
    (contourTupleOutside S P hPS) η u w z l r hl hlβ hw hz hlw
  let A := ‖xRowScalar P u W0 W1 X Y w z‖*scaleBound Z (l+z.re-1) (r+z.re-1)*
    Real.exp ((|z.re|+r+1)^2)*C
  have hA : 0≤A := by dsimp [A,scaleBound];positivity
  refine ⟨A*(2*(3+|z.im|)^2),by positivity,?_⟩
  intro v hv t
  have hZb := cpow_le_scaleBound hZ (((v:ℂ)+t*I)+z-1)
    (show (((v:ℂ)+t*I)+z-1).re∈Icc (l+z.re-1) (r+z.re-1) by
      simpa using And.intro (by linarith [hv.1] : l+z.re-1≤v+z.re-1)
        (by linarith [hv.2] : v+z.re-1≤r+z.re-1))
  have hgb := coupled_gaussian_bound z (by linarith : 0<l) hv t
  have hr : ‖star ((calibrationForSet S hmax).residueMonoid u.val)*
      physicalCompensatedRow S hS (Finset.univ.image P) (contourTupleOutside S P hPS) η u ((v:ℂ)+t*I) w z‖≤C*(3+|t|)^2 := by
    rw [norm_mul,norm_star]
    apply (mul_le_of_le_one_left (norm_nonneg _)
      ((calibrationForSet S hmax).residueMonoid_norm_le_one _)).trans
    simpa using hrow ((v:ℂ)+t*I) (by simpa using hv.1) (by simpa using hv.2)
  rw [continuedPhysicalRowKernel_x_factor,norm_mul,norm_mul,norm_mul]
  calc
    _ ≤ (‖xRowScalar P u W0 W1 X Y w z‖*scaleBound Z (l+z.re-1) (r+z.re-1))*
        (Real.exp ((|z.re|+r+1)^2)*Real.exp (-((t+z.im)^2)))*(C*(3+|t|)^2) :=
      mul_le_mul (mul_le_mul (mul_le_mul_of_nonneg_left hZb (norm_nonneg _)) hgb
        (norm_nonneg _) (mul_nonneg (norm_nonneg _) (scaleBound_pos _ _ _).le))
        hr (norm_nonneg _) (by unfold scaleBound;positivity)
    _ = A*(3+|t|)^2*Real.exp (-((t+z.im)^2)) := by dsimp [A];ring
    _ ≤ A*(2*(3+|z.im|)^2*(1+|t+z.im|^2))*Real.exp (-((t+z.im)^2)) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (Continuation.shifted_height_two t z.im) hA) (Real.exp_pos _).le
    _ = _ := by unfold Continuation.polynomialGaussian;ring

end SevenEighths.ProbeHighRowFamily

end

end OAI
