import OAI.NumberTheory.CubicMoment.Theta.CubicThetaPrimeFreeContinuation

namespace OAI

/-! Solve the two unramified local equations on the actual holomorphic
Fourier family. Together with PrimeFreeOne, these are the three literal
cubic twists of the prime-free rows. -/
noncomputable section
open Set Filter Topology
namespace CubicFirstMoment

def cubicThetaRegularizedPrimeFreeZero (p h : Eisenstein) (s : ℂ) : ℂ :=
  (cubicThetaRegularizedFrequency h s-
    cubicThetaPrimeFirstFactor p s h*cubicThetaRegularizedFrequency (p*h) s)/
      cubicThetaPrimeDeterminant p s

def cubicThetaRegularizedPrimeFreeTwo (p h : Eisenstein) (s : ℂ) : ℂ :=
  (cubicThetaRegularizedFrequency (p*h) s-
    cubicThetaPrimeSecondFactor p s h*cubicThetaRegularizedFrequency h s)/
      cubicThetaPrimeDeterminant p s

lemma cubicThetaPrimeSecondFactor_analytic {p : Eisenstein} (hp : primaryPrime p)
    (h : Eisenstein) (s : ℂ) : AnalyticAt ℂ (fun z => cubicThetaPrimeSecondFactor p z h) s :=
  analyticAt_const.mul ((cubicThetaPrimeNormPower_analytic hp s).pow 2)

theorem cubicThetaRegularizedPrimeFreeZero_analytic {p : Eisenstein}
    (hp : primaryPrime p) {h : Eisenstein} (hh : h≠0) :
    AnalyticOnNhd ℂ (cubicThetaRegularizedPrimeFreeZero p h) {s : ℂ | 1<s.re} := by
  intro s hs
  exact ((cubicThetaRegularizedFrequency_analytic hh s hs).sub
    ((cubicThetaPrimeFirstFactor_analytic hp h s).mul
      (cubicThetaRegularizedFrequency_analytic (mul_ne_zero hp.2.ne_zero hh) s hs))).div
        (cubicThetaPrimeDeterminant_analytic hp s) (cubicThetaPrimeDeterminant_ne_zero hp hs)

theorem cubicThetaRegularizedPrimeFreeTwo_analytic {p : Eisenstein}
    (hp : primaryPrime p) {h : Eisenstein} (hh : h≠0) :
    AnalyticOnNhd ℂ (cubicThetaRegularizedPrimeFreeTwo p h) {s : ℂ | 1<s.re} := by
  intro s hs
  exact ((cubicThetaRegularizedFrequency_analytic (mul_ne_zero hp.2.ne_zero hh) s hs).sub
    ((cubicThetaPrimeSecondFactor_analytic hp h s).mul
      (cubicThetaRegularizedFrequency_analytic hh s hs))).div
        (cubicThetaPrimeDeterminant_analytic hp s) (cubicThetaPrimeDeterminant_ne_zero hp hs)

theorem cubicThetaRegularizedPrimeFreeZero_right {p : Eisenstein}
    (hp : primaryPrime p) (h : Eisenstein) (hh : ¬p ∣ h) {s : ℂ} (hs : 3<s.re) :
    cubicThetaRegularizedPrimeFreeZero p h s=(s-4/3)*cubicThetaPrimeFreeDirichlet p s h 0 := by
  have hh0 : h≠0 := fun he => hh (he ▸ dvd_zero p)
  unfold cubicThetaRegularizedPrimeFreeZero
  rw [cubicThetaRegularizedFrequency_right hh0 hs,
    cubicThetaRegularizedFrequency_right (mul_ne_zero hp.2.ne_zero hh0) hs,
    cubicThetaFrequencyDirichlet_primeEulerStep hp (by linarith) h hh,
    cubicThetaFrequencyDirichlet_primeShift hp (by linarith) h hh]
  have hd := cubicThetaPrimeDeterminant_ne_zero hp (s:=s) (by linarith)
  apply (div_eq_iff hd).mpr
  have he := cubicThetaPrimeFactors_product hp s h hh
  unfold cubicThetaPrimeDeterminant
  linear_combination -(s-4/3)*cubicThetaPrimeFreeDirichlet p s h 0*he

theorem cubicThetaRegularizedPrimeFreeTwo_right {p : Eisenstein}
    (hp : primaryPrime p) (h : Eisenstein) (hh : ¬p ∣ h) {s : ℂ} (hs : 3<s.re) :
    cubicThetaRegularizedPrimeFreeTwo p h s=(s-4/3)*cubicThetaPrimeFreeDirichlet p s h 2 := by
  have hh0 : h≠0 := fun he => hh (he ▸ dvd_zero p)
  unfold cubicThetaRegularizedPrimeFreeTwo
  rw [cubicThetaRegularizedFrequency_right hh0 hs,
    cubicThetaRegularizedFrequency_right (mul_ne_zero hp.2.ne_zero hh0) hs,
    cubicThetaFrequencyDirichlet_primeEulerStep hp (by linarith) h hh,
    cubicThetaFrequencyDirichlet_primeShift hp (by linarith) h hh]
  have hd := cubicThetaPrimeDeterminant_ne_zero hp (s:=s) (by linarith)
  apply (div_eq_iff hd).mpr
  have he := cubicThetaPrimeFactors_product hp s h hh
  unfold cubicThetaPrimeDeterminant
  linear_combination -(s-4/3)*cubicThetaPrimeFreeDirichlet p s h 2*he

theorem cubicThetaRegularizedFrequency_primeFree_decomposition {p : Eisenstein}
    (hp : primaryPrime p) (h : Eisenstein) (hh : ¬p ∣ h) {s : ℂ} (hs : 1<s.re) :
    cubicThetaRegularizedFrequency h s=cubicThetaRegularizedPrimeFreeZero p h s+
      cubicThetaPrimeFirstFactor p s h*cubicThetaRegularizedPrimeFreeTwo p h s := by
  unfold cubicThetaRegularizedPrimeFreeZero cubicThetaRegularizedPrimeFreeTwo
  have hd := cubicThetaPrimeDeterminant_ne_zero hp hs
  have he := cubicThetaPrimeFactors_product hp s h hh
  rw [← mul_div_assoc,← add_div]
  apply (eq_div_iff hd).mpr
  unfold cubicThetaPrimeDeterminant
  linear_combination cubicThetaRegularizedFrequency h s*he

end CubicFirstMoment

end

end OAI
