import OAI.NumberTheory.DirichletL.Inversion.InitialDetectorSource
import OAI.NumberTheory.DirichletL.Descent.ClippedEnergy

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap FourierTransform ContDiff
open MeasureTheory
namespace SevenEighths.DetectorDictionaryInverseRawFourier
open HeckeFamily HeckeDyadic HeckeDetectorDyadicBridge InverseInitialRawDictionary
open InverseMoment InverseInitialClippedColumns InverseInitialOverlapFourier FourierBridge JointLogSeparation

private theorem child_cover (Wref : ℝ→ℂ) (b D : ℝ) (hD : 0<D)
    (hWref : ∀x,Wref x≠0 → x≤b) (s : ℝ) :
    ∀I : Ideal O,I≠0 → childLogTest Wref s ((I.absNorm:ℝ)/D)≠0 →
      I∈ConcretePrimeRowBridge.idealsUpTo ⌈D*b⌉₊ := by
  intro I hI hi
  apply finite_source_cover Wref D b hD hWref I hI
  intro hz
  exact hi (by simp [childLogTest,hz])

theorem polynomial_mode_integrable (χ : Character) (inv : Bool)
    (g : 𝓢(ℝ,ℂ)) (Wref : ℝ→ℂ) (b c θ D : ℝ) (hD : 0<D)
    (hWref : ∀x,Wref x≠0 → x≤b) :
    Integrable (fun v:ℝ=>density g (Real.log c) v*
      polynomial χ inv (childLogTest Wref (θ+v)) D 0 0) := by
  simp_rw [polynomial_eq_finite χ inv (childLogTest Wref (θ+_)) D 0 0
    (ConcretePrimeRowBridge.idealsUpTo ⌈D*b⌉₊) (child_cover Wref b D hD hWref _)]
  simp only [HeckeDyadic.shift,Complex.ofReal_zero,zero_mul,sub_zero,
    neg_zero,Complex.cpow_zero,mul_one,Finset.mul_sum]
  apply integrable_finsetSum
  intro I hI
  convert fourier_phase_integrable g
    (Real.log c+Real.log ((I.absNorm:ℝ)/D))
    ((D:ℂ)^(-(1/2:ℂ))*coefficient χ inv I*Wref ((I.absNorm:ℝ)/D)*
      logPhase θ (Real.log ((I.absNorm:ℝ)/D))) using 1
  funext v
  simp only [density,childLogTest,logPhase_add_frequency,logPhase_add]
  ring

theorem polynomial_clipped_fourier (χ : Character) (inv : Bool)
    (W : ℝ→ℂ) (lo hi : ℝ) (hlo : 0<lo)
    (hs : Function.support W⊆Set.Icc lo hi) (hW : ContDiff ℝ ∞ W)
    (Wref : ℝ→ℂ) (b c θ D : ℝ) (hc : 0<c) (hD : 0<D)
    (hWref : ∀x,Wref x≠0 → x≤b)
    (hagree : ∀y,0<y → Wref y*W (c*y)=W (c*y)) :
    polynomial χ inv (clippedTest W c θ) D 0 0=
      ∫v:ℝ,density (CubicReflectionKernel.logSchwartz W lo hi hlo hs hW) (Real.log c) v*
        polynomial χ inv (childLogTest Wref (θ+v)) D 0 0 := by
  let S:=ConcretePrimeRowBridge.idealsUpTo ⌈D*b⌉₊
  have hcover : ∀I : Ideal O,I≠0 → clippedTest W c θ ((I.absNorm:ℝ)/D)≠0 → I∈S := by
    intro I hI hi
    have hIp : 0<(I.absNorm:ℝ)/D:=div_pos (by exact_mod_cast (Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hI))) hD
    apply finite_source_cover Wref D b hD hWref I hI
    intro hz
    have he:=hagree _ hIp
    rw [hz,zero_mul] at he
    exact hi (by simp [clippedTest,childLogTest,←he])
  rw [polynomial_eq_finite χ inv (clippedTest W c θ) D 0 0 S hcover]
  simp_rw [polynomial_eq_finite χ inv (childLogTest Wref (θ+_)) D 0 0 S
    (child_cover Wref b D hD hWref _)]
  simp only [HeckeDyadic.shift,Complex.ofReal_zero,zero_mul,sub_zero,
    neg_zero,Complex.cpow_zero,mul_one,Finset.mul_sum]
  have hint (I : Ideal O) : Integrable (fun v:ℝ=>
      density (CubicReflectionKernel.logSchwartz W lo hi hlo hs hW) (Real.log c) v*
        ((D:ℂ)^(-(1/2:ℂ))*(coefficient χ inv I*childLogTest Wref (θ+v) ((I.absNorm:ℝ)/D)))) := by
    convert fourier_phase_integrable (CubicReflectionKernel.logSchwartz W lo hi hlo hs hW)
      (Real.log c+Real.log ((I.absNorm:ℝ)/D))
      ((D:ℂ)^(-(1/2:ℂ))*coefficient χ inv I*Wref ((I.absNorm:ℝ)/D)*
        logPhase θ (Real.log ((I.absNorm:ℝ)/D))) using 1
    funext v
    simp only [density,childLogTest,logPhase_add_frequency,logPhase_add]
    ring
  rw [integral_finsetSum _ (fun I _=>hint I)]
  apply Finset.sum_congr rfl
  intro I hI
  by_cases hz : I=0
  · subst I
    simp only [coefficient_zero,zero_mul,mul_zero,integral_zero]
  have hIp : 0<(I.absNorm:ℝ)/D:=div_pos (by exact_mod_cast (Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hz))) hD
  rw [clipped_test_fourier W lo hi hlo hs hW Wref c θ _ hc hIp (hagree _ hIp),
    ←integral_const_mul,←integral_const_mul]
  apply integral_congr_ae
  filter_upwards with v
  ring

end SevenEighths.DetectorDictionaryInverseRawFourier

end

end OAI
