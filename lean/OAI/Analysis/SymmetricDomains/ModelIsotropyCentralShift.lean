import Mathlib
import OAI.Analysis.SymmetricDomains.EulerSpectrum
import OAI.Analysis.SymmetricDomains.Geometry2
import OAI.Analysis.SymmetricDomains.IsotropyCentralShiftZero

namespace OAI

noncomputable section

open Set Metric Complex
open scoped Topology
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped Topology ContDiff
open Filter
open scoped BigOperators Topology ContDiff
open Set Filter MeasureTheory
open scoped Topology
open Set Filter
open Set Metric
open scoped Topology
open Set Filter Metric
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter Metric
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open Set Filter Topology
open Filter Topology
open Filter Topology
open Filter Topology
open Filter Topology
open Polynomial
open Filter Topology
open scoped TensorProduct
open Set Filter Topology
open scoped TensorProduct
open scoped TensorProduct
open Filter Topology
open Filter Topology
open scoped TensorProduct
open Filter Topology
open scoped TensorProduct
open scoped TensorProduct
open scoped TensorProduct
open Filter Topology
open scoped TensorProduct
namespace Release061
open Set Filter Topology

theorem scalar_linear_ode {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (f : ℝ → E) (c : ℂ) (hd : ∀ t, HasDerivAt f (c • f t) t) (t : ℝ) :
    f t=Complex.exp ((t : ℂ)*c) • f 0 := by
  let s : ℝ → ℂ := fun t => Complex.exp (-((t : ℂ)*c))
  have hs (u : ℝ) : HasDerivAt s ((-c)*s u) u := by
    have hu : HasDerivAt (fun u : ℝ => (u : ℂ)) 1 u := by
      convert Complex.ofRealCLM.hasDerivAt using 1 <;> rfl
    convert ((hu.mul_const c).neg).cexp using 1
    simp [s,mul_comm]
  have hd0 (u : ℝ) : HasDerivAt (fun u => s u • f u) 0 u := by
    have hh := (hs u).smul (hd u)
    have he : s u • (c • f u)+(-c*s u) • f u=0 := by
      rw [smul_smul,neg_mul,neg_smul,←sub_eq_add_neg,mul_comm]
      exact sub_self _
    exact he ▸ hh
  have hconst := is_const_of_deriv_eq_zero (fun u => (hd0 u).differentiableAt)
    (fun u => (hd0 u).deriv) t 0
  have hz : s t • f t=f 0 := by simpa [s] using hconst
  have hh := congrArg (fun v => Complex.exp ((t : ℂ)*c) • v) hz
  simpa only [s,smul_smul,←Complex.exp_add,add_neg_cancel,Complex.exp_zero,one_smul] using hh

namespace Biholomorph

section
variable {n : ℕ} {U : Set (Affine n)} (hU : IsOpen U) [LocallyCompactSpace U]
    (hbd : Bornology.IsBounded U)
include hU hbd

theorem negative_isotropy_of_scalar_generator {X : Affine n → Affine n}
    (hX : IsCompleteGenerator U X) (p : U) (hp : X p.val=0)
    (hd : fderiv ℂ X p.val=(2*Complex.I) • (1 : Affine n →L[ℂ] Affine n)) :
    ∃ a : Biholomorph U U, a.toHomeomorph p=p ∧ a.derivativeAt p= -1 := by
  obtain ⟨a,ha,ha0,ham,rfl⟩ := hX
  have hfix := oneParameter_fixed_of_generator_zero hU a ha hbd ha0 ham p hp
  let A : ℝ → (Affine n →L[ℂ] Affine n) := fun t => (a t).derivativeAt p
  have hAd (t : ℝ) : HasDerivAt A ((2*Complex.I) • A t) t := by
    have he := oneParameter_derivativeAt_hasDerivAt hU hbd a ha ha0 ham t p
    rw [hfix,hd] at he
    change HasDerivAt A (((2*Complex.I) • (1 : Affine n →L[ℂ] Affine n))*A t) t at he
    have hj : ((2*Complex.I) • (1 : Affine n →L[ℂ] Affine n))*A t=(2*Complex.I) • A t := by
      ext v
      rfl
    rwa [hj] at he
  refine ⟨a (Real.pi/2),hfix _,?_⟩
  have he := scalar_linear_ode A (2*Complex.I) hAd (Real.pi/2)
  have hA0 : A 0=1 := by dsimp only [A]; rw [ha0,derivativeAt_one hU]
  rw [hA0] at he
  have hc : ((Real.pi/2 : ℝ) : ℂ)*(2*Complex.I)=(Real.pi : ℂ)*Complex.I := by
    push_cast
    ring
  rw [hc,Complex.exp_pi_mul_I,neg_one_smul] at he
  exact he

end

open Set
variable {n m : ℕ} {U : Set (Affine n)} {D : Set (Affine m)}
    (hU : IsOpen U) [LocallyCompactSpace U] (hc : IsConnected U) (hbd : Bornology.IsBounded U)
    (hD : IsOpen D) (e : Biholomorph U D)
    (Γ : Type*) [Group Γ] [TopologicalSpace Γ] [DiscreteTopology Γ]
    [MulAction Γ U] [ProperSMul Γ U] [CompactSpace (Quotient (MulAction.orbitRel Γ U))]
    (hhol : ∀ γ : Γ, HolomorphicOnSubset U (fun p => (γ • p : U).val))
include hU hc hbd hD Γ hhol

theorem model_isotropy_central_shift_zero {X Y : Affine n → Affine n}
    (hX : IsCompleteGenerator U X) (hY : IsCompleteGenerator U Y) (p : D) (c : ℝ)
    (hx : coordinateField e X p.val=0) (hy : coordinateField e Y p.val=0)
    (hrel : fderiv ℂ (coordinateField e Y) p.val=Complex.I •
      ((c : ℂ) • (1 : Affine m →L[ℂ] Affine m)-fderiv ℂ (coordinateField e X) p.val)) : X=0 := by
  have hx0 := (coordinateField_value_zero_iff hU hD e X p).mp hx
  have hy0 := (coordinateField_value_zero_iff hU hD e Y p).mp hy
  apply isotropy_central_shift_zero hU hc hbd Γ hhol hX hY (e.toHomeomorph.symm p) c hx0 hy0
  rw [coordinateField_fderiv_of_zero hU hD e (hX.analyticOnNhd hU hbd) p hx0,
    coordinateField_fderiv_of_zero hU hD e (hY.analyticOnNhd hU hbd) p hy0] at hrel
  let A := mapDerivativeEquiv hU hD e (e.toHomeomorph.symm p)
  let B := mapDerivativeEquiv hD hU e.symm p
  apply ContinuousLinearMap.ext
  intro v
  have hz := congrArg (fun L : Affine m →L[ℂ] Affine m => L (A v)) hrel
  have hBA : B (A v)=v := by
    have hh := congrArg (fun L : Affine n →L[ℂ] Affine n => L v)
      (mapDerivative_symm_comp hU hD e (e.toHomeomorph.symm p))
    simpa only [A,B,mapDerivativeEquiv_apply,e.toHomeomorph.apply_symm_apply,ContinuousLinearMap.comp_apply,ContinuousLinearMap.id_apply] using hh
  change A (fderiv ℂ Y (e.toHomeomorph.symm p).val (B (A v)))=
    Complex.I • ((c : ℂ) • (A v)-A (fderiv ℂ X (e.toHomeomorph.symm p).val (B (A v)))) at hz
  rw [hBA,←map_smul,←map_sub,←map_smul] at hz
  exact A.injective hz
end Biholomorph
end Release061

end

end OAI
