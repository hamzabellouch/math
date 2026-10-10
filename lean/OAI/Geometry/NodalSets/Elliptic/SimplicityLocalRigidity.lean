import Mathlib.Analysis.Calculus.MeanValue
import OAI.Geometry.NodalSets.Elliptic.SimplicityCoordinateEnergy

namespace OAI

namespace Yau.Target
open Yau.Geometry Yau.Jets Set
open scoped ContDiff
noncomputable section

theorem round_simplicity_local_rigidity (u v zeta : Yau.Jets.Coord → ℝ)
    (hu : ContDiff ℝ ∞ u) (hv : ContDiff ℝ ∞ v) (hz : ContDiff ℝ ∞ zeta)
    (hc : HasCompactSupport zeta) (hzn : ∀ x, 0 ≤ zeta x) (lam : ℝ) (hlam : lam ≠ 0)
    (he : roundSimplicityEnergy u v zeta lam = 0)
    {U : Set Yau.Jets.Coord} (hU : IsOpen U) (hUc : IsPreconnected U)
    (hUz : ∀ x ∈ U, 0 < zeta x) (hUn : ∀ x ∈ U, u x ≠ 0) :
    ∃ c : ℝ, ∀ x ∈ U, v x = c*u x := by
  let q : Yau.Jets.Coord → ℝ := fun x ↦ v x/u x
  have hq (x) (hx : x ∈ U) : DifferentiableAt ℝ q x :=
    ((hv.contDiffAt.div hu.contDiffAt (hUn x hx)).differentiableAt (by simp))
  have hj := round_simplicity_zero_energy_jet u v zeta hu hv hz hc hzn lam hlam he
  have hqd (x) (hx : x ∈ U) : fderiv ℝ q x = 0 := by
    have hd := (hasDerivAt_inv (hUn x hx)).comp_hasFDerivAt x
      (hu.differentiable (by simp) x).hasFDerivAt
    have hm := (hv.differentiable (by simp) x).hasFDerivAt.mul hd
    have heq : q = fun y ↦ v y*(u y)⁻¹ := by funext y; exact div_eq_mul_inv _ _
    have hmf := hm.fderiv
    change fderiv ℝ (fun y ↦ v y*(u y)⁻¹) x = _ at hmf
    have hL : (fderiv ℝ q x).toLinearMap = 0 := by
      apply (Pi.basisFun ℝ (Fin 4)).ext
      intro i
      simp only [Pi.basisFun_apply,LinearMap.zero_apply]
      change fderiv ℝ q x (Pi.single i 1) = 0
      rw [heq,hmf]
      simp only [add_apply,smul_apply,smul_eq_mul,Function.comp_def]
      have h := hj x (hUz x hx) i
      unfold Yau.coordPartial at h
      field_simp [hUn x hx]
      nlinarith only [h]
    ext w
    exact congrArg (fun L : Yau.Jets.Coord →ₗ[ℝ] ℝ ↦ L w) hL
  obtain ⟨c,hc⟩ := hU.exists_is_const_of_fderiv_eq_zero hUc
    (fun x hx ↦ (hq x hx).differentiableWithinAt) (fun x hx ↦ hqd x hx)
  refine ⟨c,?_⟩
  intro x hx
  exact (div_eq_iff (hUn x hx)).mp (hc x hx)

end
end Yau.Target

end OAI
