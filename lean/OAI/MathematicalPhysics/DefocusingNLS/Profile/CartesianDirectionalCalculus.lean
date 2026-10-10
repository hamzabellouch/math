import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialCartesianCalculus
import Mathlib.Analysis.Calculus.FDeriv.Symmetric

namespace OAI

/-! Constant Cartesian derivatives commute with each other and the Laplacian. -/

open scoped ContDiff Laplacian
namespace DefocusingNLS
local notation "E" => EuclideanSpace ℝ (Fin 12)

noncomputable def cartesianDerivative (v : E) (f : E → ℂ) (x : E) : ℂ :=
  fderiv ℝ f x v

theorem cartesianDerivative_contDiff (f : E → ℂ) (hf : ContDiff ℝ ∞ f) (v : E) :
    ContDiff ℝ ∞ (cartesianDerivative v f) :=
  (contDiff_infty_iff_fderiv.mp hf).2.clm_apply contDiff_const

theorem cartesianDerivative_second (f : E → ℂ) (hf : ContDiff ℝ ∞ f)
    (x v w : E) :
    cartesianDerivative v (cartesianDerivative w f) x=
      fderiv ℝ (fderiv ℝ f) x v w := by
  have hd := (contDiff_infty_iff_fderiv.mp hf).2.differentiable (by simp) x
  unfold cartesianDerivative
  rw [fderiv_clm_apply hd (differentiableAt_const w)]
  simp

theorem cartesianDerivative_commute (f : E → ℂ) (hf : ContDiff ℝ ∞ f) (v w : E) :
    cartesianDerivative v (cartesianDerivative w f)=
      cartesianDerivative w (cartesianDerivative v f) := by
  funext x
  rw [cartesianDerivative_second f hf,cartesianDerivative_second f hf]
  exact (hf.contDiffAt.isSymmSndFDerivAt (by simp)).eq v w

theorem cartesianDerivative_sum (F : Fin 12 → E → ℂ)
    (hF : ∀ j, ContDiff ℝ ∞ (F j)) (v : E) :
    cartesianDerivative v (fun x => ∑ j : Fin 12, F j x)=
      fun x => ∑ j : Fin 12, cartesianDerivative v (F j) x := by
  funext x
  unfold cartesianDerivative
  rw [fderiv_fun_sum (fun j _ => (hF j).differentiable (by simp) x)]
  simp

theorem laplacian_eq_cartesianDerivatives (f : E → ℂ) (hf : ContDiff ℝ ∞ f) :
    Δ f=fun x => ∑ j : Fin 12,
      cartesianDerivative (EuclideanSpace.basisFun (Fin 12) ℝ j)
        (cartesianDerivative (EuclideanSpace.basisFun (Fin 12) ℝ j) f) x := by
  funext x
  rw [InnerProductSpace.laplacian_eq_iteratedFDeriv_orthonormalBasis _
    (EuclideanSpace.basisFun (Fin 12) ℝ)]
  apply Finset.sum_congr rfl
  intro j _
  exact radial_second_directional_eq f x _ (hf.contDiffAt.of_le (by simp))

theorem laplacian_cartesianDerivative (f : E → ℂ) (hf : ContDiff ℝ ∞ f) (v : E) :
    Δ (cartesianDerivative v f)=cartesianDerivative v (Δ f) := by
  let e := EuclideanSpace.basisFun (Fin 12) ℝ
  have hi (j : Fin 12) :
      cartesianDerivative (e j) (cartesianDerivative (e j) (cartesianDerivative v f))=
        cartesianDerivative v (cartesianDerivative (e j) (cartesianDerivative (e j) f)) := by
    rw [cartesianDerivative_commute f hf (e j) v]
    exact cartesianDerivative_commute _ (cartesianDerivative_contDiff f hf (e j)) (e j) v
  rw [laplacian_eq_cartesianDerivatives _ (cartesianDerivative_contDiff f hf v),
    laplacian_eq_cartesianDerivatives f hf,
    cartesianDerivative_sum _ (fun j => cartesianDerivative_contDiff _
      (cartesianDerivative_contDiff f hf (e j)) (e j)) v]
  funext x
  exact Finset.sum_congr rfl (fun j _ => congrFun (hi j) x)

theorem laplacian_contDiff (f : E → ℂ) (hf : ContDiff ℝ ∞ f) :
    ContDiff ℝ ∞ (Δ f) := by
  rw [laplacian_eq_cartesianDerivatives f hf]
  exact ContDiff.sum fun j _ => cartesianDerivative_contDiff _
    (cartesianDerivative_contDiff f hf (EuclideanSpace.basisFun (Fin 12) ℝ j)) _

theorem cartesianDerivative_transport (f : E → ℂ) (hf : ContDiff ℝ ∞ f) (x v : E) :
    fderiv ℝ (fun y => fderiv ℝ f y ((1/2 : ℝ) • y)) x v=
      fderiv ℝ (cartesianDerivative v f) x ((1/2 : ℝ) • x)+
        (1/2 : ℂ)*cartesianDerivative v f x := by
  have hd := (contDiff_infty_iff_fderiv.mp hf).2.differentiable (by simp) x
  have hv : HasFDerivAt (fun y : E => (1/2 : ℝ) • y)
      ((1/2 : ℝ) • ContinuousLinearMap.id ℝ E) x :=
    (hasFDerivAt_id (𝕜 := ℝ) x).const_smul (1/2 : ℝ)
  rw [fderiv_clm_apply hd hv.differentiableAt,hv.fderiv]
  simp only [add_apply,ContinuousLinearMap.comp_apply,ContinuousLinearMap.flip_apply,
    smul_apply,ContinuousLinearMap.id_apply,map_smul,Complex.real_smul]
  have hs := ((hf.contDiffAt (x := x)).isSymmSndFDerivAt (by simp)).eq v x
  have hsecond := cartesianDerivative_second f hf x x v
  unfold cartesianDerivative at hsecond ⊢
  rw [hsecond,hs]
  push_cast
  ring

end DefocusingNLS

end OAI
