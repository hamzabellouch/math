import OAI.MathematicalPhysics.DefocusingNLS.Profile.CartesianDirectionalCalculus

namespace OAI

/-! The dilation transport and its exact commutator with the Laplacian. -/

open scoped ContDiff Laplacian
namespace DefocusingNLS
local notation "E" => EuclideanSpace ℝ (Fin 12)

noncomputable def cartesianTransport (f : E → ℂ) (x : E) : ℂ :=
  fderiv ℝ f x ((1/2 : ℝ) • x)

theorem cartesianTransport_contDiff (f : E → ℂ) (hf : ContDiff ℝ ∞ f) :
    ContDiff ℝ ∞ (cartesianTransport f) :=
  (contDiff_infty_iff_fderiv.mp hf).2.clm_apply (contDiff_id.const_smul (1/2 : ℝ))

theorem cartesianDerivative_cartesianTransport (f : E → ℂ) (hf : ContDiff ℝ ∞ f)
    (v : E) :
    cartesianDerivative v (cartesianTransport f)=fun x =>
      cartesianTransport (cartesianDerivative v f) x+
        (1/2 : ℂ)*cartesianDerivative v f x := by
  funext x
  exact cartesianDerivative_transport f hf x v

theorem cartesianTransport_sum (F : Fin 12 → E → ℂ)
    (hF : ∀ j, ContDiff ℝ ∞ (F j)) :
    cartesianTransport (fun x => ∑ j : Fin 12, F j x)=
      fun x => ∑ j : Fin 12, cartesianTransport (F j) x := by
  funext x
  exact congrFun (cartesianDerivative_sum F hF ((1/2 : ℝ) • x)) x

theorem cartesianDerivative_twice_transport (f : E → ℂ) (hf : ContDiff ℝ ∞ f)
    (v x : E) :
    cartesianDerivative v (cartesianDerivative v (cartesianTransport f)) x=
      cartesianTransport (cartesianDerivative v (cartesianDerivative v f)) x+
        cartesianDerivative v (cartesianDerivative v f) x := by
  have hd := cartesianDerivative_contDiff f hf v
  have ht := cartesianTransport_contDiff (cartesianDerivative v f) hd
  rw [cartesianDerivative_cartesianTransport f hf v]
  have hs : cartesianDerivative v (fun y =>
      cartesianTransport (cartesianDerivative v f) y+
        (1/2 : ℂ)*cartesianDerivative v f y) x=
      cartesianDerivative v (cartesianTransport (cartesianDerivative v f)) x+
        (1/2 : ℂ)*cartesianDerivative v (cartesianDerivative v f) x := by
    change fderiv ℝ (fun y => cartesianTransport (cartesianDerivative v f) y+
      (1/2 : ℂ)*cartesianDerivative v f y) x v=
      fderiv ℝ (cartesianTransport (cartesianDerivative v f)) x v+
        (1/2 : ℂ)*fderiv ℝ (cartesianDerivative v f) x v
    rw [fderiv_fun_add (ht.differentiable (by simp) x)
      ((hd.differentiable (by simp) x).const_mul (1/2 : ℂ)),
      fderiv_const_mul (hd.differentiable (by simp) x)]
    simp only [add_apply,smul_apply,smul_eq_mul]
  rw [hs,cartesianDerivative_cartesianTransport _ hd v]
  dsimp only
  ring

theorem laplacian_cartesianTransport (f : E → ℂ) (hf : ContDiff ℝ ∞ f) :
    Δ (cartesianTransport f)=fun x => cartesianTransport (Δ f) x+Δ f x := by
  let e := EuclideanSpace.basisFun (Fin 12) ℝ
  rw [laplacian_eq_cartesianDerivatives _ (cartesianTransport_contDiff f hf)]
  have hi (x : E) :
      (∑ j : Fin 12, cartesianDerivative (e j)
        (cartesianDerivative (e j) (cartesianTransport f)) x)=
      (∑ j : Fin 12, cartesianTransport
        (cartesianDerivative (e j) (cartesianDerivative (e j) f)) x)+
      ∑ j : Fin 12, cartesianDerivative (e j) (cartesianDerivative (e j) f) x := by
    simp_rw [cartesianDerivative_twice_transport f hf]
    exact Finset.sum_add_distrib
  funext x
  rw [hi]
  rw [laplacian_eq_cartesianDerivatives f hf,
    cartesianTransport_sum _ (fun j => cartesianDerivative_contDiff _
      (cartesianDerivative_contDiff f hf (e j)) (e j))]

end DefocusingNLS

end OAI
