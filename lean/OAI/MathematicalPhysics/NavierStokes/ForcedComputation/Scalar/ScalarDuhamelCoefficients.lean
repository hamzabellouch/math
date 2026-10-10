import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Scalar.ScalarMassCalculus
import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Scalar.PlaneCoefficientJets

namespace OAI

/-! The three divergence-form coefficients for the actual scalar advection equation. -/

noncomputable section
namespace ForcedComputation.VelocityDetector
open ShearFlows PlanarHamiltonian Set
open scoped ContDiff BigOperators

def driftCoefficients (a : ℝ → Plane → Plane) (i : Fin 3) (p : ℝ × Plane) : ℝ :=
  Fin.cases (PlanarHamiltonian.divergence (a p.1) p.2) (fun j => -a p.1 p.2 j) i

@[simp] theorem driftCoefficients_zero (a : ℝ → Plane → Plane) (p : ℝ × Plane) :
    driftCoefficients a 0 p = PlanarHamiltonian.divergence (a p.1) p.2 := rfl

@[simp] theorem driftCoefficients_succ (a : ℝ → Plane → Plane) (j : Fin 2) (p : ℝ × Plane) :
    driftCoefficients a j.succ p = -a p.1 p.2 j := by
  simp only [driftCoefficients, Fin.cases_succ]

theorem spatialD_parameter_smooth {f : ℝ × Plane → ℝ} (hf : ContDiff ℝ ∞ f) (j : Fin 2) :
    ContDiff ℝ ∞ (fun p : ℝ × Plane => spatialD j (fun y => f (p.1,y)) p.2) := by
  have he (p : ℝ × Plane) : spatialD j (fun y => f (p.1,y)) p.2 =
      fderiv ℝ f p (0, PlanarHamiltonian.basis j) := by
    have hi : HasFDerivAt (fun y : Plane => (p.1,y))
        (ContinuousLinearMap.inr ℝ ℝ Plane) p.2 := hasFDerivAt_prodMk_right p.1 p.2
    have hd := (hf.differentiable (by simp) p).hasFDerivAt.comp p.2 hi
    change HasFDerivAt (fun y : Plane => f (p.1,y)) _ p.2 at hd
    rw [spatialD, hd.fderiv]
    rfl
  simp_rw [he]
  exact (hf.fderiv_right (by simp)).clm_apply contDiff_const

theorem driftCoefficients_smooth {a : ℝ → Plane → Plane}
    (ha : ContDiff ℝ ∞ (Function.uncurry a)) (i : Fin 3) :
    ContDiff ℝ ∞ (driftCoefficients a i) := by
  refine Fin.cases ?_ (fun j => ?_) i
  · change ContDiff ℝ ∞ (fun p : ℝ × Plane => ∑ j : Fin 2, spatialD j (fun y => a p.1 y j) p.2)
    exact ContDiff.sum fun j _ => spatialD_parameter_smooth ((contDiff_apply ℝ ℝ j).comp ha) j
  · change ContDiff ℝ ∞ (fun p : ℝ × Plane => -a p.1 p.2 j)
    exact ((contDiff_apply ℝ ℝ j).comp ha).neg

theorem driftCoefficients_periodic {a : ℝ → Plane → Plane}
    (ha : ContDiff ℝ ∞ (Function.uncurry a)) (hp : ∀ t, PlanePeriodic (a t))
    (i : Fin 3) (t : ℝ) : PlanePeriodic (fun x => driftCoefficients a i (t,x)) := by
  have hs : ContDiff ℝ ∞ (a t) := ha.comp (contDiff_const.prodMk contDiff_id)
  refine Fin.cases ?_ (fun j => ?_) i
  · intro x n
    change (∑ j : Fin 2, spatialD j (fun y => a t y j) (x + fun j => (n j : ℝ))) =
      ∑ j : Fin 2, spatialD j (fun y => a t y j) x
    apply Finset.sum_congr rfl
    intro j _
    exact spatialD_periodic ((contDiff_apply ℝ ℝ j).comp hs)
      (fun y m => congrFun (hp t y m) j) j x n
  · intro x n
    exact congrArg (fun v : Plane => -v j) (hp t x n)

theorem driftCoefficients_supported {a : ℝ → Plane → Plane} {K : Set Plane}
    (hK : IsClosed K) {t : ℝ} (ha : ∀ x ∉ K, a t x = 0)
    (i : Fin 3) (x : Plane) (hx : x ∉ K) : driftCoefficients a i (t,x) = 0 := by
  have hd (j : Fin 2) : fderiv ℝ (fun y => a t y j) x = 0 := by
    apply fderiv_of_notMem_tsupport
    have hs : tsupport (fun y => a t y j) ⊆ K := by
      apply closure_minimal _ hK
      intro y hy
      by_contra h
      apply hy
      simp only [ha y h, Pi.zero_apply]
    exact fun h => hx (hs h)
  refine Fin.cases ?_ (fun j => ?_) i
  · change (∑ j : Fin 2, fderiv ℝ (fun y => a t y j) x (PlanarHamiltonian.basis j)) = 0
    simp only [hd, zero_apply, Finset.sum_const_zero]
  · change -a t x _ = 0
    simp only [ha x hx, Pi.zero_apply, neg_zero]

theorem driftCoefficients_effective_source {a : Plane → Plane} {w : Plane → ℝ}
    (ha : ContDiff ℝ ∞ a) (hw : ContDiff ℝ ∞ w) (h : Plane → ℝ) (x : Plane) :
    h x + PlanarHamiltonian.divergence a x * w x +
      (∑ j : Fin 2, spatialD j (fun y => (-a y j) * w y) x) =
        h x - fderiv ℝ w x (a x) := by
  have he (j : Fin 2) : spatialD j (fun y => (-a y j) * w y) x =
      -spatialD j (fun y => (w y • a y) j) x := by
    have hf : (fun y => (-a y j) * w y) = fun y => -((w y • a y) j) := by
      funext y
      simp only [Pi.smul_apply, smul_eq_mul]
      ring
    rw [hf, spatialD, fderiv_fun_neg]
    rfl
  simp_rw [he]
  rw [Finset.sum_neg_distrib]
  change h x + PlanarHamiltonian.divergence a x * w x -
    PlanarHamiltonian.divergence (fun y => w y • a y) x = _
  rw [divergence_scalar_product ha hw]
  ring

end ForcedComputation.VelocityDetector

end

end OAI
