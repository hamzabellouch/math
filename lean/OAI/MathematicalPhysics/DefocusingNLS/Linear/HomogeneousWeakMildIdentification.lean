import OAI.MathematicalPhysics.DefocusingNLS.Linear.HomogeneousMeasurableMildContinuity
import OAI.MathematicalPhysics.DefocusingNLS.Linear.HomogeneousLinearizedFlow

namespace OAI

/-! # Identification of bounded weakly continuous mild limits -/

open Set MeasureTheory

namespace DefocusingNLS

local notation "E" => EuclideanSpace ℝ (Fin 12)

theorem homogeneousLinearizedTrajectory_eq_of_bounded_mild (a b k T C : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k) (hT : 0 ≤ T)
    (m : ℕ) (q u₀ : HomogeneousY a k) (v : Icc (0 : ℝ) T → HomogeneousY a k)
    (hv : ∀ t, ‖v t‖ ≤ C)
    (hp : ∀ y : E, Continuous (fun t => homogeneousPhysicalCLM a k ha ha1 hk (v t) y))
    (heq : ∀ t : Icc (0 : ℝ) T,
      v t = homogeneousFreeOperator a b k t ha ha1 hk u₀ +
        homogeneousDuhamel a b k ha ha1 hk t
          (fun s => homogeneousLinearizedPotential a k ha ha1 hk m q (v (projIcc 0 T hT s)))) :
    v = fun t => homogeneousLinearizedTrajectory a b k T ha ha1 hk hT m q u₀ t := by
  let B := homogeneousLinearizedPotential a k ha ha1 hk m q
  let r := fun s => B (v (projIcc 0 T hT s))
  have hr : StronglyMeasurable r := B.continuous.comp_stronglyMeasurable
    (stronglyMeasurable_homogeneous_clamped a k T ha ha1 hk hT v hp)
  have hir : IntegrableOn r (Icc 0 T) := B.integrable_comp
    (integrableOn_homogeneous_clamped a k T C ha ha1 hk hT v hv hp)
  have hd : Continuous (fun t : Icc (0 : ℝ) T => homogeneousDuhamel a b k ha ha1 hk t r) :=
    (continuousOn_homogeneousDuhamel_measurable a b k T ha ha1 hk r hr hir).domRestrict
  have hc : Continuous v := by
    have h := ((continuous_homogeneousFreeOperator a b k ha ha1 hk u₀).comp
      continuous_subtype_val).add hd
    exact h.congr (fun t => (heq t).symm)
  let w : C(Icc (0 : ℝ) T, HomogeneousY a k) := ⟨v, hc⟩
  have hw := homogeneousLinearizedTrajectory_unique a b k T ha ha1 hk hT m q u₀ w heq
  exact congrArg (fun z : C(Icc (0 : ℝ) T, HomogeneousY a k) => (z : Icc (0 : ℝ) T → HomogeneousY a k)) hw

end DefocusingNLS

end OAI
