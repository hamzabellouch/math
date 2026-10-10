import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanFactorHeight
import OAI.GroupTheory.PolycyclicRecognition.Algebra.FactorOverlap

namespace OAI

/-! # Logarithmic coordinates of the Cartan overlap

Injectivity of the ambient exponential identifies the two logarithms of
an overlap element. A fixed linear retraction compares their coordinate
norms; this controls the entire overlap rather than its center.
-/

noncomputable section
namespace PolycyclicRecognition.CartanFactorModel

open Module
open scoped Manifold

variable {EG G : Type*} [NormedAddCommGroup EG] [NormedSpace ℝ EG]
  [FiniteDimensional ℝ EG] [MetricSpace G] [ChartedSpace EG G] [Group G]
  [LieGroup (𝓘(ℝ, EG)) ⊤ G]
  {H : LieSubalgebra ℝ (GroupLieAlgebra (𝓘(ℝ, EG)) G)} [H.IsCartanSubalgebra]
  {ExpG : GroupLieAlgebra (𝓘(ℝ, EG)) G → G} (F : CartanFactorModel H ExpG)

theorem overlap_log_eq (hExpG : Function.Injective ExpG)
    (hbijN : Function.Bijective F.ExpN) (hbijD : Function.Bijective F.ExpD)
    (u : F.N.carrier) (d : F.D.carrier) (hu : F.inclusionN u = F.inclusionD d) :
    ((F.N.equiv.symm ((Equiv.ofBijective F.ExpN hbijN).symm u) : cartanRootIdeal H) :
      GroupLieAlgebra (𝓘(ℝ, EG)) G) =
        (cartanLog H F.D.equiv F.ExpD hbijD d : GroupLieAlgebra (𝓘(ℝ, EG)) G) := by
  apply hExpG
  have hn := F.compatibleN (F.N.equiv.symm ((Equiv.ofBijective F.ExpN hbijN).symm u))
  simp only [F.N.equiv.apply_symm_apply] at hn
  have hn0 : F.ExpN ((Equiv.ofBijective F.ExpN hbijN).symm u) = u :=
    (Equiv.ofBijective F.ExpN hbijN).apply_symm_apply u
  rw [hn0] at hn
  have hd := F.compatibleD (cartanLog H F.D.equiv F.ExpD hbijD d)
  rw [exp_cartanLog H F.D.equiv F.ExpD hbijD d] at hd
  exact hn.symm.trans (hu.trans hd)

theorem exists_overlap_coordinate_bound
    {I : Type*} [Fintype I] (b : Basis I ℝ (cartanRootIdeal H)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (v : cartanRootIdeal H) (w : H),
      (v : GroupLieAlgebra (𝓘(ℝ, EG)) G) = w →
      ‖b.equivFun v‖ ≤ C * ‖(finBasis ℝ H).equivFun w‖ := by
  let i := (cartanRootIdeal H).toSubmodule.subtype
  let r := i.leftInverse
  let f := (b.equivFun.toLinearMap.comp (r.comp H.toSubmodule.subtype)).comp
    (finBasis ℝ H).equivFun.symm.toLinearMap
  let fc := f.toContinuousLinearMap
  refine ⟨‖fc‖, norm_nonneg _, ?_⟩
  intro v w hvw
  have hr : r (v : GroupLieAlgebra (𝓘(ℝ, EG)) G) = v :=
    LinearMap.leftInverse_apply_of_inj (cartanRootIdeal H).toSubmodule.ker_subtype v
  have he : fc ((finBasis ℝ H).equivFun w) = b.equivFun v := by
    change b.equivFun (r ((finBasis ℝ H).equivFun.symm
      ((finBasis ℝ H).equivFun w) : H)) = b.equivFun v
    rw [LinearEquiv.symm_apply_apply, ← hvw, hr]
  simpa only [he] using fc.le_opNorm ((finBasis ℝ H).equivFun w)

end PolycyclicRecognition.CartanFactorModel

end

end OAI
