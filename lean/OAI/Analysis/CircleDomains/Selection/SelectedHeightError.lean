import OAI.Analysis.CircleDomains.Transfer.ModelHeightErrorTransport
import OAI.Analysis.CircleDomains.Transfer.ModelFlattenedSelection
import OAI.Analysis.CircleDomains.Modulus.BarrierErrorBudgets

namespace OAI

/-! The selected flattening and the nearly maximal deficit give an actual
transported error witness with the prescribed small source energy. -/
open Set Function Filter MeasureTheory Metric
open scoped Topology ContDiff ENNReal
noncomputable section
namespace CircleDomainRigidity

 theorem height_error_energy_mono {C₀ C₁ V e d : ℝ}
    (hd : d ≤ e) :
    2*C₀^2*(2*e+4*Real.pi*d)+4*C₁^2*(e+e)^2*V ≤
      2*C₀^2*(2*e+4*Real.pi*e)+4*C₁^2*(e+e)^2*V := by
  apply add_le_add _ le_rfl
  apply mul_le_mul_of_nonneg_left
  · exact add_le_add le_rfl (mul_le_mul_of_nonneg_left hd (by positivity))
  · positivity

namespace CompactScalarModel
variable {G : Set Sphere} {m : ℕ} {u : Fin m → EuclideanPlane → ℝ}

 theorem FlattenedSourceSelection.exists_small_height_error
    (M : CompactScalarModel G u) (hG : IsOpen G) (hinf : OnePoint.infty ∈ G)
    {R d A L e : ℝ} (H : ControlledHeight R d)
    {Wold : ∀ i, DeGiorgi.MemW1pWitness 2 (u i) (physicalPlaneDomain G)}
    (S : FlattenedSourceSelection M H Wold A L e e) (he : 0 < e) (hde : d ≤ e)
    (θ : EuclideanPlane → ℝ) (hθ : ContDiff ℝ ∞ θ) (hsθ : HasCompactSupport θ)
    (hθA : tsupport θ ⊆ ball 0 A) {C : ℝ} (hC : 0 ≤ C)
    (hθunit : ∀ x, θ x ∈ Icc (0 : ℝ) 1) (hθd : ∀ x, ‖fderiv ℝ θ x‖ ≤ C)
    (hclose : ∀ x ∈ ball (0 : EuclideanPlane) A,
      |H.height (complexPlaneCoordinates x)-x 1| ≤ e)
    {ν : ℝ} (hbudget : 2*(2*e+4*Real.pi*e)+4*C^2*(e+e)^2*
      (volume (ball (0 : EuclideanPlane) A)).toReal < ν^2) :
    ∃ E : DeGiorgi.MemW1pWitness 2 (planeInverseTransport (extendAtInfinity M.function)
        (fun y => θ y*(flattenValues S.heightValues (H.height (complexPlaneCoordinates y))-y 1)))
        (physicalPlaneDomain G),
      (∫ x in physicalPlaneDomain G, E.weakGrad x 0^2+E.weakGrad x 1^2) < ν^2 := by
  obtain ⟨E,hE⟩ := M.compact_height_error_transport hG hinf H A
    (flattenValues S.heightValues) (flattenValues_lipschitz S.height_open.measurableSet).continuous
    S.heightWitness he he.le he.le S.height_error (fun t => (S.height_close t).le) hclose
    θ hθ hsθ hθA (show (0 : ℝ) ≤ 1 by norm_num) hC
    (fun x => by rw [abs_of_nonneg (hθunit x).1]; exact (hθunit x).2) hθd
  refine ⟨E,hE.trans_lt ?_⟩
  have hm := height_error_energy_mono (C₀ := 1) (C₁ := C)
    (V := (volume (ball (0 : EuclideanPlane) A)).toReal) hde
  norm_num only [one_pow, mul_one] at hm
  simpa only [one_pow, mul_one] using hm.trans_lt hbudget

end CompactScalarModel
end CircleDomainRigidity

end

end OAI
