import OAI.Analysis.CircleDomains.Modulus.ModelSelectedBarrier
import OAI.Analysis.CircleDomains.Sobolev.BarrierEnergyAssembly

namespace OAI

/-! Small selected-coordinate errors give a strict total source barrier
bound, uniformly for any smooth barrier with the specified constants. -/
open Set Function Filter MeasureTheory Metric
open scoped Topology ContDiff ENNReal
noncomputable section
namespace CircleDomainRigidity
namespace CompactScalarModel
variable {G : Set Sphere} {m : ℕ} {u : Fin m → EuclideanPlane → ℝ}

 theorem small_selected_barrier_energy (M : CompactScalarModel G u)
    (hG : IsOpen G) (hinf : OnePoint.infty ∈ G)
    {R d A L e t η N : ℝ} (H : ControlledHeight R d)
    {Wold : ∀ i, DeGiorgi.MemW1pWitness 2 (u i) (physicalPlaneDomain G)}
    (S : FlattenedSourceSelection M H Wold A L e e)
    (he : 0 ≤ e) (het : e ≤ t) (ht : 0 ≤ t) (hηpos : 0 < η)
    (ζ : ℂ → ℝ) (θ : EuclideanPlane → ℝ)
    (hζ : ∀ z ∈ {z : ℂ | (z : Sphere) ∈ G} ∩ ball 0 L, ζ z = 1)
    (hθ : ∀ x ∈ physicalPlaneDomain G ∩ ball 0 L,
      θ (complexPlaneCoordinates.symm (M.function (complexPlaneCoordinates x))) = 1)
    (hp : Continuous (M.compactPrioritySource S.cutoff S.value ζ))
    (hq : Continuous (M.compactHeightSource H (flattenValues S.heightValues) θ))
    (Wp : DeGiorgi.MemW1pWitness 2 (M.compactPrioritySource S.cutoff S.value ζ)
      (physicalPlaneDomain G ∩ ball 0 L))
    (Wq : DeGiorgi.MemW1pWitness 2 (M.compactHeightSource H (flattenValues S.heightValues) θ)
      (physicalPlaneDomain G ∩ ball 0 L))
    (Wx : DeGiorgi.MemW1pWitness 2 (fun x => (M.function (complexPlaneCoordinates x)).re)
      (physicalPlaneDomain G ∩ ball 0 L))
    (Wy : DeGiorgi.MemW1pWitness 2 (fun x => (M.function (complexPlaneCoordinates x)).im)
      (physicalPlaneDomain G ∩ ball 0 L))
    (E : DeGiorgi.MemW1pWitness 2 (planeInverseTransport (extendAtInfinity M.function)
      (fun y => θ y*(flattenValues S.heightValues (H.height (complexPlaneCoordinates y))-y 1)))
      (physicalPlaneDomain G))
    (hE : (∫ x in physicalPlaneDomain G, E.weakGrad x 0^2+E.weakGrad x 1^2) ≤ t^2)
    (hheight : ∀ x ∈ physicalPlaneDomain G ∩ ball 0 L,
      |H.height (M.function (complexPlaneCoordinates x))-(M.function (complexPlaneCoordinates x)).im| ≤ e)
    (hN : (eLpNorm (fun x => weakPairDifferential (Wx.weakGrad x) (Wy.weakGrad x)) 2
      (volume.restrict (physicalPlaneDomain G ∩ ball 0 L))).toReal ≤ N)
    {Φ : EuclideanPlane → ℝ} (hΦ : ContDiff ℝ ∞ Φ) (hsΦ : HasCompactSupport Φ)
    {B M₁ M₂ : ℝ} (hB : 0 ≤ B) (hM₁ : 0 ≤ M₁) (hM₂ : 0 ≤ M₂)
    (hΦb : ∀ z, ‖Φ z‖ ≤ B) (hbound : ∀ z, ‖fderiv ℝ Φ z‖ ≤ M₁)
    (hlip : ∀ z w, ‖fderiv ℝ Φ z-fderiv ℝ Φ w‖ ≤ M₂*‖z-w‖)
    (henergy : (∫ x, ‖planeCovectorGradient (fderiv ℝ Φ x)‖^2) ≤ (η/3)^2)
    (hbudget : M₁*(t+t)+(M₂*(t+t))*N+4*M₁*t < η/3) :
    ∃ W : DeGiorgi.MemW1pWitness 2 (fun x => Φ (planePair
        (M.compactPrioritySource S.cutoff S.value ζ x)
        (M.compactHeightSource H (flattenValues S.heightValues) θ x)))
      (physicalPlaneDomain G ∩ ball 0 L),
      (eLpNorm W.weakGrad 2 (volume.restrict (physicalPlaneDomain G ∩ ball 0 L))).toReal < η := by
  obtain ⟨W,hW⟩ := M.selected_barrier_error hG hinf H S ζ θ hζ hθ hp hq Wp Wq Wx Wy E
    ht he he hE hheight (hΦ.of_le (by simp)) hB hM₁ hM₂ hΦb hbound hlip
  have hfirst : M₁*(e+t) ≤ M₁*(t+t) :=
    mul_le_mul_of_nonneg_left (add_le_add het le_rfl) hM₁
  have hsecond : (M₂*(e+e))*(eLpNorm
      (fun x => weakPairDifferential (Wx.weakGrad x) (Wy.weakGrad x)) 2
      (volume.restrict (physicalPlaneDomain G ∩ ball 0 L))).toReal ≤ (M₂*(t+t))*N :=
    mul_le_mul (mul_le_mul_of_nonneg_left (add_le_add het het) hM₂) hN
      ENNReal.toReal_nonneg (mul_nonneg hM₂ (add_nonneg ht ht))
  have hthird : 4*M₁*e ≤ 4*M₁*t := mul_le_mul_of_nonneg_left het (by positivity)
  have herror := hW.trans ((add_le_add (add_le_add hfirst hsecond) hthird))
  have htotal := M.barrier_energy_from_reference hG hinf L Wx Wy hΦ hsΦ W
    (show 0 ≤ η/3 by positivity) henergy herror
  refine ⟨W,?_⟩
  linarith

end CompactScalarModel
end CircleDomainRigidity

end

end OAI
