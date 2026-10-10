import OAI.Analysis.CircleDomains.Sobolev.ScalarCutoffEnergy
import OAI.Analysis.CircleDomains.Modulus.FixedCapacityCutoffs

namespace OAI

/-! The actual smooth band test used by graph capacity. Its gradient
vanishes off the enlarged spatial/value cylinder. -/
open Set Function MeasureTheory Metric
open scoped Topology
noncomputable section
namespace CircleDomainRigidity

def unitBandWitness {u : EuclideanPlane → ℝ} (hu : Continuous u)
    (W : DeGiorgi.MemW1pWitness 2 u univ) (hsu : HasCompactSupport u)
    {C : ℝ} (hC : ∀ t, ‖deriv scalarCapacityBump t‖ ≤ C) :
    DeGiorgi.MemW1pWitness 2
      (fun x => spatialCapacityBump x * scalarCapacityBump (u x)) univ :=
  smoothScalarCutoffWitness hu W hsu scalarCapacityBump.contDiff
    (fun _ => ⟨scalarCapacityBump.nonneg,scalarCapacityBump.le_one⟩)
    hC spatialCapacityBump.contDiff spatialCapacityBump.hasCompactSupport

lemma unitBandWitness_one {u : EuclideanPlane → ℝ} {x : EuclideanPlane}
    (hx : euclideanPlaneCoordinates x ∈ closedBall 0 1) (hu : |u x| ≤ 1) :
    spatialCapacityBump x * scalarCapacityBump (u x) = 1 := by
  rw [spatialCapacityBump_one hx, scalarCapacityBump_one hu, mul_one]

lemma unitBandWitness_zero {u : EuclideanPlane → ℝ} (hu : Continuous u)
    (W : DeGiorgi.MemW1pWitness 2 u univ) (hsu : HasCompactSupport u)
    {C : ℝ} (hC : ∀ t, ‖deriv scalarCapacityBump t‖ ≤ C) {x : EuclideanPlane}
    (hx : 4 < ‖x‖ ∨ 2 < |u x|) :
    spatialCapacityBump x * scalarCapacityBump (u x) = 0 ∧
      (unitBandWitness hu W hsu hC).weakGrad x = 0 := by
  have he (i : Fin 2) : (unitBandWitness hu W hsu hC).weakGrad x i =
      spatialCapacityBump x * (deriv scalarCapacityBump (u x) * W.weakGrad x i) +
      fderiv ℝ spatialCapacityBump x (EuclideanSpace.single i 1) * scalarCapacityBump (u x) := rfl
  rcases hx with hx | hx
  · obtain ⟨hz,hd⟩ := spatialCapacityBump_zero hx
    refine ⟨by rw [hz,zero_mul],?_⟩
    ext i
    simp only [he, hz, hd, zero_apply, zero_mul, add_zero, PiLp.zero_apply]
  · obtain ⟨hz,hd⟩ := scalarCapacityBump_zero hx
    refine ⟨by rw [hz,mul_zero],?_⟩
    ext i
    simp only [he, hz, hd, mul_zero, zero_mul, add_zero, PiLp.zero_apply]

lemma unitBandWitness_energy {u : EuclideanPlane → ℝ} (hu : Continuous u)
    (W : DeGiorgi.MemW1pWitness 2 u univ) (hsu : HasCompactSupport u)
    {C : ℝ} (hC0 : 0 ≤ C) (hC : ∀ t, ‖deriv scalarCapacityBump t‖ ≤ C)
    (hηd : ∀ x, ‖fderiv ℝ spatialCapacityBump x‖ ≤ C) (x : EuclideanPlane) :
    let Q := unitBandWitness hu W hsu hC
    (spatialCapacityBump x * scalarCapacityBump (u x))^2 +
      (|Q.weakGrad x 0|+|Q.weakGrad x 1|)^2 ≤
      ({y : EuclideanPlane | ‖y‖ ≤ 4 ∧ |u y| ≤ 2}).indicator
        (fun y => (1+8*C^2)*(1+(|W.weakGrad y 0|+|W.weakGrad y 1|)^2)) x := by
  dsimp only
  by_cases hx : x ∈ {y : EuclideanPlane | ‖y‖ ≤ 4 ∧ |u y| ≤ 2}
  · rw [indicator_of_mem hx]
    exact smoothScalarCutoffWitness_energy hu W hsu scalarCapacityBump.contDiff
      (fun _ => ⟨scalarCapacityBump.nonneg,scalarCapacityBump.le_one⟩) hC0 hC
      spatialCapacityBump.contDiff spatialCapacityBump.hasCompactSupport
      (fun _ => ⟨spatialCapacityBump.nonneg,spatialCapacityBump.le_one⟩) hηd x
  · rw [indicator_of_notMem hx]
    have hh : 4 < ‖x‖ ∨ 2 < |u x| := by simpa only [mem_ofPred_eq, not_and_or, not_le] using hx
    obtain ⟨hz,hg⟩ := unitBandWitness_zero hu W hsu hC hh
    simp only [hz, hg, PiLp.zero_apply, abs_zero, zero_add, zero_pow (by decide : 2 ≠ 0), le_rfl]

end CircleDomainRigidity

end

end OAI
