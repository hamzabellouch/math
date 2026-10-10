import OAI.Analysis.CircleDomains.Modulus.FiniteDiskSlicePayment
import OAI.Analysis.CircleDomains.Rigidity.AxialSlicesFromTrace

namespace OAI

/-! The actual matched field satisfies the finite enlarged-hole slice
inequality. No independent slice or flux assumption is retained. -/
open Set Function Filter MeasureTheory Metric
open scoped Topology
noncomputable section
attribute [local instance] Classical.propDecidable
namespace CircleDomainRigidity
open FiniteTransfer
attribute [local instance] sphereMetric sphereBorel
local instance : BorelSpace Sphere := ⟨rfl⟩
namespace MatchedConformalEnds
variable {G : Set Sphere} {f : Sphere → Sphere} (D : MatchedConformalEnds G f)

 theorem actual_finite_disk_slice [Countable D.IndexedMatchedPair]
    (E : D.MatchedRoundDisks) (hG : IsCircleDomain G) (hinf : OnePoint.infty ∈ G)
    (hf : IsConformalEquivalence f G (f '' G)) (hfix : f OnePoint.infty = OnePoint.infty)
    (hH : IsCircleDomain (f '' G)) (hinf' : OnePoint.infty ∈ f '' G)
    (R : ℝ) (i k : Fin 2) (y : ℝ)
    (htrace : volume ((fun x => (complexPlaneCoordinates.symm
      (D.selectedPlane hG.1 hf (complexCoordinateLine i y x))) k) ''
      {x | complexCoordinateLine i y x ∈ D.commonPointPlane}) = 0)
    (htoll : Summable (fun j : D.IndexedMatchedPair =>
      (Icc (transverseCoordinate i (E.sourceCenter j)-E.sourceRadius j)
        (transverseCoordinate i (E.sourceCenter j)+E.sourceRadius j)).indicator
          (fun _ => 2*E.targetRadius j) y))
    (hρ : IntegrableOn (fun x => ‖deriv (fun z : ℂ => finiteCoord (f (z : Sphere)))
        (complexCoordinateLine i y x)‖)
      {x | (complexCoordinateLine i y x : Sphere) ∈ G ∧ complexCoordinateLine i y x ∈ ball 0 R} volume)
    (F : Finset D.IndexedMatchedPair) {η : ℝ} (hη : 0 < η)
    (hd : Pairwise (Disjoint on fun j : F => closedBall (E.sourceCenter j) (E.sourceRadius j+η)))
    (hone : ∀ l ∉ F, ∀ j ∈ F, ∀ m ∈ F,
      (closedBall (E.sourceCenter l) (E.sourceRadius l) ∩
        closedBall (E.sourceCenter j) (E.sourceRadius j+η)).Nonempty →
      (closedBall (E.sourceCenter l) (E.sourceRadius l) ∩
        closedBall (E.sourceCenter m) (E.sourceRadius m+η)).Nonempty → j = m)
    {a b : ℝ} (hab : a < b)
    (hseg : ∀ x ∈ Icc a b, complexCoordinateLine i y x ∈ ball 0 R)
    (ha : ∀ j ∈ F, complexCoordinateLine i y a ∉ closedBall (E.sourceCenter j) (E.sourceRadius j+η))
    (hb : ∀ j ∈ F, complexCoordinateLine i y b ∉ closedBall (E.sourceCenter j) (E.sourceRadius j+η)) :
    let v := fun x => (complexPlaneCoordinates.symm (D.selectedPlane hG.1 hf (complexCoordinateLine i y x))) k
    v b-v a-
      (∑ j ∈ crossingDisks (fun j : F => axialSwap i (E.sourceCenter j))
          (fun j => E.sourceRadius j+η) y a b,
        (v (axialChord i (E.sourceCenter j) (E.sourceRadius j+η) y).2-
          v (axialChord i (E.sourceCenter j) (E.sourceRadius j+η) y).1)) ≤
      (∫ x in Icc a b ∩ {x | (complexCoordinateLine i y x : Sphere) ∈ G},
        ‖deriv (fun z : ℂ => finiteCoord (f (z : Sphere))) (complexCoordinateLine i y x)‖)+
        2*axialDiskToll i (fun j : {j : D.IndexedMatchedPair // j ∉ F} => E.sourceCenter j)
          (fun j => E.sourceRadius j) (fun j => E.targetRadius j) y := by
  dsimp only
  have hmem (j : D.IndexedMatchedPair) (z : ℂ) :
      (z : Sphere) ∈ j.val.1 ↔ z ∈ closedBall (E.sourceCenter j) (E.sourceRadius j) := by
    rw [E.source_eq j]
    constructor
    · rintro ⟨w,hw,he⟩
      exact OnePoint.coe_injective he ▸ hw
    · exact mem_image_of_mem _
  apply finite_disk_slice_payment i E.sourceCenter E.sourceRadius E.targetRadius
    E.source_nonneg E.target_nonneg F hη hd hone hab ha hb
  · exact htoll.comp_injective Subtype.val_injective
  · exact hG.1.measurableSet.preimage (OnePoint.continuous_coe.comp (complexCoordinateLine_contDiff i y).continuous).measurable
  · exact hρ.mono_set (fun x hx => ⟨hx.2,hseg x hx.1⟩)
  · exact fun _ _ => norm_nonneg _
  · intro u w huw hsub havoid
    have hp := D.axial_slices_of_trace E hG hinf hf hfix hH hinf' R i k y htrace htoll hρ u w huw F
      (fun x hx => hseg x (hsub hx)) (by
        intro x hx j hj hxj
        exact havoid x hx j hj ((hmem j _).mp hxj))
    simpa only [hmem] using hp

end MatchedConformalEnds
end CircleDomainRigidity

end

end OAI
