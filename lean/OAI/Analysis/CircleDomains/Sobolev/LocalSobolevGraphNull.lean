import OAI.Analysis.CircleDomains.Sobolev.SobolevGraphNull
import OAI.Analysis.CircleDomains.Sobolev.LocalSobolevLipschitzCover

namespace OAI

/-! The graph-null result localizes to continuous W1,2_loc functions on
bounded null base sets by a genuine compact smooth cutoff. -/
open Set Function Filter MeasureTheory Metric Bornology
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity

lemma locally_sobolev_graph_null {u : EuclideanPlane → ℝ} (hu : Continuous u)
    {V : EuclideanPlane → EuclideanPlane} (hw : DeGiorgi.HasWeakGrad V u univ)
    (hLp : ∀ R i, MemLp (fun p => V p i) 2 (volume.restrict (ball 0 R)))
    {E : Set EuclideanPlane} (hE : MeasurableSet E) (hEb : IsBounded E)
    (hnull : volume E = 0) :
    (μH[2] : Measure GraphSpace) (sobolevGraph u '' E) = 0 := by
  have hK : IsCompact (closure E) := hEb.isCompact_closure
  obtain ⟨R,hR⟩ := hK.isBounded.subset_ball 0
  obtain ⟨η,O,hη,hsη,_,hηR,_,hKO,hone⟩ :=
    exists_smooth_compact_cutoff_one_near hK isOpen_ball hR
  let w : EuclideanPlane → ℝ := fun p => η p*u p
  obtain ⟨W⟩ := exists_global_compact_cutoff_witness isOpen_ball
    (scalarBallWeakWitness hu hw hLp R).memW1p hη hsη hηR
  have heq : EqOn (sobolevGraph w) (sobolevGraph u) E := by
    intro x hx
    change (euclideanPlaneCoordinates x,w x) = (euclideanPlaneCoordinates x,u x)
    apply Prod.ext
    · rfl
    · change η x*u x = u x
      rw [hone x (hKO (subset_closure hx)),one_mul]
  rw [← Set.image_congr heq]
  exact compact_sobolev_graph_null (hη.continuous.mul hu) W hsη.mul_right hE hnull

end CircleDomainRigidity

end

end OAI
