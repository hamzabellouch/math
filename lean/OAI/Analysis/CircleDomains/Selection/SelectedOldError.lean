import OAI.Analysis.CircleDomains.Transfer.ModelFlattenedSelection
import OAI.Analysis.CircleDomains.Sobolev.IndicatorL2Energy

namespace OAI

/-! The selected old coordinates obey the requested uniform and gradient
norm errors, after choosing the squared energy budget below the tolerance. -/
open Set Function Filter MeasureTheory
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity
namespace CompactScalarModel
variable {G : Set Sphere} {m : ℕ} {u : Fin m → EuclideanPlane → ℝ}

 theorem FlattenedSourceSelection.old_errors (M : CompactScalarModel G u)
    {R d A L e δ : ℝ} {H : ControlledHeight R d}
    {Wold : ∀ i, DeGiorgi.MemW1pWitness 2 (u i) (physicalPlaneDomain G)}
    (S : FlattenedSourceSelection M H Wold A L e e)
    (hδ : 0 < δ) (heδ : e ≤ δ) (heδsq : e ≤ δ^2) (i : Fin m) :
    (∀ x, |flattenValues (S.oldValues i) (u i x)-u i x| < δ) ∧
    (eLpNorm (fun x => (S.oldWitness i).weakGrad x-(Wold i).weakGrad x) 2
      (volume.restrict (physicalPlaneDomain G))).toReal < δ := by
  refine ⟨fun x => (S.old_close i (u i x)).trans_le heδ,?_⟩
  have hm := ((S.oldWitness i).weakGrad_memLp.sub (Wold i).weakGrad_memLp).norm
  have hE : (∫⁻ x in physicalPlaneDomain G,
      ENNReal.ofReal (‖(S.oldWitness i).weakGrad x-(Wold i).weakGrad x‖^2)) <
        ENNReal.ofReal (δ^2) := (S.old_error i).trans_le (ENNReal.ofReal_le_ofReal heδsq)
  have hi := indicator_L2_norm_lt_of_energy_lt hm MeasurableSet.univ hδ
    (by simpa only [Measure.restrict_univ, Pi.sub_apply] using hE)
  have hnorm : AEStronglyMeasurable
      (fun x => (S.oldWitness i).weakGrad x-(Wold i).weakGrad x)
      (volume.restrict (physicalPlaneDomain G)) :=
    ((S.oldWitness i).weakGrad_memLp.sub (Wold i).weakGrad_memLp).aestronglyMeasurable
  have hi' : (eLpNorm (fun x => ‖(S.oldWitness i).weakGrad x-(Wold i).weakGrad x‖) 2
      (volume.restrict (physicalPlaneDomain G))).toReal < δ := by
    simpa only [indicator_univ, Pi.sub_apply] using hi
  rwa [eLpNorm_norm _ hnorm] at hi'

end CompactScalarModel
end CircleDomainRigidity

end

end OAI
