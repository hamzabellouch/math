import OAI.Analysis.CircleDomains.Sobolev.SobolevRepresentative
import OAI.Analysis.CircleDomains.Sobolev.LocalComplexWitness

namespace OAI

/-! Borel L² representatives of the two actual global weak derivatives.
Changing these representatives preserves the Sobolev witness. -/
open Set Function Filter MeasureTheory
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity

 def scalarGradientRepresentative {u : EuclideanPlane → ℝ}
    (W : DeGiorgi.MemW1pWitness 2 u univ) (i : Fin 2) :
    Lp ℝ 2 (volume : Measure EuclideanPlane) :=
  (show MemLp (fun p => W.weakGrad p i) 2 volume by
    simpa only [Measure.restrict_univ] using W.weakGrad_component_memLp i).toLp _

 theorem scalarGradientRepresentative_ae {u : EuclideanPlane → ℝ}
    (W : DeGiorgi.MemW1pWitness 2 u univ) (i : Fin 2) :
    scalarGradientRepresentative W i =ᵐ[volume] (fun p => W.weakGrad p i) :=
  MemLp.coeFn_toLp _

 def borelSobolevWitness {u : EuclideanPlane → ℝ}
    (W : DeGiorgi.MemW1pWitness 2 u univ) : DeGiorgi.MemW1pWitness 2 u univ where
  memLp := W.memLp
  weakGrad := fun p => WithLp.toLp 2 (fun i => scalarGradientRepresentative W i p)
  weakGrad_component_memLp := fun i => (Lp.memLp (scalarGradientRepresentative W i)).restrict univ
  isWeakGrad := by
    intro i
    apply (W.isWeakGrad i).congr_ae (EventuallyEq.rfl)
    simpa only [Measure.restrict_univ] using (scalarGradientRepresentative_ae W i).symm

end CircleDomainRigidity

end

end OAI
