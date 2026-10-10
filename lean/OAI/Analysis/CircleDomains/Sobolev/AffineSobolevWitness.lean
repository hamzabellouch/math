import OAI.Analysis.CircleDomains.Sobolev.WeakGradientAffineRescale
import OAI.Analysis.CircleDomains.Sobolev.AffineLpTransport
import OAI.Analysis.KLS.Sobolev.Witnesses

namespace OAI

/-! Global Sobolev witnesses retain their actual gradient under affine
rescaling. This is the witness used in the local capacity application. -/
open Set Function MeasureTheory
open scoped ENNReal
noncomputable section
namespace CircleDomainRigidity

def affineSobolevWitness {u : EuclideanPlane → ℝ}
    (W : DeGiorgi.MemW1pWitness 2 u univ) (a : EuclideanPlane)
    {s : ℝ} (hs : 0 < s) :
    DeGiorgi.MemW1pWitness 2 (fun x => u (a+s • x)) univ where
  memLp := by
    simp only [Measure.restrict_univ] at *
    exact memLp_planarAffine (by simpa using W.memLp) a hs
  weakGrad := fun x => s • W.weakGrad (a+s • x)
  weakGrad_component_memLp := by
    intro i
    simp only [Measure.restrict_univ, PiLp.smul_apply, smul_eq_mul]
    exact (memLp_planarAffine (by simpa using W.weakGrad_component_memLp i) a hs).const_mul s
  isWeakGrad := weakGradient_planarAffine W.isWeakGrad a hs

end CircleDomainRigidity

end

end OAI
