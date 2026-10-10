import OAI.NumberTheory.CubicMoment.Theta.CubicThetaEnergyPencilKernel
import Mathlib.Analysis.Normed.Operator.Compact.FredholmAlternative

namespace OAI

/-! The elementary Fredholm alternative needed for the compactly
corrected energy pencil: injectivity upgrades to invertibility. -/
noncomputable section
namespace CubicFirstMoment

lemma cubicThetaCompactPerturbation_unit
    {H : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H] [CompleteSpace H]
    (A K : H →L[ℂ] H) (hK : IsCompactOperator K) (hU : IsUnit (A+K))
    (hinj : Function.Injective A) : IsUnit A := by
  let U := A+K
  let L : H →L[ℂ] H := (Ring.inverse U).comp K
  have hL : IsCompactOperator L := hK.clm_comp (Ring.inverse U)
  have hfactor : U*(1-L)=A := by
    change U*(1-Ring.inverse U*K)=A
    rw [mul_sub,mul_one,← mul_assoc,Ring.mul_inverse_cancel _ hU,one_mul]
    dsimp [U]
    abel
  have hn : ¬Module.End.HasEigenvalue (L : Module.End ℂ H) 1 := by
    intro he
    obtain ⟨v,hv,hv0⟩ := he.exists_hasEigenvector
    have heq : L v=v := by
      have hh := Module.End.mem_eigenspace_iff.mp hv
      change L v=(1:ℂ) • v at hh
      simpa only [one_smul] using hh
    have hav : A v=0 := by
      rw [← hfactor]
      change U (v-L v)=0
      rw [heq,sub_self,map_zero]
    exact hv0 (hinj (hav.trans (map_zero A).symm))
  have hu : IsUnit (1-L) := by
    have hr := (hL.hasEigenvalue_or_mem_resolventSet (one_ne_zero : (1:ℂ)≠0)).resolve_left hn
    simpa only [spectrum.mem_resolventSet_iff,map_one] using hr
  rw [← hfactor]
  exact hU.mul hu

end CubicFirstMoment

end

end OAI
