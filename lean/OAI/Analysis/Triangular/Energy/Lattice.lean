import OAI.Analysis.Triangular.Energy.Mixtures

namespace OAI

noncomputable section
open scoped BigOperators
namespace TriangularUniversal
lemma triangularPoint_eq_zero_iff (v : ℤ × ℤ) : triangularPoint v=0 ↔ v=0 := by
  rw [← triangularPoint_zero]
  exact triangularPoint_injective.eq_iff

def nonzeroLatticeEquiv : {v : ℤ × ℤ // v≠0} ≃ NonzeroSite := Equiv.ofBijective
  (fun v => ⟨triangularPoint v.val,⟨⟨v.val,rfl⟩,fun h => v.property ((triangularPoint_eq_zero_iff _).mp h)⟩⟩)
  (by
    constructor
    · intro v w he
      apply Subtype.ext
      exact triangularPoint_injective (congrArg Subtype.val he)
    · intro x
      obtain ⟨v,hv⟩ := x.property.1
      refine ⟨⟨v,?_⟩,?_⟩
      · intro h
        exact x.property.2 (hv.symm.trans ((triangularPoint_eq_zero_iff _).mpr h))
      · exact Subtype.ext hv)
lemma latticeEnergy_nonzero_index (g : ℝ → ℝ) :
    latticeEnergy g=∑' v : {v : ℤ × ℤ // v≠0}, ENNReal.ofReal (g (‖triangularPoint v.val‖^2)) := by
  exact (nonzeroLatticeEquiv.tsum_eq (fun x : NonzeroSite => ENNReal.ofReal (g (‖x.val‖^2)))).symm
end TriangularUniversal
end

end OAI
