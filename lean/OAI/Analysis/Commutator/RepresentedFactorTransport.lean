import Mathlib
import OAI.Analysis.Commutator.BicommutantRange
import OAI.Analysis.Commutator.FactorCorner
import OAI.Analysis.Commutator.VonNeumannCStar

namespace OAI

noncomputable section

section

noncomputable section

attribute [-instance] NonUnitalStarSubalgebra.nonUnitalCStarAlgebra

namespace Kadison.FactorCorner

variable {H G : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]

variable (M : VonNeumannAlgebra H)

lemma commutant_factor (hM : IsFactor M) : IsFactor M.commutant := by
  intro z hz hzc
  have hzM : z∈M := by
    have hc : z∈M.commutant.commutant := by
      rw [←SetLike.mem_coe,VonNeumannAlgebra.coe_commutant]
      exact hzc
    simpa only [VonNeumannAlgebra.commutant_commutant] using hc
  apply hM z hzM
  simpa only [←SetLike.mem_coe,VonNeumannAlgebra.coe_commutant] using hz

lemma image_factor (hM : IsFactor M) (φ : M →⋆ₐ[ℂ] (G →L[ℂ] G))
    (hinj : Function.Injective φ)
    (hclosed : Set.centralizer (Set.centralizer (Set.range φ))=Set.range φ) :
    IsFactor (BicommutantRange.ofStarHom φ hclosed) := by
  intro z hz hzc
  obtain ⟨a,rfl⟩ := hz
  have hac : (a:H →L[ℂ] H)∈Set.centralizer (M : Set (H →L[ℂ] H)) := by
    intro b hb
    have he : (⟨b,hb⟩:M)*a=a*⟨b,hb⟩ := by
      apply hinj
      simp only [map_mul]
      exact hzc _ (Set.mem_range_self (⟨b,hb⟩:M))
    exact congrArg (fun c : M => (c:H →L[ℂ] H)) he
  obtain ⟨c,hc⟩ := hM a a.property hac
  have ha : a=c • (1:M) := Subtype.ext hc
  refine ⟨c,?_⟩
  change φ a=c • 1
  rw [ha,map_smul,map_one]

end Kadison.FactorCorner

end

end
end

end OAI
