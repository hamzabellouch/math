import Mathlib
import OAI.Probability.CriticalPercolation.Growth.CosetGeometry
import OAI.Probability.CriticalPercolation.Growth.CosetBounded

namespace OAI

section
noncomputable section
open Set Function
open scoped Classical Pointwise

namespace CriticalPercolation.RelativeGrowth
variable {A : Type*} [Group A]

lemma normalized_generators (K : Subgroup A) (S : Set A)
    (h1 : (1:A)∈S) (hi : S⁻¹=S) (hgen : Subgroup.closure S=⊤)
    (hK : Bounded S (K:Set A)) :
    ∃ P : Presentation A, P.K=K ∧ Bounded S P.S ∧ S⊆P.S := by
  let T := (K:Set A)*S*(K:Set A)
  have hs : S⊆T := by
    intro s hs
    have hh := Set.mul_mem_mul (Set.mul_mem_mul K.one_mem hs) K.one_mem
    simpa only [one_mul,mul_one] using hh
  have hT1 : (1:A)∈T := hs h1
  have hTi : T⁻¹=T := by
    dsimp [T]
    rw [mul_inv_rev,mul_inv_rev,inv_coe_set,hi,mul_assoc]
  have hTgen : Subgroup.closure T=⊤ := top_unique (hgen ▸ Subgroup.closure_mono hs)
  have hleft : (K:Set A)*T⊆T := by
    rintro _ ⟨k,hk,_,⟨_,⟨l,hl,s,hs,rfl⟩,m,hm,rfl⟩,rfl⟩
    have hh := Set.mul_mem_mul (Set.mul_mem_mul (K.mul_mem hk hl) hs) hm
    simpa only [T,mul_assoc] using hh
  refine ⟨⟨K,T,hT1,hTi,hTgen,hleft⟩,rfl,?_,hs⟩
  exact (hK.mul ⟨1,by simp⟩).mul hK

end CriticalPercolation.RelativeGrowth
end
end

end OAI
