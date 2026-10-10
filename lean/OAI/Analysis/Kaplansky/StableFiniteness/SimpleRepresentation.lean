import OAI.Analysis.Kaplansky.Main
import OAI.Analysis.Kaplansky.StableFiniteness.StateExists
import Mathlib.Analysis.CStarAlgebra.GelfandNaimarkSegal

namespace OAI

noncomputable section

namespace KaplanskyConsequences

open scoped ComplexOrder InnerProductSpace
attribute [local instance] CStarAlgebra.spectralOrder CStarAlgebra.spectralOrderedRing
universe u v
variable {A : Type u} {B : Type v} [CStarAlgebra A] [CStarAlgebra B]

def homKernel (f : A →⋆ₐ[ℂ] B) : ClosedStarIdeal A where
  carrier := {a | f a=0}
  zero_mem' := map_zero f
  add_mem' := by intros; dsimp at *; simp_all only [map_add,add_zero]
  mul_mem' := by intros; dsimp at *; simp_all only [map_mul,zero_mul]
  smul_mem' := by intros; dsimp at *; simp_all only [map_smul,smul_zero]
  star_mem' := by intros; dsimp at *; simp_all only [map_star,star_zero]
  mul_mem_left := by intro a b hb; change f (a*b)=0; rw [map_mul,hb,mul_zero]
  mul_mem_right := by intro a b ha; change f (a*b)=0; rw [map_mul,ha,zero_mul]
  closed := isClosed_eq (map_continuous f) continuous_const

lemma simple_hom_injective [Nontrivial B] (hA : CStarSimple A) (f : A →⋆ₐ[ℂ] B) :
    Function.Injective f := by
  rcases hA (homKernel f) with hzero | hwhole
  · intro a b hab
    apply sub_eq_zero.mp
    apply hzero
    change f (a-b)=0
    rw [map_sub,hab,sub_self]
  · have h := hwhole 1
    change f 1=0 at h
    rw [map_one] at h
    exact (one_ne_zero h).elim

lemma gns_nontrivial (f : A →ₚ[ℂ] ℂ) (hf : f 1=1) : Nontrivial f.GNS := by
  apply nontrivial_of_ne ((f.toPreGNS 1 : f.PreGNS) : f.GNS) 0
  intro h
  have he := congrArg norm h
  rw [UniformSpace.Completion.norm_coe,norm_zero] at he
  have hs := f.preGNS_norm_sq (f.toPreGNS 1)
  apply (zero_ne_one : (0:ℂ)≠1)
  simpa only [he,Complex.ofReal_zero,zero_pow (by decide : 2≠0),f.ofPreGNS_toPreGNS,
    star_one,one_mul,hf] using hs

theorem simple_faithful_representation [Nontrivial A] (hA : CStarSimple A) :
    ∃ (H : Type u) (instH : NormedAddCommGroup H) (innerH : InnerProductSpace ℂ H),
      letI := instH
      letI := innerH
      ∃ (completeH : CompleteSpace H),
        letI := completeH
        ∃ ρ : A →⋆ₐ[ℂ] (H →L[ℂ] H), Function.Injective ρ := by
  obtain ⟨f,hf⟩ := normalized_positive_functional_exists (A:=A)
  let : Nontrivial f.GNS := gns_nontrivial f hf
  exact ⟨f.GNS,inferInstance,inferInstance,inferInstance,f.gnsStarAlgHom,
    simple_hom_injective hA f.gnsStarAlgHom⟩


end KaplanskyConsequences

end

end OAI
