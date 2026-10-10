import Mathlib

namespace OAI

namespace PiExponent.HomogeneousSubmoduleGrading
noncomputable section
open DirectSum
variable {R M σM : Type*} [Ring R] [AddCommGroup M] [Module R M]
  [SetLike σM M] [AddSubgroupClass σM M]
  (𝓜 : ℤ → σM) [DirectSum.Decomposition 𝓜]
  (K : Submodule R M) (hK : K.IsHomogeneous 𝓜)

def piece (_hK : K.IsHomogeneous 𝓜) (d : ℤ) : AddSubgroup K where
  carrier := {m | (m : M) ∈ 𝓜 d}
  zero_mem' := zero_mem _
  add_mem' := fun hm hn => add_mem hm hn
  neg_mem' := fun hm => neg_mem hm

def component (m : K) (d : ℤ) : piece 𝓜 K hK d :=
  ⟨⟨DirectSum.decompose 𝓜 (m : M) d, hK d m.property⟩,
    (DirectSum.decompose 𝓜 (m : M) d).property⟩

def decompositionMap : K →+ ⨁ d, piece 𝓜 K hK d where
  toFun m := by
    classical
    exact DFinsupp.mk' (component 𝓜 K hK m) (Trunc.mk
    ⟨(DirectSum.decompose 𝓜 (m : M)).support.val, fun d => by
      classical
      by_cases hd : d ∈ (DirectSum.decompose 𝓜 (m : M)).support
      · exact Or.inl hd
      · right
        apply Subtype.ext
        apply Subtype.ext
        change (DirectSum.decompose 𝓜 (m : M) d : M) = 0
        rw [DFinsupp.notMem_support_iff.mp hd]
        rfl⟩)
  map_zero' := by
    ext d
    change (DirectSum.decompose 𝓜 (0 : M) d : M) = 0
    rw [DirectSum.decompose_zero]
    rfl
  map_add' m n := by
    ext d
    change (DirectSum.decompose 𝓜 ((m : M) + (n : M)) d : M) =
      (DirectSum.decompose 𝓜 (m : M) d : M) + (DirectSum.decompose 𝓜 (n : M) d : M)
    rw [DirectSum.decompose_add]
    rfl

@[simp] theorem decompositionMap_apply (m : K) (d : ℤ) :
    (((decompositionMap 𝓜 K hK m) d : K) : M) =
      (DirectSum.decompose 𝓜 (m : M) d : M) := rfl

theorem decompositionMap_injective : Function.Injective (decompositionMap 𝓜 K hK) := by
  intro m n h
  apply Subtype.ext
  apply (DirectSum.decompose 𝓜).injective
  ext d
  exact congrArg (fun z : ⨁ d, piece 𝓜 K hK d => ((z d : K) : M)) h

theorem decompositionMap_homogeneous (d : ℤ) (m : piece 𝓜 K hK d) :
    decompositionMap 𝓜 K hK m.val = DirectSum.of (fun d => piece 𝓜 K hK d) d m := by
  classical
  ext e
  by_cases he : d = e
  · subst e
    rw [DirectSum.of_eq_same]
    exact DirectSum.decompose_of_mem_same 𝓜 m.property
  · rw [DirectSum.of_eq_of_ne _ _ _ (Ne.symm he)]
    exact DirectSum.decompose_of_mem_ne 𝓜 m.property he

instance decomposition : DirectSum.Decomposition (piece 𝓜 K hK) := by
  classical
  have hr : (decompositionMap 𝓜 K hK).comp (DirectSum.coeAddMonoidHom (piece 𝓜 K hK)) =
      AddMonoidHom.id _ := by
    apply DirectSum.addHom_ext
    intro d m
    simp only [AddMonoidHom.comp_apply, DirectSum.coeAddMonoidHom_of,
      AddMonoidHom.id_apply, decompositionMap_homogeneous]
  apply DirectSum.Decomposition.ofAddHom (piece 𝓜 K hK) (decompositionMap 𝓜 K hK) ?_ hr
  apply AddMonoidHom.ext
  intro m
  apply decompositionMap_injective 𝓜 K hK
  exact DFunLike.congr_fun hr (decompositionMap 𝓜 K hK m)

theorem subtype_degree_compatible (d : ℤ) (m : K) :
    K.subtype (DirectSum.decompose (piece 𝓜 K hK) m d : K) =
      (DirectSum.decompose 𝓜 (K.subtype m) d : M) := rfl

variable {σR : Type*} [SetLike σR R] [AddSubgroupClass σR R]
  (𝒜 : ℤ → σR) [SetLike.GradedSMul 𝒜 𝓜]

instance gradedSMul : SetLike.GradedSMul 𝒜 (piece 𝓜 K hK) where
  smul_mem := by
    intro i d a m ha hm
    change a • (m : M) ∈ 𝓜 (i + d)
    exact SetLike.GradedSMul.smul_mem ha (show (m : M) ∈ 𝓜 d from hm)

end
end PiExponent.HomogeneousSubmoduleGrading

end OAI
