import Mathlib

namespace OAI

namespace PiExponent.ShiftedFreeGrading
noncomputable section
open scoped BigOperators
open DirectSum
variable {A J σA : Type*} [AddCommGroup A] [Fintype J]
  [SetLike σA A] [AddSubgroupClass σA A]
  (𝒜 : ℤ → σA) [DirectSum.Decomposition 𝒜] (w : J → ℤ)

def piece (d : ℤ) : AddSubgroup (J → A) where
  carrier := {f | ∀ j, f j ∈ 𝒜 (d - w j)}
  zero_mem' := fun _j => zero_mem _
  add_mem' := fun hf hg j => add_mem (hf j) (hg j)
  neg_mem' := fun hf j => neg_mem (hf j)

def component (f : J → A) (d : ℤ) : piece 𝒜 w d :=
  ⟨fun j => (DirectSum.decompose 𝒜 (f j) (d - w j) : A),
    fun j => (DirectSum.decompose 𝒜 (f j) (d - w j)).property⟩

def support (f : J → A) : Finset ℤ := by
  classical
  exact Finset.univ.biUnion fun j =>
    (DirectSum.decompose 𝒜 (f j)).support.image (fun d => d + w j)

theorem component_eq_zero_of_not_mem (f : J → A) (d : ℤ)
    (hd : d ∉ support 𝒜 w f) : component 𝒜 w f d = 0 := by
  classical
  apply Subtype.ext
  funext j
  change (DirectSum.decompose 𝒜 (f j) (d - w j) : A) = 0
  have hh : d - w j ∉ (DirectSum.decompose 𝒜 (f j)).support := by
    intro h
    apply hd
    exact Finset.mem_biUnion.mpr ⟨j, Finset.mem_univ _,
      Finset.mem_image.mpr ⟨d - w j, h, sub_add_cancel _ _⟩⟩
  rw [DFinsupp.notMem_support_iff.mp hh]
  rfl

def decompositionMap : (J → A) →+ ⨁ d, piece 𝒜 w d where
  toFun f := DFinsupp.mk' (component 𝒜 w f)
    (Trunc.mk ⟨(support 𝒜 w f).val, fun d => by
      classical
      by_cases hd : d ∈ support 𝒜 w f
      · exact Or.inl hd
      · exact Or.inr (component_eq_zero_of_not_mem 𝒜 w f d hd)⟩)
  map_zero' := by
    ext d j
    change (DirectSum.decompose 𝒜 (0 : A) (d - w j) : A) = 0
    rw [DirectSum.decompose_zero]
    rfl
  map_add' f g := by
    ext d j
    change (DirectSum.decompose 𝒜 (f j + g j) (d - w j) : A) =
      (DirectSum.decompose 𝒜 (f j) (d - w j) : A) +
      (DirectSum.decompose 𝒜 (g j) (d - w j) : A)
    rw [DirectSum.decompose_add]
    rfl

@[simp] theorem decompositionMap_apply (f : J → A) (d : ℤ) (j : J) :
    (decompositionMap 𝒜 w f d : J → A) j =
      (DirectSum.decompose 𝒜 (f j) (d - w j) : A) := rfl

theorem decompositionMap_injective : Function.Injective (decompositionMap 𝒜 w) := by
  intro f g h
  funext j
  apply (DirectSum.decompose 𝒜).injective
  ext d
  have hh := congrArg (fun z : ⨁ d, piece 𝒜 w d => (z (d + w j) : J → A) j) h
  change (DirectSum.decompose 𝒜 (f j) (d + w j - w j) : A) =
    (DirectSum.decompose 𝒜 (g j) (d + w j - w j) : A) at hh
  rw [show d + w j - w j = d by omega] at hh
  exact hh

theorem decompositionMap_homogeneous (d : ℤ) (f : piece 𝒜 w d) :
    decompositionMap 𝒜 w f.val = DirectSum.of (fun d => piece 𝒜 w d) d f := by
  classical
  ext e j
  by_cases he : d = e
  · subst e
    rw [DirectSum.of_eq_same]
    exact DirectSum.decompose_of_mem_same 𝒜 (f.property j)
  · rw [DirectSum.of_eq_of_ne _ _ _ (Ne.symm he)]
    change (DirectSum.decompose 𝒜 (f.val j) (e - w j) : A) = 0
    exact DirectSum.decompose_of_mem_ne 𝒜 (f.property j) (by omega)

instance decomposition : DirectSum.Decomposition (piece 𝒜 w) := by
  classical
  have hr : (decompositionMap 𝒜 w).comp (DirectSum.coeAddMonoidHom (piece 𝒜 w)) =
      AddMonoidHom.id _ := by
    apply DirectSum.addHom_ext
    intro d f
    simp only [AddMonoidHom.comp_apply, DirectSum.coeAddMonoidHom_of,
      AddMonoidHom.id_apply, decompositionMap_homogeneous]
  apply DirectSum.Decomposition.ofAddHom (piece 𝒜 w) (decompositionMap 𝒜 w) ?_ hr
  apply AddMonoidHom.ext
  intro f
  apply decompositionMap_injective 𝒜 w
  exact DFunLike.congr_fun hr (decompositionMap 𝒜 w f)

@[simp] theorem decompose_apply (f : J → A) (d : ℤ) (j : J) :
    (DirectSum.decompose (piece 𝒜 w) f d : J → A) j =
      (DirectSum.decompose 𝒜 (f j) (d - w j) : A) := rfl

end
end PiExponent.ShiftedFreeGrading

end OAI
