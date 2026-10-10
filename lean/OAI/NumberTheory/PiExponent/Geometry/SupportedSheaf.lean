import Mathlib

namespace OAI


namespace PiExponentSeshadri.FiniteSupport
noncomputable section
open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite AlgebraicGeometry
variable {X : TopCat.{0}}

lemma sections_subsingleton_of_stalks (F : X.Sheaf AddCommGrpCat.{0})
    (U : Opens X) (h : ∀ x ∈ U, Subsingleton (F.presheaf.stalk x)) :
    Subsingleton (F.obj.obj (op U)) := by
  constructor
  intro s t
  apply TopCat.Presheaf.section_ext F U s t
  intro x hx
  let := h x hx
  exact Subsingleton.elim _ _

lemma finite_closed_support_restriction_surjective
    (F : X.Sheaf AddCommGrpCat.{0}) (S : Set X) (hfin : S.Finite)
    (hclosed : ∀ x ∈ S, IsClosed ({x} : Set X))
    (hsupp : ∀ x ∉ S, Subsingleton (F.presheaf.stalk x))
    {U V : Opens X} (i : V ⟶ U) : Function.Surjective (F.obj.map i.op) := by
  classical
  intro s
  have hcS : IsClosed (S ∩ V) := by
    rw [← Set.biUnion_of_singleton (S ∩ (V : Set X))]
    exact (hfin.subset Set.inter_subset_left).isClosed_biUnion
      (fun x hx => hclosed x hx.1)
  let W : Opens X := U ⊓ ⟨(S ∩ V)ᶜ,hcS.isOpen_compl⟩
  let D : Bool → Opens X := fun b => if b then V else W
  let e : ∀ b, D b ⟶ U := fun b => homOfLE (by
    cases b
    · exact inf_le_left
    · exact i.le)
  have hcover : U ≤ ⨆ b, D b := by
    intro x hx
    by_cases hv : x ∈ V
    · exact Opens.mem_iSup.mpr ⟨true,hv⟩
    · exact Opens.mem_iSup.mpr ⟨false,hx,fun h => hv h.2⟩
  let t : ∀ b, F.obj.obj (op (D b)) := fun b => match b with
    | true => s
    | false => 0
  have hz : ∀ b c, b ≠ c → Subsingleton (F.obj.obj (op (D b ⊓ D c))) := by
    intro b c hbc
    apply sections_subsingleton_of_stalks
    intro x hx
    apply hsupp
    intro hs
    cases b <;> cases c
    · exact hbc rfl
    · exact hx.1.2 ⟨hs,hx.2⟩
    · exact hx.2.2 ⟨hs,hx.1⟩
    · exact hbc rfl
  have hcomp : TopCat.Presheaf.IsCompatible F.obj D t := by
    intro b c
    by_cases he : b = c
    · subst c; rfl
    · let := hz b c he
      exact Subsingleton.elim _ _
  obtain ⟨a,ha,_⟩ := F.existsUnique_gluing' D U e hcover t hcomp
  exact ⟨a,ha true⟩

lemma finite_closed_support_flasque (F : X.Sheaf AddCommGrpCat.{0})
    (S : Set X) (hfin : S.Finite)
    (hclosed : ∀ x ∈ S, IsClosed ({x} : Set X))
    (hsupp : ∀ x ∉ S, Subsingleton (F.presheaf.stalk x)) : F.IsFlasque where
  epi i := (AddCommGrpCat.epi_iff_surjective _).mpr
    (finite_closed_support_restriction_surjective F S hfin hclosed hsupp i.unop)

lemma finite_closed_support_global_germ_surjective
    (F : X.Sheaf AddCommGrpCat.{0}) (S : Set X) (hfin : S.Finite)
    (hclosed : ∀ x ∈ S, IsClosed ({x} : Set X))
    (hsupp : ∀ x ∉ S, Subsingleton (F.presheaf.stalk x)) (x : X) :
    Function.Surjective (F.presheaf.germ ⊤ x trivial) := by
  intro z
  obtain ⟨U,hx,s,hs⟩ := F.presheaf.exists_germ_eq z
  obtain ⟨t,ht⟩ := finite_closed_support_restriction_surjective F S hfin hclosed hsupp
    (homOfLE (le_top : U ≤ ⊤)) s
  refine ⟨t,?_⟩
  rw [← hs, ← ht, TopCat.Presheaf.germ_res_apply]

end
end PiExponentSeshadri.FiniteSupport

end OAI
