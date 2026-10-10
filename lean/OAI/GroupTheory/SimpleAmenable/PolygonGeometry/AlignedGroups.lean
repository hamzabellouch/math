import Mathlib
import OAI.GroupTheory.SimpleAmenable.CentralCovers.TranslatedDisjoint

namespace OAI

section
section
open scoped symmDiff
namespace SimpleAmenable
open scoped commutatorElement
open scoped commutatorElement
section AlignedGroups

variable {A H : Type*} [Group A] [Group H] {B : Type*}

noncomputable def alignedGroup (t : A →* H) (x : B → H) (P : B → Prop) : Subgroup H :=
  Subgroup.closure {y | ∃ b, P b ∧ ∃ u, y = t u*x b*(t u)⁻¹}

theorem alignedGroup_generator (t : A →* H) (x : B → H) (P : B → Prop)
    (b : B) (hb : P b) (u : A) : t u*x b*(t u)⁻¹ ∈ alignedGroup t x P :=
  Subgroup.subset_closure ⟨b,hb,u,rfl⟩

theorem alignedGroup_input (t : A →* H) (x : B → H) (P : B → Prop)
    (b : B) (hb : P b) : x b ∈ alignedGroup t x P := by
  simpa only [map_one,inv_one,one_mul,mul_one] using alignedGroup_generator t x P b hb 1

theorem alignedGroup_conjugate (t : A →* H) (x : B → H) (P : B → Prop)
    (u : A) {y : H} (hy : y ∈ alignedGroup t x P) :
    t u*y*(t u)⁻¹ ∈ alignedGroup t x P := by
  let f : H →* H := (MulAut.conj (t u)).toMonoidHom
  have hh : alignedGroup t x P ≤ (alignedGroup t x P).comap f := by
    apply (Subgroup.closure_le _).mpr
    rintro z ⟨b,hb,v,rfl⟩
    change t u*(t v*x b*(t v)⁻¹)*(t u)⁻¹ ∈ alignedGroup t x P
    have he : t u*(t v*x b*(t v)⁻¹)*(t u)⁻¹ = t (u*v)*x b*(t (u*v))⁻¹ := by
      rw [map_mul]; group
    rw [he]
    exact alignedGroup_generator t x P b hb (u*v)
  exact hh hy

theorem alignedGroup_commute (t : A →* H) (x : B → H) (P Q : B → Prop)
    (hc : ∀ b, P b → ∀ c, Q c → ∀ u v,
      Commute (t u*x b*(t u)⁻¹) (t v*x c*(t v)⁻¹)) :
    ∀ g ∈ alignedGroup t x P, ∀ h ∈ alignedGroup t x Q, Commute g h := by
  have hh : alignedGroup t x P ≤ Subgroup.centralizer (alignedGroup t x Q) := by
    apply (Subgroup.closure_le _).mpr
    rintro g ⟨b,hb,u,rfl⟩
    rw [alignedGroup,Subgroup.centralizer_closure]
    intro h hh
    obtain ⟨c,hc',v,rfl⟩ := hh
    exact (hc b hb c hc' u v).symm.eq
  intro g hg h hmem
  exact (hh hg h hmem).symm

theorem alignedGroup_map {G : Type*} [Group G] (q : H →* G)
    (t : A →* H) (x : B → H) (P : B → Prop) :
    (alignedGroup t x P).map q = alignedGroup (q.comp t) (fun b => q (x b)) P := by
  rw [alignedGroup,MonoidHom.map_closure]
  congr 1
  ext y
  constructor
  · rintro ⟨z,⟨b,hb,u,rfl⟩,rfl⟩
    exact ⟨b,hb,u,by simp⟩
  · rintro ⟨b,hb,u,rfl⟩
    exact ⟨t u*x b*(t u)⁻¹,⟨b,hb,u,rfl⟩,by simp⟩

end AlignedGroups

section SourceAlignedGroups

def SmallConditional (m : ℕ) := Fin 5 × {σ : Equiv.Perm (Fin (m+1)) //
  σ ∈ alternatingGroup (Fin (m+1)) ∧ σ.support.card ≤ 5}

instance (m : ℕ) : Finite (SmallConditional m) := by unfold SmallConditional; infer_instance

noncomputable def sourceAlignedGroup (a : ℕ) (r : CutRing) (m : ℕ) (hm : 2 ≤ m)
    (M : ℕ) (t : Multiplicative (FreeAbelianGroup (Fin m × Fin 2)) →*
      BoundedRelationCover M (alternatingGenerator a r m hm)) (I : Finset (Fin (m+1))) :
      Subgroup (BoundedRelationCover M (alternatingGenerator a r m hm)) :=
  alignedGroup t (fun b : SmallConditional m => PresentedGroup.of (Sum.inl b))
    (fun b => b.2.val.support ⊆ I)

theorem source_aligned_disjoint_eventually (a : ℕ) (r : CutRing) (m : ℕ)
    (hm : 2 ≤ m) (hm' : 10 < m+1) :
    ∃ L : ℕ, ∀ M : ℕ, L ≤ M →
      ∃ t : Multiplicative (FreeAbelianGroup (Fin m × Fin 2)) →*
          BoundedRelationCover M (alternatingGenerator a r m hm),
        (∀ i, t (Multiplicative.ofAdd (FreeAbelianGroup.of i)) = PresentedGroup.of (Sum.inr i)) ∧
        (coverMap M (alternatingGenerator a r m hm)).comp t = sourceLatticeMap a r m hm ∧
        ∀ (I J : Finset (Fin (m+1))), Disjoint I J →
          ∀ g ∈ sourceAlignedGroup a r m hm M t I,
          ∀ h ∈ sourceAlignedGroup a r m hm M t J, Commute g h := by
  obtain ⟨L,hL⟩ := source_translated_disjoint_eventually a r m hm hm'
  refine ⟨L,fun M hM => ?_⟩
  obtain ⟨t,ht,htq,hc⟩ := hL M hM
  refine ⟨t,ht,htq,?_⟩
  intro I J hIJ
  apply alignedGroup_commute
  intro b hb c hc' u v
  exact hc b.1 c.1 b.2 c.2 (hIJ.mono hb hc') u v

end SourceAlignedGroups

end SimpleAmenable
end
end

end OAI
