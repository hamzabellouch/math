import Mathlib
import OAI.GroupTheory.SimpleAmenable.PolygonGeometry.LiftedTranslationOrbits
import OAI.GroupTheory.SimpleAmenable.Arithmetic.LatticeRange
import OAI.GroupTheory.SimpleAmenable.Configurations.ConditionalTranslationStabilizers

namespace OAI

section
section
open scoped symmDiff
namespace SimpleAmenable
open scoped commutatorElement
open scoped commutatorElement
section TranslatedDisjoint

theorem generator_commutations_eventually {α G : Type*} [Finite α] [Group G]
    (f : α → G) :
    ∃ L : ℕ, ∀ M : ℕ, L ≤ M → ∀ i j, Commute (f i) (f j) →
      Commute (PresentedGroup.of i : BoundedRelationCover M f) (PresentedGroup.of j) := by
  let β := {p : α × α // Commute (f p.1) (f p.2)}
  obtain ⟨L,hL⟩ := finite_word_equalities_eventually f
    (fun p : β => FreeGroup.of p.val.1 * FreeGroup.of p.val.2)
    (fun p : β => FreeGroup.of p.val.2 * FreeGroup.of p.val.1)
    (fun p => by simpa only [map_mul,FreeGroup.lift_apply_of] using p.property.eq)
  refine ⟨L,fun M hM i j hij => ?_⟩
  have he := hL M hM ⟨(i,j),hij⟩
  change _*_ = _*_
  simpa only [map_mul,PresentedGroup.of] using he

theorem lifted_common_shift_commute {A G H : Type*} [CommGroup A] [Group G] [Group H]
    (q : A →* G) (t : A →* H) (x₁ x₂ : G) (y₁ y₂ : H)
    (hc₁ : ∀ k, Commute (q k) x₁ → Commute (t k) y₁)
    (hc₂ : ∀ k, Commute (q k) x₂ → Commute (t k) y₂)
    (hy : Commute y₁ y₂) (u v w : A)
    (hw₁ : q u*x₁*(q u)⁻¹ = q w*x₁*(q w)⁻¹)
    (hw₂ : q v*x₂*(q v)⁻¹ = q w*x₂*(q w)⁻¹) :
    Commute (t u*y₁*(t u)⁻¹) (t v*y₂*(t v)⁻¹) := by
  rw [lifted_translation_orbit_independent q t x₁ y₁ hc₁ u w hw₁,
    lifted_translation_orbit_independent q t x₂ y₂ hc₂ v w hw₂]
  change _*_ = _*_
  calc
    _ = t w*(y₁*y₂)*(t w)⁻¹ := by group
    _ = t w*(y₂*y₁)*(t w)⁻¹ := by rw [hy.eq]
    _ = _ := by group

theorem conditionalHom_disjoint_alphabets {a m : ℕ} (U V : polygonAlgebra a)
    (σ ρ : Equiv.Perm (Fin m)) (h : Disjoint σ.support ρ.support) :
    Commute (conditionalHom U σ) (conditionalHom V ρ) := by
  have hh := Equiv.Perm.Disjoint.commute (Equiv.Perm.disjoint_iff_disjoint_support.mpr h)
  change _*_ = _*_
  apply Subtype.ext
  apply Equiv.ext
  intro p
  change conditionalPerm U σ (conditionalPerm V ρ p) =
    conditionalPerm V ρ (conditionalPerm U σ p)
  have hp := DFunLike.congr_fun hh.eq p.1
  simp only [Equiv.Perm.mul_apply] at hp
  by_cases hu : p.2 ∈ U.val <;> by_cases hv : p.2 ∈ V.val
  all_goals simp [conditionalPerm,hu,hv,hp]

variable (a : ℕ) (r : CutRing) (m : ℕ) (hm : 2 ≤ m)

theorem source_disjoint_common_shift
    (σ ρ : Equiv.Perm (Fin (m+1))) (hd : Disjoint σ.support ρ.support)
    (hb : σ.support.card + ρ.support.card < m+1)
    (U V : polygonAlgebra a)
    (u v : Multiplicative (FreeAbelianGroup (Fin m × Fin 2))) :
    ∃ w, sourceLatticeFullMap a r m hm u * conditionalHom U σ *
        (sourceLatticeFullMap a r m hm u)⁻¹ =
      sourceLatticeFullMap a r m hm w * conditionalHom U σ *
        (sourceLatticeFullMap a r m hm w)⁻¹ ∧
      sourceLatticeFullMap a r m hm v * conditionalHom V ρ *
        (sourceLatticeFullMap a r m hm v)⁻¹ =
      sourceLatticeFullMap a r m hm w * conditionalHom V ρ *
        (sourceLatticeFullMap a r m hm w)⁻¹ := by
  classical
  obtain ⟨d,hu⟩ := sourceLatticeFullMap_translation a r m hm u
  obtain ⟨e,hv⟩ := sourceLatticeFullMap_translation a r m hm v
  have hcard : (σ.support ∪ ρ.support).card < (Finset.univ : Finset (Fin (m+1))).card := by
    simpa only [Finset.card_univ,Fintype.card_fin] using
      lt_of_le_of_lt (Finset.card_union_le _ _) hb
  obtain ⟨b,_,hbi⟩ := Finset.exists_mem_notMem_of_card_lt_card hcard
  let z : Fin (m+1) → CutRing × CutRing := fun i => if i ∈ σ.support then d i else e i
  obtain ⟨w,f,hw,hf⟩ := sourceLatticeFullMap_prescribed a r m hm
    (σ.support ∪ ρ.support) b hbi z
  refine ⟨w,?_,?_⟩
  · rw [hu,hw]
    apply conditional_conjugation_support
    intro i hi
    have hi' : i ∈ σ.support := Equiv.Perm.mem_support.mpr hi
    rw [hf i (Finset.mem_union_left _ hi')]
    simp only [z,ite_eq_left hi']
  · rw [hv,hw]
    apply conditional_conjugation_support
    intro i hi
    have hi' : i ∈ ρ.support := Equiv.Perm.mem_support.mpr hi
    have hin : i ∉ σ.support := fun h => Finset.disjoint_left.mp hd h hi'
    rw [hf i (Finset.mem_union_right _ hi')]
    simp only [z,ite_eq_right hin]

theorem source_translated_disjoint_eventually (hm' : 10 < m+1) :
    ∃ L : ℕ, ∀ M : ℕ, L ≤ M →
      ∃ t : Multiplicative (FreeAbelianGroup (Fin m × Fin 2)) →*
          BoundedRelationCover M (alternatingGenerator a r m hm),
        (∀ i, t (Multiplicative.ofAdd (FreeAbelianGroup.of i)) = PresentedGroup.of (Sum.inr i)) ∧
        (coverMap M (alternatingGenerator a r m hm)).comp t = sourceLatticeMap a r m hm ∧
        ∀ (j k : Fin 5)
          (σ ρ : {σ : Equiv.Perm (Fin (m+1)) //
            σ ∈ alternatingGroup (Fin (m+1)) ∧ σ.support.card ≤ 5}),
            Disjoint σ.val.support ρ.val.support → ∀ u v,
            Commute (t u * PresentedGroup.of (Sum.inl (j,σ)) * (t u)⁻¹)
              (t v * PresentedGroup.of (Sum.inl (k,ρ)) * (t v)⁻¹) := by
  obtain ⟨L₁,hL₁⟩ := source_centralizing_translation_lifts_eventually a r m hm
  obtain ⟨L₂,hL₂⟩ := generator_commutations_eventually (alternatingGenerator a r m hm)
  refine ⟨max L₁ L₂,fun M hM => ?_⟩
  obtain ⟨t,ht,htq,hc⟩ := hL₁ M (le_trans (le_max_left _ _) hM)
  refine ⟨t,ht,htq,?_⟩
  intro j k σ ρ hd u v
  have hy : Commute (PresentedGroup.of (Sum.inl (j,σ)) :
      BoundedRelationCover M (alternatingGenerator a r m hm))
      (PresentedGroup.of (Sum.inl (k,ρ))) := by
    apply hL₂ M (le_trans (le_max_right _ _) hM)
    change _*_ = _*_
    apply Subtype.ext
    exact (conditionalHom_disjoint_alphabets (initialTest a r j)
      (initialTest a r k) σ.val ρ.val hd).eq
  obtain ⟨w,hw₁,hw₂⟩ := source_disjoint_common_shift a r m hm σ.val ρ.val hd
    (by have hσ := σ.property.2; have hρ := ρ.property.2; omega)
    (initialTest a r j) (initialTest a r k) u v
  apply lifted_common_shift_commute (sourceLatticeMap a r m hm) t
    (alternatingGenerator a r m hm (Sum.inl (j,σ)))
    (alternatingGenerator a r m hm (Sum.inl (k,ρ))) _ _
    (hc (Sum.inl (j,σ))) (hc (Sum.inl (k,ρ))) hy u v w
  · apply Subtype.ext
    exact hw₁
  · apply Subtype.ext
    exact hw₂

end TranslatedDisjoint

end SimpleAmenable
end
end

end OAI
