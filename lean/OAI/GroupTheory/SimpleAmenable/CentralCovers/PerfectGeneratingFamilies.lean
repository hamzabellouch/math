import Mathlib
import OAI.GroupTheory.SimpleAmenable.CentralCovers.FiniteCentralKernel
import OAI.GroupTheory.SimpleAmenable.PolygonGeometry.TranslationLifts

namespace OAI

section
section
open scoped symmDiff
namespace SimpleAmenable
open scoped commutatorElement
open scoped commutatorElement
section PerfectGeneratingFamilies

variable {ι G H : Type*} [Group G] [Group H]

theorem perfect_iSup (F : ι → Subgroup G) [∀ i, Group.IsPerfect (F i)] :
    Group.IsPerfect ↥(⨆ i, F i) := by
  apply Subgroup.isPerfect_iff.mpr
  apply le_antisymm (Subgroup.commutator_le_self _)
  apply iSup_le
  intro i
  rw [← Subgroup.commutator_eq_self (H := F i)]
  exact Subgroup.commutator_mono (le_iSup F i) (le_iSup F i)

theorem central_perfect_generating_ranges {E : ι → Type*} [∀ i, Group (E i)]
    [∀ i, Group.IsPerfect (E i)] [Group.IsPerfect H]
    (q : H →* G) (hc : q.ker ≤ Subgroup.center H)
    (f : ∀ i, E i →* H) (hf : (⨆ i, (q.comp (f i)).range) = ⊤) :
    (⨆ i, (f i).range) = ⊤ := by
  let S : Subgroup H := ⨆ i, (f i).range
  let (i : ι) : Group.IsPerfect (f i).range := Group.IsPerfect.range (f i)
  let : Group.IsPerfect S := perfect_iSup (fun i => (f i).range)
  have hm : S.map q = ⊤ := by
    simp only [S, Subgroup.map_iSup, ← MonoidHom.range_comp]
    exact hf
  have hs : Function.Surjective (q.comp S.subtype) := by
    apply MonoidHom.range_eq_top.mp
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
    exact hm
  have hr := perfect_lift_range S.subtype q hs hc
  simpa only [Subgroup.range_subtype, Group.IsPerfect.commutator_eq_top] using hr

variable [Group.IsPerfect G]

theorem universal_generating_ranges {E : ι → Type*} [∀ i, Group (E i)]
    [∀ i, Group.IsPerfect (E i)] (f : ∀ i, E i →* G)
    (hf : (⨆ i, (f i).range) = ⊤) :
    (⨆ i, (universalMap (f i)).range) = ⊤ := by
  apply central_perfect_generating_ranges (universalProjection G)
    (universalProjection_central G) (fun i => universalMap (f i))
  have he (i : ι) : ((universalProjection G).comp (universalMap (f i))).range = (f i).range := by
    rw [universalMap_spec, MonoidHom.range_comp,
      MonoidHom.range_eq_top.mpr (universalProjection_surjective (E i)), ← MonoidHom.range_eq_map]
  simpa only [he] using hf

end PerfectGeneratingFamilies

section FiniteTranslationCentralizers

variable {α β ι G : Type*} [Group G]

noncomputable def translationWordMap (β : Type*) :
    FreeGroup β →* Multiplicative (FreeAbelianGroup β) :=
  FreeGroup.lift (fun i => Multiplicative.ofAdd (FreeAbelianGroup.of i))

theorem translationWordMap_surjective : Function.Surjective (translationWordMap β) := by
  intro x
  change ∃ y, translationWordMap β y =
    Multiplicative.ofAdd (Multiplicative.toAdd x)
  induction Multiplicative.toAdd x using FreeAbelianGroup.induction_on with
  | zero => exact ⟨1,map_one _⟩
  | of i => exact ⟨FreeGroup.of i,FreeGroup.lift_apply_of⟩
  | neg i hi =>
      obtain ⟨w,hw⟩ := hi
      exact ⟨w⁻¹,by change translationWordMap β (w⁻¹) = _⁻¹; rw [map_inv,hw]; rfl⟩
  | add x y hx hy =>
      obtain ⟨w,hw⟩ := hx
      obtain ⟨v,hv⟩ := hy
      exact ⟨w*v,by change translationWordMap β (w*v) = _*_; rw [map_mul,hw,hv]; rfl⟩

theorem translation_lattice_fg [Finite β] :
    Group.FG (Multiplicative (FreeAbelianGroup β)) :=
  Group.fg_of_surjective (translationWordMap_surjective (β := β))

theorem translation_centralizers_eventually [Finite β] [Finite ι]
    (f : α → G) (w : β → FreeGroup α) (v : ι → FreeGroup α)
    (ht : ∀ i j, Commute (FreeGroup.lift f (w i)) (FreeGroup.lift f (w j))) :
    ∃ L : ℕ, ∀ M : ℕ, L ≤ M →
      ∀ t : Multiplicative (FreeAbelianGroup β) →* BoundedRelationCover M f,
      (∀ i, t (Multiplicative.ofAdd (FreeAbelianGroup.of i)) =
          PresentedGroup.mk (shortRelations M f) (w i)) →
      ∀ i k, Commute (commutingFamilyHom (fun j => FreeGroup.lift f (w j)) ht k)
          (FreeGroup.lift f (v i)) →
        Commute (t k) (PresentedGroup.mk (shortRelations M f) (v i)) := by
  classical
  let T := Multiplicative (FreeAbelianGroup β)
  let : Group.FG T := translation_lattice_fg
  let q : T →* G := commutingFamilyHom (fun j => FreeGroup.lift f (w j)) ht
  let K (i : ι) : Subgroup T := (Subgroup.centralizer {FreeGroup.lift f (v i)}).comap q
  have hK (i : ι) : (K i).FG := subgroup_fg_of_comm (K i)
  choose S hS using hK
  let J := (i : ι) × ↥(S i)
  let z : J → T := fun j => j.2.val
  choose V hV using fun j : J => translationWordMap_surjective (z j)
  let W : FreeGroup β →* FreeGroup α := FreeGroup.lift w
  have he : (FreeGroup.lift f).comp W = q.comp (translationWordMap β) := by
    ext i
    simp only [MonoidHom.comp_apply,W,q,translationWordMap,FreeGroup.lift_apply_of]
    exact (commutingFamilyHom_of (fun j => FreeGroup.lift f (w j)) ht i).symm
  have hc (j : J) : Commute (FreeGroup.lift f (W (V j))) (FreeGroup.lift f (v j.1)) := by
    have hz : z j ∈ K j.1 := by
      rw [← hS j.1]
      exact Subgroup.subset_closure j.2.property
    change q (z j) ∈ Subgroup.centralizer {_} at hz
    have hv : FreeGroup.lift f (W (V j)) = q (z j) := by
      simpa only [MonoidHom.comp_apply,hV j] using DFunLike.congr_fun he (V j)
    rw [hv]
    exact Subgroup.mem_centralizer_singleton_iff.mp hz
  obtain ⟨L,hL⟩ := finite_word_equalities_eventually f
    (fun j : J => W (V j) * v j.1) (fun j => v j.1 * W (V j))
    (fun j => by simpa only [map_mul] using (hc j).eq)
  refine ⟨L,fun M hM t ht' i k hk => ?_⟩
  have he' : t.comp (translationWordMap β) =
      (PresentedGroup.mk (shortRelations M f)).comp W := by
    ext j
    simpa [translationWordMap,W] using ht' j
  have hk' : k ∈ K i := Subgroup.mem_centralizer_singleton_iff.mpr hk.eq
  have hle : K i ≤ (Subgroup.centralizer
      {PresentedGroup.mk (shortRelations M f) (v i)}).comap t := by
    rw [← hS i]
    apply (Subgroup.closure_le _).mpr
    intro x hx
    let j : J := ⟨i,⟨x,hx⟩⟩
    have hv : t x = PresentedGroup.mk (shortRelations M f) (W (V j)) := by
      simpa only [MonoidHom.comp_apply,hV j] using DFunLike.congr_fun he' (V j)
    change t x ∈ Subgroup.centralizer {_}
    apply Subgroup.mem_centralizer_singleton_iff.mpr
    rw [hv]
    simpa only [map_mul] using hL M hM j
  exact Subgroup.mem_centralizer_singleton_iff.mp (hle hk')

end FiniteTranslationCentralizers

section SourceCentralizingTranslations

variable (a : ℕ) (r : CutRing) (m : ℕ) (hm : 2 ≤ m)

noncomputable def sourceLatticeMap :
    Multiplicative (FreeAbelianGroup (Fin m × Fin 2)) →*
      polygonAlternatingGroup a (m+1) :=
  commutingFamilyHom (fun i => alternatingGenerator a r m hm (Sum.inr i))
    (source_translation_commute a r m hm)

theorem source_centralizing_translation_lifts_eventually :
    ∃ L : ℕ, ∀ M : ℕ, L ≤ M →
      ∃ t : Multiplicative (FreeAbelianGroup (Fin m × Fin 2)) →*
          BoundedRelationCover M (alternatingGenerator a r m hm),
        (∀ i, t (Multiplicative.ofAdd (FreeAbelianGroup.of i)) =
          PresentedGroup.of (Sum.inr i)) ∧
        (coverMap M (alternatingGenerator a r m hm)).comp t =
          sourceLatticeMap a r m hm ∧
        ∀ s k, Commute (sourceLatticeMap a r m hm k)
            (alternatingGenerator a r m hm s) →
          Commute (t k) (PresentedGroup.of s) := by
  let f := alternatingGenerator a r m hm
  let w : Fin m × Fin 2 → FreeGroup (SourceGeneratorLabel m) :=
    fun i => FreeGroup.of (sourceTranslationLabel m i)
  have hc : ∀ i j, Commute (FreeGroup.lift f (w i)) (FreeGroup.lift f (w j)) := by
    intro i j
    exact source_translation_commute a r m hm i j
  obtain ⟨L₁,hL₁⟩ := commuting_words_lift_eventually f w hc
  obtain ⟨L₂,hL₂⟩ := translation_centralizers_eventually f w
    (fun s : SourceGeneratorLabel m => FreeGroup.of s) hc
  refine ⟨max L₁ L₂,fun M hM => ?_⟩
  obtain ⟨t,ht,htq⟩ := hL₁ M (le_trans (le_max_left _ _) hM)
  refine ⟨t,ht,htq,?_⟩
  intro s k hk
  exact hL₂ M (le_trans (le_max_right _ _) hM) t ht s k hk

end SourceCentralizingTranslations

end SimpleAmenable
end
end

end OAI
