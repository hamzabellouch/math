import Mathlib
import OAI.GroupTheory.SimpleAmenable.Configurations.TrackTranslationChart
import OAI.GroupTheory.SimpleAmenable.CentralCovers.BoundedRelationCover

namespace OAI

section
section
open scoped symmDiff
namespace SimpleAmenable
section FinitelyManyTranslationRelations

open scoped IsMulCommutative

variable {β H : Type*} [Group H]

noncomputable def commutingFamilyHom (t : β → H) (ht : ∀ i j, Commute (t i) (t j)) :
    Multiplicative (FreeAbelianGroup β) →* H := by
  let C := Subgroup.closure (Set.range t)
  haveI : IsMulCommutative C := Subgroup.isMulCommutative_closure (by
    rintro x ⟨i,rfl⟩ y ⟨j,rfl⟩ _
    exact ht i j)
  letI : CommGroup C := by infer_instance
  exact C.subtype.comp (AddMonoidHom.toMultiplicativeLeft
    (FreeAbelianGroup.lift (fun i => Additive.ofMul (⟨t i,Subgroup.subset_closure ⟨i,rfl⟩⟩ : C))))

@[simp] theorem commutingFamilyHom_of (t : β → H) (ht : ∀ i j, Commute (t i) (t j))
    (i : β) : commutingFamilyHom t ht (Multiplicative.ofAdd (FreeAbelianGroup.of i)) = t i := by
  simp [commutingFamilyHom]

theorem freeAbelianHom_ext (φ ψ : Multiplicative (FreeAbelianGroup β) →* H)
    (h : ∀ i, φ (Multiplicative.ofAdd (FreeAbelianGroup.of i)) =
      ψ (Multiplicative.ofAdd (FreeAbelianGroup.of i))) : φ = ψ := by
  apply MonoidHom.ext
  intro x
  change φ (Multiplicative.ofAdd (Multiplicative.toAdd x)) = ψ (Multiplicative.ofAdd (Multiplicative.toAdd x))
  induction Multiplicative.toAdd x using FreeAbelianGroup.induction_on with
  | zero => exact (map_one φ).trans (map_one ψ).symm
  | of i => exact h i
  | neg x hx =>
      change φ ((Multiplicative.ofAdd (FreeAbelianGroup.of x))⁻¹) = ψ ((Multiplicative.ofAdd (FreeAbelianGroup.of x))⁻¹)
      rw [map_inv, map_inv, hx]
  | add x y hx hy =>
      change φ (Multiplicative.ofAdd x * Multiplicative.ofAdd y) = ψ (Multiplicative.ofAdd x * Multiplicative.ofAdd y)
      rw [map_mul, map_mul, hx, hy]

theorem commutingFamilyHom_range (t : β → H) (ht : ∀ i j, Commute (t i) (t j)) :
    (commutingFamilyHom t ht).range = Subgroup.closure (Set.range t) := by
  apply le_antisymm
  · rintro _ ⟨x,rfl⟩
    exact Subtype.property _
  · apply (Subgroup.closure_le _).mpr
    rintro _ ⟨i,rfl⟩
    exact ⟨_,commutingFamilyHom_of t ht i⟩

theorem commutingFamilyHom_commute (t : β → H) (ht : ∀ i j, Commute (t i) (t j))
    {g : H} (hg : ∀ i, Commute (t i) g) (v : Multiplicative (FreeAbelianGroup β)) :
    Commute (commutingFamilyHom t ht v) g := by
  have hc : Subgroup.closure (Set.range t) ≤ Subgroup.centralizer {g} := by
    apply (Subgroup.closure_le _).mpr
    rintro x ⟨i,rfl⟩
    exact Subgroup.mem_centralizer_singleton_iff.mpr (hg i).eq
  have hm : commutingFamilyHom t ht v ∈ Subgroup.closure (Set.range t) := by
    rw [← commutingFamilyHom_range t ht]
    exact ⟨v,rfl⟩
  exact Subgroup.mem_centralizer_singleton_iff.mp (hc hm)

variable {α G : Type*} [Group G] (f : α → G)

theorem finite_word_equalities_eventually [Finite β] (u v : β → FreeGroup α)
    (huv : ∀ i, FreeGroup.lift f (u i) = FreeGroup.lift f (v i)) :
    ∃ L : ℕ, ∀ M : ℕ, L ≤ M → ∀ i,
      PresentedGroup.mk (shortRelations M f) (u i) =
        PresentedGroup.mk (shortRelations M f) (v i) := by
  obtain ⟨L,hL⟩ := finite_true_relations_bounded f
    (Set.finite_range (fun i => u i * (v i)⁻¹)) (by
      rintro w ⟨i,rfl⟩
      simp [huv])
  refine ⟨L,fun M hM i => ?_⟩
  exact PresentedGroup.mk_eq_mk_of_mul_inv_mem
    (shortRelations_mono f hM (hL ⟨i,rfl⟩))

theorem finite_table_with_inputs_eventually {T : Type*} [Group T] [Finite T]
    [Finite β] (φ : T →* G) (input : β → T) (w : β → FreeGroup α)
    (hw : ∀ i, FreeGroup.lift f (w i) = φ (input i))
    (hf : Function.Surjective (FreeGroup.lift f)) :
    ∃ L : ℕ, ∀ M : ℕ, L ≤ M → ∃ ρ : T →* BoundedRelationCover M f,
      (coverMap M f).comp ρ = φ ∧
      ∀ i, ρ (input i) = PresentedGroup.mk (shortRelations M f) (w i) := by
  choose W hW using fun t : T => hf (φ t)
  obtain ⟨L₁,hL₁⟩ := finite_table_lift_eventually f φ W hW
  obtain ⟨L₂,hL₂⟩ := finite_word_equalities_eventually f (fun i => W (input i)) w
    (fun i => (hW (input i)).trans (hw i).symm)
  refine ⟨max L₁ L₂,fun M hM => ?_⟩
  obtain ⟨ρ,hρ,hρW⟩ := hL₁ M (le_trans (le_max_left _ _) hM)
  refine ⟨ρ,hρ,fun i => ?_⟩
  rw [hρW, hL₂ M (le_trans (le_max_right _ _) hM)]

theorem commuting_words_lift_eventually [Finite β] (w : β → FreeGroup α)
    (ht : ∀ i j, Commute (FreeGroup.lift f (w i)) (FreeGroup.lift f (w j))) :
    ∃ L : ℕ, ∀ M : ℕ, L ≤ M →
      ∃ t : Multiplicative (FreeAbelianGroup β) →* BoundedRelationCover M f,
        (∀ i, t (Multiplicative.ofAdd (FreeAbelianGroup.of i)) =
          PresentedGroup.mk (shortRelations M f) (w i)) ∧
        (coverMap M f).comp t =
          commutingFamilyHom (fun i => FreeGroup.lift f (w i)) ht := by
  obtain ⟨L,hL⟩ := finite_word_equalities_eventually f
    (fun p : β × β => w p.1 * w p.2) (fun p => w p.2 * w p.1)
    (fun p => by simpa only [map_mul] using (ht p.1 p.2).eq)
  refine ⟨L,fun M hM => ?_⟩
  let u : β → BoundedRelationCover M f := fun i => PresentedGroup.mk (shortRelations M f) (w i)
  have hu : ∀ i j, Commute (u i) (u j) := by
    intro i j
    have he := hL M hM (i,j)
    exact show u i * u j = u j * u i from by simpa only [map_mul] using he
  refine ⟨commutingFamilyHom u hu, fun i => commutingFamilyHom_of u hu i, ?_⟩
  apply freeAbelianHom_ext
  intro i
  simp [u]

end FinitelyManyTranslationRelations

def SourceCoverCentrality (a : ℕ) (r : CutRing) (m : ℕ) (hm : 2 ≤ m) : Prop :=
  ∃ L : ℕ, (coverMap L (alternatingGenerator a r m hm)).ker ≤
    Subgroup.center (BoundedRelationCover L (alternatingGenerator a r m hm))

end SimpleAmenable
end
end

end OAI
