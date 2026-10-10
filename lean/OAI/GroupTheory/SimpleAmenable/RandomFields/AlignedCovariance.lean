import Mathlib
import OAI.GroupTheory.SimpleAmenable.RandomFields.FiniteCovariance

namespace OAI

section
section
open scoped symmDiff
namespace SimpleAmenable
open scoped commutatorElement
open scoped commutatorElement
section AlignedCovariance

variable {A B H : Type*} [Group A] [Group H]

theorem alignedGroup_reindex (t : A →* H) (x : B → H) (P Q : B → Prop)
    (c : H) (R : A →* A) (b : B → B)
    (ht : ∀ u, c*t u*c⁻¹ = t (R u)) (hx : ∀ i, c*x i*c⁻¹ = x (b i))
    (hb : ∀ i, P i → Q (b i)) {y : H} (hy : y ∈ alignedGroup t x P) :
    c*y*c⁻¹ ∈ alignedGroup t x Q := by
  let f : H →* H := (MulAut.conj c).toMonoidHom
  have hh : alignedGroup t x P ≤ (alignedGroup t x Q).comap f := by
    apply (Subgroup.closure_le _).mpr
    rintro z ⟨i,hi,u,rfl⟩
    change c*(t u*x i*(t u)⁻¹)*c⁻¹ ∈ alignedGroup t x Q
    have he : c*(t u*x i*(t u)⁻¹)*c⁻¹ = t (R u)*x (b i)*(t (R u))⁻¹ := by
      rw [← ht,← hx]
      group
    rw [he]
    exact alignedGroup_generator t x Q (b i) (hb i hi) (R u)
  exact hh hy

end AlignedCovariance

section SourceAlignedCovariance

variable (a : ℕ) (r : CutRing) (m : ℕ) (hm : 2 ≤ m) (M : ℕ)

theorem source_aligned_constant_conjugation
    (t : Multiplicative (FreeAbelianGroup (Fin m × Fin 2)) →*
      BoundedRelationCover M (alternatingGenerator a r m hm))
    (c : alternatingGroup (Fin (m+1)) →*
      BoundedRelationCover M (alternatingGenerator a r m hm))
    (R : alternatingGroup (Fin (m+1)) →
      Multiplicative (FreeAbelianGroup (Fin m × Fin 2)) →*
      Multiplicative (FreeAbelianGroup (Fin m × Fin 2)))
    (ht : ∀ s k, c s*t k*(c s)⁻¹ = t (R s k))
    (hx : ∀ s (b : SmallConditional m), c s*PresentedGroup.of (Sum.inl b)*(c s)⁻¹ =
      PresentedGroup.of (Sum.inl (reindexSmallConditional m s b)))
    (s : alternatingGroup (Fin (m+1))) (I : Finset (Fin (m+1)))
    {y : BoundedRelationCover M (alternatingGenerator a r m hm)}
    (hy : y ∈ sourceAlignedGroup a r m hm M t I) :
    c s*y*(c s)⁻¹ ∈ sourceAlignedGroup a r m hm M t (I.map s.val.toEmbedding) := by
  apply alignedGroup_reindex t (fun b : SmallConditional m => PresentedGroup.of (Sum.inl b))
    (fun b => b.2.val.support ⊆ I) (fun b => b.2.val.support ⊆ I.map s.val.toEmbedding)
    (c s) (R s) (reindexSmallConditional m s) (ht s) (hx s) _ hy
  intro b hb
  rw [reindexSmallConditional_support]
  exact Finset.map_subset_map.mpr hb

end SourceAlignedCovariance

end SimpleAmenable
end
end

end OAI
