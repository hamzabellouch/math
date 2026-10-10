import OAI.Algebra.AuslanderReiten.Stable.SourceStableCoordinates
import OAI.Algebra.AuslanderReiten.HomComplex.FullHomNaturality

namespace OAI

noncomputable section
open CategoryTheory HomologicalComplex
open CochainComplex CochainComplex.HomComplex
namespace ArExplicit.CompleteComparison
universe u
variable {k R : Type u} [Field k] [Ring R] [Algebra k R] [CharP k 2]
variable {K L M : CochainComplex (ModuleCat.{u} R) ℤ} {n : ℤ}

theorem sourceCocycleComponent_precomp (f : K ⟶ L) (x : Cocycle L M n) :
    sourceCocycleComponent (x.precomp f) =
      (extendMap f negIndexEmbedding).f n ≫ sourceCocycleComponent x := by
  unfold sourceCocycleComponent
  change _ ≫ ((Cochain.ofHom f).comp x.val (zero_add n)).v (-n) 0 (by omega) ≫ _ = _
  rw [Cochain.comp_v _ _ (zero_add n) (-n) (-n) 0 (by omega) (by omega),
    Cochain.ofHom_v,
    extendMap_f f negIndexEmbedding (i := -n) (i' := n) (neg_neg n)]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]

theorem sourceCocycleComponent_postcomp (x : Cocycle K L n) (f : L ⟶ M) :
    sourceCocycleComponent (x.postcomp f) =
      sourceCocycleComponent x ≫ (extendMap f negIndexEmbedding).f 0 := by
  unfold sourceCocycleComponent
  change _ ≫ (x.val.comp (Cochain.ofHom f) (add_zero n)).v (-n) 0 (by omega) ≫ _ = _
  rw [Cochain.comp_v _ _ (add_zero n) (-n) 0 0 (by omega) (by omega),
    Cochain.ofHom_v, extendMap_f f negIndexEmbedding (i := 0) (i' := 0) rfl]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]

include k in
theorem sourceCocycleMap_precomp (f : K ⟶ L) (x : Cocycle L M n) :
    sourceCocycleMap (x.precomp f) =
      (sourceCocycleMap x).comp (cokernelMap (extendMap f negIndexEmbedding) n) := by
  apply LinearMap.ext
  intro z
  obtain ⟨z, rfl⟩ := Submodule.mkQ_surjective
    (LinearMap.range ((chainOfCochain K).d (n+1) n).hom) z
  change sourceCocycleMap (x.precomp f) (Submodule.Quotient.mk z) =
    sourceCocycleMap x (Submodule.Quotient.mk (((extendMap f negIndexEmbedding).f n).hom z))
  rw [sourceCocycleMap_mk (k := k), sourceCocycleMap_mk (k := k), sourceCocycleComponent_precomp]
  rfl

include k in
theorem sourceCocycleMap_postcomp (x : Cocycle K L n) (f : L ⟶ M) :
    sourceCocycleMap (x.postcomp f) =
      (cokernelMap (extendMap f negIndexEmbedding) 0).comp (sourceCocycleMap x) := by
  apply LinearMap.ext
  intro z
  obtain ⟨z, rfl⟩ := Submodule.mkQ_surjective
    (LinearMap.range ((chainOfCochain K).d (n+1) n).hom) z
  change sourceCocycleMap (x.postcomp f) (Submodule.Quotient.mk z) =
    cokernelMap (extendMap f negIndexEmbedding) 0 (sourceCocycleMap x (Submodule.Quotient.mk z))
  rw [sourceCocycleMap_mk (k := k), sourceCocycleMap_mk (k := k), sourceCocycleComponent_postcomp]
  rfl

end ArExplicit.CompleteComparison

end

end OAI
