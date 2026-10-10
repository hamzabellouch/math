import OAI.Algebra.AuslanderReiten.HomComplex.FullHomFunctor

namespace OAI

noncomputable section
namespace ArExplicit
open CategoryTheory CochainComplex.HomComplex
variable {C D : Type*} [Category* C] [Category* D] [Preadditive C] [Preadditive D]
variable (Φ : C ⥤ D) [Φ.Additive]
variable (K L : CochainComplex C ℤ) (n : ℤ)

def mapFullHom : CohomologyClass K L n →+
    CohomologyClass ((Φ.mapHomologicalComplex _).obj K)
      ((Φ.mapHomologicalComplex _).obj L) n :=
  CohomologyClass.descAddMonoidHom
    ((CohomologyClass.mkAddMonoidHom _ _ _).comp (fullHomCocycleMap Φ K L n)) (by
      intro x hx
      apply (CohomologyClass.mk_eq_zero_iff _).mpr
      obtain ⟨m, hm, y, hy⟩ := hx
      refine ⟨m, hm, y.map Φ, ?_⟩
      rw [δ_map, hy]
      rfl)

@[simp] theorem mapFullHom_mk (x : Cocycle K L n) :
    mapFullHom Φ K L n (CohomologyClass.mk x) =
      CohomologyClass.mk (fullHomCocycleMap Φ K L n x) := rfl

theorem mapFullHom_eq [Φ.Full] [Φ.Faithful] :
    mapFullHom Φ K L n = fullHomCohomologyMap Φ K L n := rfl

variable {K L n}
theorem mapFullHom_product {M : CochainComplex C ℤ} {m : ℤ}
    (x : CohomologyClass K L n) (y : CohomologyClass L M m) :
    mapFullHom Φ K M (n+m) (CompleteComparison.fullHomProduct x y) =
      CompleteComparison.fullHomProduct (mapFullHom Φ K L n x)
        (mapFullHom Φ L M m y) := by
  obtain ⟨x, rfl⟩ := CohomologyClass.mk_surjective x
  obtain ⟨y, rfl⟩ := CohomologyClass.mk_surjective y
  simp only [CompleteComparison.fullHomProduct_mk, mapFullHom_mk]
  congr 1
  apply Cocycle.ext
  apply Cochain.map_comp
  rfl

end ArExplicit

end

end OAI
