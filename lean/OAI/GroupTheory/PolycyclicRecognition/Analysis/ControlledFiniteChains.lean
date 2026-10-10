import OAI.GroupTheory.PolycyclicRecognition.Algebra.ControlledPrismIdentity

namespace OAI

/-! # Finite chains at a controlled scale

These submodules retain a finite set of allowed relative positions. They
provide the chain-level control needed for the remaining FP transfer argument.
-/

noncomputable section
namespace PolycyclicRecognition
open CategoryTheory
variable {R G H : Type} [CommRing R] [Group G] [Group H] {n m : ℕ}

def controlledChainSpan (R G : Type) [CommRing R] [Group G] (n : ℕ) (S : Set G) :
    Submodule R (MonoidAlgebra R (Fin (n + 1) → G)) :=
  Submodule.span R {c | ∃ x, IsControlledTuple S x ∧ c = MonoidAlgebra.single x 1}

theorem controlledChainSpan_single {S : Set G} {x : Fin (n + 1) → G}
    (hx : IsControlledTuple S x) :
    MonoidAlgebra.single x 1 ∈ controlledChainSpan R G n S :=
  Submodule.subset_span ⟨x, hx, rfl⟩

theorem controlledChainSpan_mono {S T : Set G} (h : S ⊆ T) :
    controlledChainSpan R G n S ≤ controlledChainSpan R G n T := by
  apply Submodule.span_mono
  rintro c ⟨x, hx, rfl⟩
  exact ⟨x, fun i j => h (hx i j), rfl⟩

theorem controlledChainSpan_map {S : Set G} {T : Set H}
    (f : MonoidAlgebra R (Fin (n + 1) → G) →ₗ[R]
      MonoidAlgebra R (Fin (m + 1) → H))
    (hf : ∀ x, IsControlledTuple S x →
      f (MonoidAlgebra.single x 1) ∈ controlledChainSpan R H m T)
    {c : MonoidAlgebra R (Fin (n + 1) → G)} (hc : c ∈ controlledChainSpan R G n S) :
    f c ∈ controlledChainSpan R H m T := by
  have h : controlledChainSpan R G n S ≤ (controlledChainSpan R H m T).comap f := by
    apply Submodule.span_le.mpr
    rintro a ⟨x, hx, rfl⟩
    exact hf x hx
  exact h hc

theorem controlledChainSpan_boundary {S : Set G}
    {c : MonoidAlgebra R (Fin (n + 2) → G)}
    (hc : c ∈ controlledChainSpan R G (n + 1) S) :
    (tupleChainComplex R G).d (n + 1) n c ∈ controlledChainSpan R G n S := by
  apply controlledChainSpan_map ((tupleChainComplex R G).d (n + 1) n).hom _ hc
  intro x hx
  change (tupleChainComplex R G).d (n + 1) n (MonoidAlgebra.single x 1) ∈
    controlledChainSpan R G n S
  rw [tupleChainComplex_boundary]
  apply Submodule.sum_mem
  intro i _
  exact Submodule.smul_mem _ _ (controlledChainSpan_single (hx.face i))

theorem exists_controlledChainScale (c : MonoidAlgebra R (Fin (n + 1) → G)) :
    ∃ S : Set G, S.Finite ∧ c ∈ controlledChainSpan R G n S := by
  induction c using MonoidAlgebra.induction_on with
  | of x =>
    let S := Set.range (fun p : Fin (n + 1) × Fin (n + 1) => (x p.1)⁻¹ * x p.2)
    exact ⟨S, Set.finite_range _, controlledChainSpan_single (fun i j => ⟨(i, j), rfl⟩)⟩
  | add c c' hc hc' =>
    obtain ⟨S, hS, hc⟩ := hc
    obtain ⟨T, hT, hc'⟩ := hc'
    exact ⟨S ∪ T, hS.union hT, Submodule.add_mem _
      (controlledChainSpan_mono Set.subset_union_left hc)
      (controlledChainSpan_mono Set.subset_union_right hc')⟩
  | smul r c hc =>
    obtain ⟨S, hS, hc⟩ := hc
    exact ⟨S, hS, Submodule.smul_mem _ r hc⟩

theorem controlledChainSpan_pushforward (f : G → H) (hf : GroupBornologous f)
    (S : Set G) (hS : S.Finite) :
    ∃ T : Set H, T.Finite ∧ ∀ c ∈ controlledChainSpan R G n S,
      (tupleChainMap (R := R) f).f n c ∈ controlledChainSpan R H n T := by
  obtain ⟨T, hT, hbound⟩ := hf S hS
  refine ⟨T, hT, fun c hc => controlledChainSpan_map ((tupleChainMap f).f n).hom ?_ hc⟩
  intro x hx
  change (tupleChainMap (R := R) f).f n (MonoidAlgebra.single x 1) ∈
    controlledChainSpan R H n T
  rw [tupleChainMap_single]
  exact controlledChainSpan_single (fun i j => hbound _ _ (hx i j))

theorem controlledChainSpan_prism (e e' : GroupCoarseEquivalence G H)
    (hc : (Set.range fun x => (e.toFun x)⁻¹ * e'.toFun x).Finite)
    (S : Set G) (hS : S.Finite) :
    ∃ T : Set H, T.Finite ∧ ∀ c ∈ controlledChainSpan R G n S,
      (tupleChainPrism (R := R) e.toFun e'.toFun).hom n (n + 1) c ∈
        controlledChainSpan R H (n + 1) T := by
  obtain ⟨T, hT, hbound⟩ := controlled_tuplePrism (n := n) e e' hc S hS
  refine ⟨T, hT, fun c hc' =>
    controlledChainSpan_map ((tupleChainPrism e.toFun e'.toFun).hom n (n + 1)).hom ?_ hc'⟩
  intro x hx
  change (tupleChainPrism (R := R) e.toFun e'.toFun).hom n (n + 1)
    (MonoidAlgebra.single x 1) ∈ controlledChainSpan R H (n + 1) T
  rw [tupleChainPrism_single]
  apply Submodule.neg_mem
  apply Submodule.sum_mem
  intro i _
  exact Submodule.smul_mem _ _ (controlledChainSpan_single (hbound x hx i))

end PolycyclicRecognition

end

end OAI
