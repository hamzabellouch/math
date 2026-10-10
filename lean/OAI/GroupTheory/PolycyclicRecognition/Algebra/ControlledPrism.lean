import OAI.GroupTheory.PolycyclicRecognition.Finiteness.ControlledTupleMaps
import OAI.GroupTheory.PolycyclicRecognition.Algebra.TuplePrism

namespace OAI

/-! # The prism preserves controlled support

Closeness bounds all mixed pairs of vertices. Properness of the first vertex
then gives finite fibers at each controlled scale.
-/

noncomputable section
namespace PolycyclicRecognition
variable {G H R : Type} [Group G] [Group H] [CommRing R] {n : ℕ}

theorem controlled_tuplePrism (e e' : GroupCoarseEquivalence G H)
    (hc : (Set.range fun x => (e.toFun x)⁻¹ * e'.toFun x).Finite)
    (S : Set G) (hS : S.Finite) :
    ∃ T : Set H, T.Finite ∧ ∀ (x : Fin (n + 1) → G), IsControlledTuple S x →
      ∀ i, IsControlledTuple T (tuplePrism e.toFun e'.toFun i x) := by
  obtain ⟨T, hT, hmix⟩ := controlled_mixed_tuple (n := n) (m := n + 1)
    e.toFun e'.toFun e.bornologous_toFun e'.bornologous_toFun hc S hS
  refine ⟨T, hT, fun x hx i => ?_⟩
  let a : Fin (n + 2) → Fin (n + 1) := fun k =>
    if h : k.val ≤ i.val then ⟨k.val, lt_of_le_of_lt h i.isLt⟩
    else ⟨k.val - 1, by omega⟩
  let choose : Fin (n + 2) → Bool := fun k => decide (¬ k.val ≤ i.val)
  convert hmix x hx a choose using 1
  funext k
  by_cases h : k.val ≤ i.val <;> simp [tuplePrism, a, choose, h]

/-- Each prism summand is defined on the controlled cochains themselves. -/
def controlledPrismTerm (e e' : GroupCoarseEquivalence G H)
    (hc : (Set.range fun x => (e.toFun x)⁻¹ * e'.toFun x).Finite)
    (i : Fin (n + 1)) :
    controlledCochains R H (n + 1) →ₗ[R] controlledCochains R G n where
  toFun c := ⟨fun x => c (tuplePrism e.toFun e'.toFun i x), by
    intro S hS
    obtain ⟨T, hT, hprism⟩ := controlled_tuplePrism e e' hc S hS
    let C := {y : Fin (n + 2) → H | IsControlledTuple T y ∧ c y ≠ 0}
    have hC : C.Finite := c.property T hT
    have hF : (⋃ y ∈ C, {x : Fin (n + 1) → G |
        IsControlledTuple S x ∧ tuplePrism e.toFun e'.toFun i x = y}).Finite :=
      hC.biUnion (fun y _ => finite_controlled_tuple_map_fiber e.toFun e.finite_fiber
        (tuplePrism e.toFun e'.toFun i) (fun x => tuplePrism_zero _ _ _ x) S hS y)
    apply hF.subset
    intro x hx
    exact Set.mem_iUnion.mpr ⟨_, Set.mem_iUnion.mpr ⟨⟨hprism x hx.1 i, hx.2⟩, hx.1, rfl⟩⟩⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp] theorem controlledPrismTerm_apply (e e' : GroupCoarseEquivalence G H)
    (hc : (Set.range fun x => (e.toFun x)⁻¹ * e'.toFun x).Finite)
    (i : Fin (n + 1)) (c : controlledCochains R H (n + 1))
    (x : Fin (n + 1) → G) :
    controlledPrismTerm e e' hc i c x = c (tuplePrism e.toFun e'.toFun i x) := rfl

/-- The negative alternating prism, with the sign convention of Mathlib's
chain homotopy, lowers cochain degree by one. -/
def controlledPrism (e e' : GroupCoarseEquivalence G H)
    (hc : (Set.range fun x => (e.toFun x)⁻¹ * e'.toFun x).Finite) :
    controlledCochains R H (n + 1) →ₗ[R] controlledCochains R G n :=
  -∑ i : Fin (n + 1), (-1 : R) ^ i.val • controlledPrismTerm e e' hc i

@[simp] theorem controlledPrism_apply (e e' : GroupCoarseEquivalence G H)
    (hc : (Set.range fun x => (e.toFun x)⁻¹ * e'.toFun x).Finite)
    (c : controlledCochains R H (n + 1)) (x : Fin (n + 1) → G) :
    controlledPrism e e' hc c x =
      -∑ i : Fin (n + 1), (-1 : R) ^ i.val * c (tuplePrism e.toFun e'.toFun i x) := by
  simp [controlledPrism, smul_eq_mul]

end PolycyclicRecognition

end

end OAI
