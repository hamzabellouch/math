import OAI.GroupTheory.PolycyclicRecognition.Analysis.CoarseEquivalence
import Mathlib.LinearAlgebra.Pi

namespace OAI

/-! # Cochains with finite support on controlled tuples

These are the scalar homogeneous cochains used to compare group-ring
cohomology under a coarse equivalence. Support is finite after restricting
all pairwise differences to any finite set. The pullback below uses both
bounded-difference control and finite fibers of the coarse map.
-/

noncomputable section
namespace PolycyclicRecognition

variable {G H : Type*} [Group G] [Group H]
variable (R : Type*) [CommRing R]

/-- All pairwise differences of a tuple belong to the indicated finite scale. -/
def IsControlledTuple {n : ℕ} (S : Set G) (x : Fin (n + 1) → G) : Prop :=
  ∀ i j, (x i)⁻¹ * x j ∈ S

/-- Homogeneous scalar cochains, locally finite on every controlled set. -/
def controlledCochains (G : Type*) [Group G] (n : ℕ) :
    Submodule R ((Fin (n + 1) → G) → R) where
  carrier := {c | ∀ S : Set G, S.Finite →
    {x | IsControlledTuple S x ∧ c x ≠ 0}.Finite}
  zero_mem' := by intro S _; simp
  add_mem' := by
    intro c d hc hd S hS
    apply ((hc S hS).union (hd S hS)).subset
    intro x hx
    by_cases hcx : c x = 0
    · exact Or.inr ⟨hx.1, by simpa only [Pi.add_apply, hcx, zero_add] using hx.2⟩
    · exact Or.inl ⟨hx.1, hcx⟩
  smul_mem' := by
    intro a c hc S hS
    apply (hc S hS).subset
    intro x hx
    refine ⟨hx.1, fun hz => hx.2 ?_⟩
    simp only [Pi.smul_apply, hz, smul_zero]

variable {R}

instance {n : ℕ} : CoeFun (controlledCochains R G n)
    (fun _ => (Fin (n + 1) → G) → R) := ⟨fun c => c.val⟩

/-- A coarse equivalence has finite inverse images of finite sets. -/
theorem GroupCoarseEquivalence.finite_preimage (e : GroupCoarseEquivalence G H)
    (S : Set H) (hS : S.Finite) : (e.toFun ⁻¹' S).Finite :=
  hS.preimage' (fun y _ => e.finite_fiber y)

/-- Coordinatewise pullback retains properness on finite tuple spaces. -/
theorem GroupCoarseEquivalence.finite_tuple_fiber (e : GroupCoarseEquivalence G H)
    (n : ℕ) (y : Fin (n + 1) → H) :
    {x : Fin (n + 1) → G | e.toFun ∘ x = y}.Finite := by
  let A (i : Fin (n + 1)) := {g : G // e.toFun g = y i}
  have hA (i : Fin (n + 1)) : Finite (A i) := (e.finite_fiber (y i)).to_subtype
  let (i : Fin (n + 1)) : Finite (A i) := hA i
  let F : {x : Fin (n + 1) → G // e.toFun ∘ x = y} → ∀ i, A i :=
    fun x i => ⟨x.val i, congrFun x.property i⟩
  have hi : Function.Injective F := by
    intro x z h
    apply Subtype.ext
    funext i
    exact congrArg Subtype.val (congrFun h i)
  exact Set.finite_coe_iff.mp (Finite.of_injective F hi)

/-- Pullback is well-defined because controlled tuples map to controlled
tuples and the map on tuples has finite fibers. -/
def controlledCochainPullback (e : GroupCoarseEquivalence G H) (n : ℕ) :
    controlledCochains R H n →ₗ[R] controlledCochains R G n where
  toFun c := ⟨fun x => c (e.toFun ∘ x), by
    intro S hS
    obtain ⟨T, hT, he⟩ := e.bornologous_toFun S hS
    have hf := (c.property T hT).preimage'
      (fun y _ => e.finite_tuple_fiber n y)
    apply hf.subset
    intro x hx
    exact ⟨fun i j => he (x i) (x j) (hx.1 i j), hx.2⟩⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp] theorem controlledCochainPullback_apply
    (e : GroupCoarseEquivalence G H) (n : ℕ) (c : controlledCochains R H n)
    (x : Fin (n + 1) → G) : controlledCochainPullback e n c x = c (e.toFun ∘ x) := rfl

/-- Cochain pullback reverses composition of coarse maps. -/
theorem controlledCochainPullback_trans {J : Type*} [Group J]
    (e : GroupCoarseEquivalence G H) (e' : GroupCoarseEquivalence H J) (n : ℕ)
    (c : controlledCochains R J n) :
    controlledCochainPullback (e.trans e') n c =
      controlledCochainPullback e n (controlledCochainPullback e' n c) := rfl

end PolycyclicRecognition

end

end OAI
