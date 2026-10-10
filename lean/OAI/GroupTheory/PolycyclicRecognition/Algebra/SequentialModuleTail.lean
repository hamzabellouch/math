import Mathlib.Algebra.Colimit.Module

namespace OAI

/-! # Removing the first stage of a sequential integral module colimit -/
noncomputable section
namespace PolycyclicRecognition
attribute [local instance 2300] Module.DirectLimit.module
variable (M : ℕ → Type) [∀ i, AddCommGroup (M i)] [∀ i, Module ℤ (M i)]
  (f : ∀ i j, i ≤ j → M i →ₗ[ℤ] M j)
  [DirectedSystem M (fun i j h => f i j h)]

abbrev moduleTailMap (i j : ℕ) (h : i ≤ j) : M (i + 1) →ₗ[ℤ] M (j + 1) :=
  f (i + 1) (j + 1) (Nat.add_le_add_right h 1)

instance moduleTailMap_directed : DirectedSystem (fun i => M (i + 1))
    (fun i j h => moduleTailMap M f i j h) where
  map_self := by intro i x; exact Module.DirectedSystem.map_self (f := f) x
  map_map := by
    intro k j i hij hjk x
    exact Module.DirectedSystem.map_map (f := f)
      (Nat.add_le_add_right hij 1) (Nat.add_le_add_right hjk 1) x

abbrev ModuleTailLimit := Module.DirectLimit (fun i => M (i + 1)) (moduleTailMap M f)

def moduleTailToOriginal : ModuleTailLimit M f →ₗ[ℤ] Module.DirectLimit M f :=
  Module.DirectLimit.lift ℤ ℕ _ _
    (fun i => Module.DirectLimit.of ℤ ℕ M f (i + 1))
    (fun _ _ h x => Module.DirectLimit.of_f (R := ℤ) (f := f)
      (hij := Nat.add_le_add_right h 1) (x := x))

omit [DirectedSystem M (fun i j h => f i j h)] in
theorem moduleTailToOriginal_of (i : ℕ) (x : M (i + 1)) :
    moduleTailToOriginal M f (Module.DirectLimit.of ℤ ℕ _ (moduleTailMap M f) i x) =
      Module.DirectLimit.of ℤ ℕ M f (i + 1) x :=
  Module.DirectLimit.lift_of _ _ _

def moduleOriginalToTail : Module.DirectLimit M f →ₗ[ℤ] ModuleTailLimit M f :=
  Module.DirectLimit.lift ℤ ℕ _ _
    (fun i => (Module.DirectLimit.of ℤ ℕ _ (moduleTailMap M f) i).comp
      (f i (i + 1) (Nat.le_succ i))) (by
        intro i j h x
        change Module.DirectLimit.of ℤ ℕ _ (moduleTailMap M f) j
          (f j (j + 1) (Nat.le_succ j) (f i j h x)) =
            Module.DirectLimit.of ℤ ℕ _ (moduleTailMap M f) i
              (f i (i + 1) (Nat.le_succ i) x)
        rw [Module.DirectedSystem.map_map]
        rw [← Module.DirectedSystem.map_map (f := f) (Nat.le_succ i)
          (Nat.add_le_add_right h 1) x]
        exact Module.DirectLimit.of_f (R := ℤ) (f := moduleTailMap M f)
          (hij := h) (x := f i (i + 1) (Nat.le_succ i) x))

@[simp]
theorem moduleOriginalToTail_of (i : ℕ) (x : M i) :
    moduleOriginalToTail M f (Module.DirectLimit.of ℤ ℕ M f i x) =
      Module.DirectLimit.of ℤ ℕ _ (moduleTailMap M f) i (f i (i + 1) (Nat.le_succ i) x) :=
  Module.DirectLimit.lift_of _ _ _

theorem moduleTail_original_inverse :
    (moduleTailToOriginal M f).comp (moduleOriginalToTail M f) = LinearMap.id := by
  apply LinearMap.ext
  intro z
  obtain ⟨i, x, rfl⟩ := Module.DirectLimit.exists_of z
  change moduleTailToOriginal M f (moduleOriginalToTail M f
    (Module.DirectLimit.of ℤ ℕ M f i x)) = _
  rw [moduleOriginalToTail_of, moduleTailToOriginal_of]
  exact Module.DirectLimit.of_f (R := ℤ) (f := f) (hij := Nat.le_succ i) (x := x)

theorem moduleOriginal_tail_inverse :
    (moduleOriginalToTail M f).comp (moduleTailToOriginal M f) = LinearMap.id := by
  apply LinearMap.ext
  intro z
  obtain ⟨i, x, rfl⟩ := Module.DirectLimit.exists_of z
  change moduleOriginalToTail M f (moduleTailToOriginal M f
    (Module.DirectLimit.of ℤ ℕ _ (moduleTailMap M f) i x)) = _
  rw [moduleTailToOriginal_of, moduleOriginalToTail_of]
  exact Module.DirectLimit.of_f (R := ℤ) (f := moduleTailMap M f)
    (hij := Nat.le_succ i) (x := x)

def sequentialModuleTailEquiv : ModuleTailLimit M f ≃ₗ[ℤ] Module.DirectLimit M f :=
  LinearEquiv.ofLinearMap (moduleTailToOriginal M f) (moduleOriginalToTail M f)
    (moduleTail_original_inverse M f) (moduleOriginal_tail_inverse M f)

end PolycyclicRecognition

end

end OAI
