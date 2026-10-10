import OAI.GroupTheory.PolycyclicRecognition.Finiteness.FinitePresentationSequentialLimit

namespace OAI

/-! # Hom from a finitely presented module commutes with sequential limits

The comparison is an isomorphism of abelian groups, expressed as a linear
equivalence over the integers. This includes noncommutative group rings.
-/
noncomputable section
namespace PolycyclicRecognition

variable {R : Type*} [Ring R] {D : ℕ → Type*}
  [∀ i, AddCommGroup (D i)] [∀ i, Module R (D i)]
  (f : ∀ i j, i ≤ j → D i →ₗ[R] D j)
  [DirectedSystem D (fun i j h => f i j h)]
  (M : Type*) [AddCommGroup M] [Module R M]

def sequentialHomTransition (i j : ℕ) (h : i ≤ j) :
    (M →ₗ[R] D i) →ₗ[ℤ] (M →ₗ[R] D j) where
  toFun u := (f i j h).comp u
  map_add' u v := by ext x; simp
  map_smul' r u := by ext x; simp

instance sequentialHomTransition_directed :
    DirectedSystem (fun i => M →ₗ[R] D i)
      (fun i j h => sequentialHomTransition f M i j h) where
  map_self := by
    intro i u
    apply LinearMap.ext
    intro x
    exact DirectedSystem.map_self (f := fun i j h => f i j h) (u x)
  map_map := by
    intro k j i hij hjk u
    apply LinearMap.ext
    intro x
    exact DirectedSystem.map_map (f := fun i j h => f i j h) hij hjk (u x)

def sequentialHomCocone (i : ℕ) :
    (M →ₗ[R] D i) →ₗ[ℤ] (M →ₗ[R] Module.DirectLimit D f) where
  toFun u := (Module.DirectLimit.of R ℕ D f i).comp u
  map_add' u v := by ext x; simp
  map_smul' r u := by ext x; simp

def sequentialHomComparison :
    Module.DirectLimit (fun i => M →ₗ[R] D i) (sequentialHomTransition f M) →ₗ[ℤ]
      (M →ₗ[R] Module.DirectLimit D f) :=
  Module.DirectLimit.lift ℤ ℕ _ _ (sequentialHomCocone f M) (by
    intro i j hij u
    apply LinearMap.ext
    intro x
    exact Module.DirectLimit.of_f)

omit [DirectedSystem D (fun i j h => f i j h)] in
@[simp]
theorem sequentialHomComparison_of (i : ℕ) (u : M →ₗ[R] D i) :
    sequentialHomComparison f M
      (Module.DirectLimit.of ℤ ℕ _ (sequentialHomTransition f M) i u) =
        (Module.DirectLimit.of R ℕ D f i).comp u := by
  apply Module.DirectLimit.lift_of

theorem sequentialHomComparison_injective [Module.Finite R M] :
    Function.Injective (sequentialHomComparison f M) := by
  apply (injective_iff_map_eq_zero _).mpr
  intro x hx
  obtain ⟨i, u, rfl⟩ := Module.DirectLimit.exists_of x
  rw [sequentialHomComparison_of] at hx
  obtain ⟨j, hij, hj⟩ := sequentialLimit_eventually_zero_finite f i u hx
  have he := Module.DirectLimit.of_f (R := ℤ) (ι := ℕ)
    (G := fun i => M →ₗ[R] D i) (f := sequentialHomTransition f M)
    (hij := hij) (x := u)
  change Module.DirectLimit.of ℤ ℕ _ (sequentialHomTransition f M) j
    ((f i j hij).comp u) = _ at he
  rw [hj, map_zero] at he
  exact he.symm

theorem sequentialHomComparison_surjective [Module.FinitePresentation R M] :
    Function.Surjective (sequentialHomComparison f M) := by
  intro u
  obtain ⟨i, v, hv⟩ := sequentialLimit_lift_finitelyPresented f u
  exact ⟨Module.DirectLimit.of ℤ ℕ _ (sequentialHomTransition f M) i v,
    (sequentialHomComparison_of f M i v).trans hv⟩

def sequentialHomLimitEquiv [Module.FinitePresentation R M] :
    Module.DirectLimit (fun i => M →ₗ[R] D i) (sequentialHomTransition f M) ≃ₗ[ℤ]
      (M →ₗ[R] Module.DirectLimit D f) :=
  LinearEquiv.ofBijective (sequentialHomComparison f M)
    ⟨sequentialHomComparison_injective f M, sequentialHomComparison_surjective f M⟩

end PolycyclicRecognition

end

end OAI
