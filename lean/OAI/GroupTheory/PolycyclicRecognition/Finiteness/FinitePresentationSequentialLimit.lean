import Mathlib.Algebra.Module.FinitePresentation
import Mathlib.Algebra.Colimit.Module

namespace OAI

/-! # Finite presentation and sequential module limits

Finite generators can be moved to one stage, and finitely many relations
vanish at one later stage. The ring need not be commutative, as required for
integral group rings.
-/
noncomputable section
namespace PolycyclicRecognition

variable {R : Type*} [Ring R] {D : ℕ → Type*}
  [∀ i, AddCommGroup (D i)] [∀ i, Module R (D i)]
  (f : ∀ i j, i ≤ j → D i →ₗ[R] D j)
  [DirectedSystem D (fun i j h => f i j h)]

omit [DirectedSystem D (fun i j h => f i j h)] in
theorem sequentialLimit_lift_finite_free (n : ℕ)
    (u : (Fin n → R) →ₗ[R] Module.DirectLimit D f) :
    ∃ (i : ℕ) (v : (Fin n → R) →ₗ[R] D i),
      (Module.DirectLimit.of R ℕ D f i).comp v = u := by
  classical
  let b := Pi.basisFun R (Fin n)
  choose k x hx using fun a : Fin n => Module.DirectLimit.exists_of (u (b a))
  let i := Finset.univ.sup k
  have hk (a : Fin n) : k a ≤ i := Finset.le_sup (f := k) (Finset.mem_univ a)
  refine ⟨i, b.constr ℕ (fun a => f (k a) i (hk a) (x a)), ?_⟩
  apply b.ext
  intro a
  simp only [LinearMap.comp_apply, Module.Basis.constr_basis]
  rw [Module.DirectLimit.of_f, hx]

theorem sequentialLimit_eventually_zero_finite
    {M : Type*} [AddCommGroup M] [Module R M] [Module.Finite R M]
    (i : ℕ) (u : M →ₗ[R] D i)
    (hu : (Module.DirectLimit.of R ℕ D f i).comp u = 0) :
    ∃ (j : ℕ) (hij : i ≤ j), (f i j hij).comp u = 0 := by
  classical
  obtain ⟨n, π, hπ⟩ := Module.Finite.exists_fin' R M
  let b := Pi.basisFun R (Fin n)
  have hz (a : Fin n) : Module.DirectLimit.of R ℕ D f i (u (π (b a))) = 0 :=
    LinearMap.congr_fun hu (π (b a))
  choose k hk he using fun a => Module.DirectLimit.of.zero_exact (hz a)
  let j := max i (Finset.univ.sup k)
  have hij : i ≤ j := le_max_left _ _
  have hkj (a : Fin n) : k a ≤ j :=
    (Finset.le_sup (f := k) (Finset.mem_univ a)).trans (le_max_right _ _)
  have hzero : ((f i j hij).comp u).comp π = 0 := by
    apply b.ext
    intro a
    change f i j hij (u (π (b a))) = 0
    rw [← DirectedSystem.map_map (f := fun i j h => f i j h) (hk a) (hkj a)]
    rw [he a, map_zero]
  refine ⟨j, hij, ?_⟩
  ext x
  obtain ⟨y, rfl⟩ := hπ x
  exact LinearMap.congr_fun hzero y

theorem sequentialLimit_lift_finitelyPresented
    {M : Type*} [AddCommGroup M] [Module R M] [Module.FinitePresentation R M]
    (u : M →ₗ[R] Module.DirectLimit D f) :
    ∃ (i : ℕ) (v : M →ₗ[R] D i), (Module.DirectLimit.of R ℕ D f i).comp v = u := by
  obtain ⟨n, m, π, r, hπ, hr⟩ := Module.FinitePresentation.exists_fin' R M
  obtain ⟨i, v, hv⟩ := sequentialLimit_lift_finite_free f n (u.comp π)
  have hvr : (Module.DirectLimit.of R ℕ D f i).comp (v.comp r) = 0 := by
    rw [← LinearMap.comp_assoc, hv, LinearMap.comp_assoc]
    have hπr : π.comp r = 0 := by
      apply LinearMap.ext
      intro x
      exact hr.apply_apply_eq_zero x
    rw [hπr, LinearMap.comp_zero]
  obtain ⟨j, hij, hj⟩ := sequentialLimit_eventually_zero_finite f i (v.comp r) hvr
  let w := (f i j hij).comp v
  have hker : LinearMap.ker π ≤ LinearMap.ker w := by
    intro x hx
    obtain ⟨y, rfl⟩ := (hr x).mp hx
    exact LinearMap.congr_fun hj y
  let v' := (Submodule.liftQ (LinearMap.ker π) w hker).comp
    (LinearMap.quotKerEquivOfSurjective π hπ).symm.toLinearMap
  refine ⟨j, v', ?_⟩
  ext x
  obtain ⟨y, rfl⟩ := hπ x
  change Module.DirectLimit.of R ℕ D f j
    ((Submodule.liftQ (LinearMap.ker π) w hker)
      ((LinearMap.quotKerEquivOfSurjective π hπ).symm (π y))) = u (π y)
  rw [LinearMap.quotKerEquivOfSurjective_symm_apply]
  change Module.DirectLimit.of R ℕ D f j (f i j hij (v y)) = u (π y)
  rw [Module.DirectLimit.of_f]
  exact LinearMap.congr_fun hv y

end PolycyclicRecognition

end

end OAI
