import OAI.Analysis.KadisonSimilarity.Derivation.CyclicFactorization
import Mathlib.Topology.Algebra.Module.Basic
import Mathlib.Topology.Metrizable.Basic

namespace OAI

/-! # Separable reducing subspaces for finitely many tests

Take the closed complex span of the orbit of finitely many vectors under
words in finitely many operators and their adjoints. The orbit is countable,
so the resulting Hilbert subspace is separable. No representation estimate
or separability assumption on the ambient space is used.
-/

noncomputable section
namespace KadisonSimilarity

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H] {m r : ℕ}

private def testLetter (T : Fin m → H →L[ℂ] H) (a : Fin m × Bool) : H →L[ℂ] H :=
  if a.2 then (T a.1).adjoint else T a.1

private def testWord (T : Fin m → H →L[ℂ] H) : List (Fin m × Bool) → H →L[ℂ] H
  | [] => 1
  | a :: w => testLetter T a * testWord T w

private def testOrbit (T : Fin m → H →L[ℂ] H) (ξ : Fin r → H) : Set H :=
  Set.range (fun p : List (Fin m × Bool) × Fin r => testWord T p.1 (ξ p.2))

/-- The canonical separable reducing space of a finite test family. -/
def separableReducingTestSpace (T : Fin m → H →L[ℂ] H) (ξ : Fin r → H) :
    ClosedSubmodule ℂ H :=
  (Submodule.span ℂ (testOrbit T ξ)).closure

instance separableReducingTestSpace_separable
    (T : Fin m → H →L[ℂ] H) (ξ : Fin r → H) :
    TopologicalSpace.SeparableSpace (separableReducingTestSpace T ξ) := by
  have hcount : (testOrbit T ξ).Countable := Set.countable_range _
  apply TopologicalSpace.IsSeparable.separableSpace
  change TopologicalSpace.IsSeparable
    (closure (Submodule.span ℂ (testOrbit T ξ) : Set H))
  exact (hcount.isSeparable.span (R := ℂ)).closure

theorem mem_separableReducingTestSpace (T : Fin m → H →L[ℂ] H)
    (ξ : Fin r → H) (i : Fin r) : ξ i ∈ separableReducingTestSpace T ξ := by
  apply (Submodule.span ℂ (testOrbit T ξ)).le_topologicalClosure
  apply Submodule.subset_span
  exact ⟨([], i), rfl⟩

private theorem testLetter_invariant (T : Fin m → H →L[ℂ] H)
    (ξ : Fin r → H) (a : Fin m × Bool) (x : H)
    (hx : x ∈ separableReducingTestSpace T ξ) :
    testLetter T a x ∈ separableReducingTestSpace T ξ := by
  have hspan : Submodule.span ℂ (testOrbit T ξ) ≤
      (Submodule.span ℂ (testOrbit T ξ)).comap (testLetter T a).toLinearMap := by
    apply Submodule.span_le.mpr
    rintro y ⟨⟨w, i⟩, rfl⟩
    apply Submodule.subset_span
    exact ⟨(a :: w, i), rfl⟩
  have hmap : Set.MapsTo (testLetter T a)
      (Submodule.span ℂ (testOrbit T ξ) : Set H)
      (Submodule.span ℂ (testOrbit T ξ) : Set H) := fun _ hy => hspan hy
  exact hmap.closure (testLetter T a).continuous hx

theorem separableReducingTestSpace_invariant (T : Fin m → H →L[ℂ] H)
    (ξ : Fin r → H) (i : Fin m) (x : H)
    (hx : x ∈ separableReducingTestSpace T ξ) :
    T i x ∈ separableReducingTestSpace T ξ :=
  testLetter_invariant T ξ (i, false) x hx

theorem separableReducingTestSpace_adjoint_invariant (T : Fin m → H →L[ℂ] H)
    (ξ : Fin r → H) (i : Fin m) (x : H)
    (hx : x ∈ separableReducingTestSpace T ξ) :
    (T i).adjoint x ∈ separableReducingTestSpace T ξ :=
  testLetter_invariant T ξ (i, true) x hx

/-- Reduction is an actual projection identity, not merely invariance. -/
theorem separableReducingTestSpace_projection_commutes
    (T : Fin m → H →L[ℂ] H) (ξ : Fin r → H) (i : Fin m) :
    Commute (separableReducingTestSpace T ξ).toSubmodule.starProjection (T i) := by
  let M := separableReducingTestSpace T ξ
  change M.toSubmodule.starProjection * T i = T i * M.toSubmodule.starProjection
  ext x
  apply Submodule.eq_starProjection_of_mem_of_inner_eq_zero
  · exact separableReducingTestSpace_invariant T ξ i _
      (Submodule.starProjection_apply_mem _ _)
  · intro w hw
    simp only [mul_apply_eq_comp]
    have hzero : inner ℂ (T i (x - M.toSubmodule.starProjection x)) w = 0 := by
      rw [← ContinuousLinearMap.adjoint_inner_right]
      exact M.toSubmodule.starProjection_inner_eq_zero x _
        (separableReducingTestSpace_adjoint_invariant T ξ i w hw)
    simpa only [map_sub, ContinuousLinearMap.coe_coe] using hzero

/-- Every finite collection of bounded operators and test vectors admits
a common separable closed reducing Hilbert subspace. -/
theorem exists_separable_reducing_test_space
    (T : Fin m → H →L[ℂ] H) (ξ : Fin r → H) :
    ∃ M : ClosedSubmodule ℂ H, TopologicalSpace.SeparableSpace M ∧
      (∀ i, ξ i ∈ M) ∧
      (∀ i x, x ∈ M → T i x ∈ M) ∧
      (∀ i x, x ∈ M → (T i).adjoint x ∈ M) ∧
      (∀ i, Commute M.toSubmodule.starProjection (T i)) :=
  ⟨separableReducingTestSpace T ξ, inferInstance,
    mem_separableReducingTestSpace T ξ,
    separableReducingTestSpace_invariant T ξ,
    separableReducingTestSpace_adjoint_invariant T ξ,
    separableReducingTestSpace_projection_commutes T ξ⟩

end KadisonSimilarity

end

end OAI
