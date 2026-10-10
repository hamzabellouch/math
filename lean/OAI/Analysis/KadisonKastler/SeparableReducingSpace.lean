import OAI.Analysis.FactorGeneration.Bicommutant
import Mathlib.Topology.Algebra.Module.Basic

namespace OAI

/-! # A separable reducing subspace containing finitely many vectors

The closed complex span of the algebra orbits of a finite vector family
is separable when the algebra is norm separable. It is invariant under
the algebra and its adjoints, so its orthogonal projection commutes with
every element of the algebra.
-/

namespace KadisonKastler

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

def finiteAlgebraOrbit (A : StarSubalgebra ℂ (H →L[ℂ] H)) (V : Finset H) : Set H :=
  Set.range (fun p : A × V => (p.1 : H →L[ℂ] H) (p.2 : H))

def finiteReducingSpace (A : StarSubalgebra ℂ (H →L[ℂ] H)) (V : Finset H) :
    Submodule ℂ H :=
  (Submodule.span ℂ (finiteAlgebraOrbit A V)).topologicalClosure

theorem finiteAlgebraOrbit_subset (A : StarSubalgebra ℂ (H →L[ℂ] H)) (V : Finset H) :
    finiteAlgebraOrbit A V ⊆ finiteReducingSpace A V :=
  (Submodule.subset_span).trans (Submodule.le_topologicalClosure _)

theorem mem_finiteReducingSpace (A : StarSubalgebra ℂ (H →L[ℂ] H)) (V : Finset H)
    {v : H} (hv : v ∈ V) : v ∈ finiteReducingSpace A V := by
  apply finiteAlgebraOrbit_subset A V
  exact ⟨(1, ⟨v, hv⟩), by simp⟩

theorem isClosed_finiteReducingSpace (A : StarSubalgebra ℂ (H →L[ℂ] H))
    (V : Finset H) : IsClosed (finiteReducingSpace A V : Set H) :=
  Submodule.isClosed_topologicalClosure _

theorem isSeparable_finiteAlgebraOrbit (A : StarSubalgebra ℂ (H →L[ℂ] H))
    [TopologicalSpace.SeparableSpace A] (V : Finset H) :
    TopologicalSpace.IsSeparable (finiteAlgebraOrbit A V) := by
  apply TopologicalSpace.isSeparable_range
  exact (continuous_subtype_val.comp continuous_fst).clm_apply
    (continuous_subtype_val.comp continuous_snd)

instance finiteReducingSpaceSeparable (A : StarSubalgebra ℂ (H →L[ℂ] H))
    [TopologicalSpace.SeparableSpace A] (V : Finset H) :
    TopologicalSpace.SeparableSpace (finiteReducingSpace A V) := by
  have hs : TopologicalSpace.IsSeparable
      (Submodule.span ℂ (finiteAlgebraOrbit A V) : Set H) :=
    (isSeparable_finiteAlgebraOrbit A V).span
  exact hs.closure.separableSpace

theorem finiteReducingSpace_invariant (A : StarSubalgebra ℂ (H →L[ℂ] H))
    (V : Finset H) (a : A) {x : H} (hx : x ∈ finiteReducingSpace A V) :
    (a : H →L[ℂ] H) x ∈ finiteReducingSpace A V := by
  have h : finiteReducingSpace A V ≤
      (finiteReducingSpace A V).comap (a : H →L[ℂ] H).toLinearMap := by
    apply Submodule.topologicalClosure_minimal
    · apply Submodule.span_le.mpr
      rintro _ ⟨⟨b, v⟩, rfl⟩
      apply finiteAlgebraOrbit_subset A V
      exact ⟨(a * b, v), rfl⟩
    · exact (isClosed_finiteReducingSpace A V).preimage
        (a : H →L[ℂ] H).continuous
  exact h hx

instance finiteReducingSpaceComplete (A : StarSubalgebra ℂ (H →L[ℂ] H))
    (V : Finset H) : CompleteSpace (finiteReducingSpace A V) :=
  inferInstanceAs (CompleteSpace (Submodule.span ℂ (finiteAlgebraOrbit A V)).topologicalClosure)

theorem finiteReducingSpace_projection_commutes (A : StarSubalgebra ℂ (H →L[ℂ] H))
    (V : Finset H) (a : A) :
    (finiteReducingSpace A V).starProjection * (a : H →L[ℂ] H) =
      (a : H →L[ℂ] H) * (finiteReducingSpace A V).starProjection := by
  apply Generator.starProjection_commutes_of_invariant
  · exact fun x hx => finiteReducingSpace_invariant A V a hx
  · exact fun x hx => finiteReducingSpace_invariant A V (star a) hx

/-- The actual closed separable reducing subspace needed for finitely
many vector tests, with its projection commutation stated explicitly. -/
theorem exists_separable_reducingSpace (A : StarSubalgebra ℂ (H →L[ℂ] H))
    [TopologicalSpace.SeparableSpace A] (V : Finset H) :
    ∃ K : Submodule ℂ H, IsClosed (K : Set H) ∧
      TopologicalSpace.SeparableSpace K ∧
      (∀ v ∈ V, v ∈ K) ∧
      (∀ a : A, ∀ x ∈ K, (a : H →L[ℂ] H) x ∈ K) :=
  ⟨finiteReducingSpace A V, isClosed_finiteReducingSpace A V, inferInstance,
    fun _ hv => mem_finiteReducingSpace A V hv,
    fun a _ hx => finiteReducingSpace_invariant A V a hx⟩

end

end KadisonKastler

end OAI
