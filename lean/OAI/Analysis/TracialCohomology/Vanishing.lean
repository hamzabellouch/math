import Mathlib
import OAI.Analysis.BoundedHochschild.CocycleNormalParts
import OAI.Analysis.BoundedHochschild.FactorFinitePaths
import OAI.Analysis.BoundedHochschild.FreeWords
import OAI.Analysis.BoundedHochschild.MatrixDisplacement
import OAI.Analysis.BoundedHochschild.UnitaryLifts
import OAI.Analysis.TracialCohomology.TracialPrimitives
import OAI.Analysis.TracialCohomology.NormalReduction
import OAI.Analysis.TracialCohomology.Cohomology

namespace OAI

/-! Vanishing for bounded Hochschild cohomology. -/

noncomputable section
open Filter Topology MeasureTheory
open scoped BigOperators ComplexOrder InnerProductSpace ComplexStarModule CStarAlgebra

namespace BoundedHochschild
universe u v

lemma differential_eq_zero_iff {M : Type*} [CStarAlgebra M] {n : ℕ}
    (f : Cochain M n) :
    differential f = 0 ↔ ∀ x, differentialValue f x = 0 := by
  constructor
  · intro h x
    simpa only [differential_apply, zero_apply] using
      congrArg (fun F : Cochain M (n+1) => F x) h
  · intro h
    ext x
    simpa only [differential_apply, zero_apply] using h x

lemma separatelyNormal_iff_tracialSeparatelyNormal
    {M X : Type u} [CStarAlgebra M]
    [NormedAddCommGroup X] [NormedSpace ℂ X]
    (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M) {n : ℕ} (f : Cochain M n) :
    SeparatelyNormal e f ↔ TracialSeparatelyNormal e f := by
  constructor
  · intro h x i z
    exact h i x z
  · intro h i x z
    exact h x i z

theorem wstar_normal_reduction
    (M : Type u) [CStarAlgebra M] [WStarAlgebra M]
    (k : ℕ) (hk : 2 ≤ k) (f : Cochain M k) (hf : differential f = 0) :
    ∃ (X : Type u) (_ : NormedAddCommGroup X) (_ : NormedSpace ℂ X)
      (_ : CompleteSpace X) (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)
      (F : Cochain M k) (b : Cochain M (k-1)),
      SeparatelyNormal e F ∧ differential F = 0 ∧
      f = F + incomingDifferential M k b := by
  obtain ⟨X, hX, hXS, hXC, ⟨e⟩⟩ := WStarAlgebra.exists_predual (M := M)
  let := hX
  let := hXS
  let := hXC
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le' hk
  obtain ⟨F, b, hFN, hFc, hfb⟩ :=
    normal_reduction_any e (by omega : 1 ≤ n+1) f ((differential_eq_zero_iff f).mp hf)
  refine ⟨X, hX, hXS, hXC, e, F, b, hFN,
    (differential_eq_zero_iff F).mpr hFc, ?_⟩
  ext x
  simpa only [add_apply, incomingDifferential_succ, differential_apply] using hfb x

theorem tracial_bounded_hochschild_vanishing
    {M X : Type u} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
    [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]
    (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M) (τ : M →ₚ[ℂ] ℂ)
    (hτ : TraceInPredual e τ) (htr : ∀ a b : M, τ (a*b) = τ (b*a))
    (hfaith : ∀ a : M, τ (star a*a) = 0 → a = 0) (h1 : τ 1 = 1)
    (hII : PopaTypeII.NoTypeICentralPart M) (k : ℕ) (hk : 2 ≤ k) :
    (∀ f : Cochain M k, differential f = 0 →
      ∃ g : Cochain M (k-1), incomingDifferential M k g = f) ∧
    Subsingleton (Cohomology M k) := by
  have h : ∀ f : Cochain M k, differential f = 0 →
      ∃ g : Cochain M (k-1), incomingDifferential M k g = f := by
    obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le' hk
    intro f hf
    obtain ⟨g, _, hg⟩ := source_tracial_ordinary_primitive e τ hτ htr hfaith h1 hII
      f ((differential_eq_zero_iff f).mp hf)
    refine ⟨g, ?_⟩
    apply ContinuousMultilinearMap.ext
    intro x
    simpa only [incomingDifferential_succ, differential_apply] using hg x
  exact ⟨h, (cohomology_subsingleton_iff M k).mpr h⟩

theorem operators_bounded_hochschild_vanishing
    (H : Type u) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (k : ℕ) (hk : 1 ≤ k) :
    (∀ f : Cochain (H →L[ℂ] H) k, differential f = 0 →
      ∃ g : Cochain (H →L[ℂ] H) (k-1),
        incomingDifferential (H →L[ℂ] H) k g = f) ∧
    Subsingleton (Cohomology (H →L[ℂ] H) k) := by
  have h : ∀ f : Cochain (H →L[ℂ] H) k, differential f = 0 →
      ∃ g : Cochain (H →L[ℂ] H) (k-1),
        incomingDifferential (H →L[ℂ] H) k g = f := by
    obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le' hk
    intro f hf
    obtain ⟨g, _, hg⟩ := primitive_on_operators f ((differential_eq_zero_iff f).mp hf)
    refine ⟨g, ?_⟩
    apply ContinuousMultilinearMap.ext
    intro x
    simpa only [incomingDifferential_succ, differential_apply] using hg x
  exact ⟨h, (cohomology_subsingleton_iff (H →L[ℂ] H) k).mpr h⟩

end BoundedHochschild

end

end OAI
