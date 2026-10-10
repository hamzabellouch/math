import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Topology.Bases
import Mathlib.Basic.Denumerable

namespace OAI

namespace Hyperinvariant
open Submodule TopologicalSpace
universe u v
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- An orthonormal subset of a separable Hilbert space is countable. -/
theorem orthonormal_subtype_countable [CompleteSpace H] [SeparableSpace H] (w : Set H)
    (hw : Orthonormal ℂ (Subtype.val : w → H)) : Countable w := by
  classical
  let : DiscreteTopology w := discreteTopology_iff_isOpen_singleton.mpr (by
    intro i
    have ho : IsOpen {j : w | (1 / 2 : ℝ) < ‖inner ℂ (i : H) (j : H)‖} :=
      isOpen_lt continuous_const (continuous_const.inner continuous_subtype_val).norm
    have he : {j : w | (1 / 2 : ℝ) < ‖inner ℂ (i : H) (j : H)‖} = {i} := by
      ext j
      rw [Set.mem_ofPred_eq, orthonormal_iff_ite.mp hw i j]
      by_cases hij : i = j <;> simp [hij, eq_comm]; norm_num
    rwa [he] at ho)
  exact separableSpace_iff_countable.mp inferInstance

variable [CompleteSpace H] [SeparableSpace H]

/-- Every infinite-dimensional separable complex Hilbert space has a
Hilbert basis indexed by the natural numbers. -/
theorem exists_nat_hilbertBasis (hInf : ¬FiniteDimensional ℂ H) :
    Nonempty (HilbertBasis ℕ ℂ H) := by
  classical
  obtain ⟨w, b, hb⟩ := exists_hilbertBasis ℂ H
  have hw : Orthonormal ℂ (Subtype.val : w → H) := by
    simpa only [hb] using b.orthonormal
  let : Countable w := orthonormal_subtype_countable w hw
  let : Infinite w := by
    refine not_finite_iff_infinite.mp ?_
    intro hfin
    let : Finite w := hfin
    let : Fintype w := Fintype.ofFinite w
    exact hInf (Module.Finite.of_basis b.toOrthonormalBasis.toBasis)
  let e : ℕ ≃ w := Classical.choice (inferInstance : Nonempty (ℕ ≃ w))
  have ho : Orthonormal ℂ (b ∘ e) := b.orthonormal.comp e e.injective
  have hr : Set.range (b ∘ e) = Set.range b := by
    ext x
    constructor
    · rintro ⟨n, rfl⟩
      exact ⟨e n, rfl⟩
    · rintro ⟨i, rfl⟩
      exact ⟨e.symm i, by simp⟩
  exact ⟨HilbertBasis.mk ho (by rw [hr, b.dense_span])⟩

/-- This handles arbitrary ambient Hilbert spaces, not just a canonical model. -/
theorem nonempty_linearIsometryEquiv
    {K : Type v} [NormedAddCommGroup K] [InnerProductSpace ℂ K]
    [CompleteSpace K] [SeparableSpace K]
    (hH : ¬FiniteDimensional ℂ H) (hK : ¬FiniteDimensional ℂ K) :
    Nonempty (H ≃ₗᵢ[ℂ] K) := by
  obtain ⟨bH⟩ := exists_nat_hilbertBasis hH
  obtain ⟨bK⟩ := exists_nat_hilbertBasis hK
  exact ⟨bH.repr.trans bK.repr.symm⟩

end Hyperinvariant

end OAI
