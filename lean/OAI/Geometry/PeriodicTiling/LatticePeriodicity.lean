import OAI.Geometry.PeriodicTiling.EuclideanBasic
import OAI.Geometry.PeriodicTiling.TilingTransport
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.LinearAlgebra.Basis.SMul
import Mathlib.LinearAlgebra.StdBasis

namespace OAI

noncomputable section

namespace PeriodicTilingThree

def scaledCoordinateBasis (d q : ℕ) (hq : q ≠ 0) : Module.Basis (Fin d) ℝ (Space d) :=
  (Units.mk0 (q : ℝ) (Nat.cast_ne_zero.mpr hq)) • Pi.basisFun ℝ (Fin d)

theorem scaledCoordinateBasis_eq_cast {d q : ℕ} (hq : q ≠ 0) (i : Fin d) :
    scaledCoordinateBasis d q hq i =
      castLattice (q • (Pi.single i 1 : Lattice d)) := by
  classical
  ext j
  by_cases hji : j = i
  · subst j
    simp [scaledCoordinateBasis, Module.Basis.smul_apply, Units.smul_def]
  · simp [scaledCoordinateBasis, Module.Basis.smul_apply,
      hji]

theorem exists_positive_scalar_sublattice {d : ℕ} (P : AddSubgroup (Lattice d))
    (hP : P.FiniteIndex) : ∃ q : ℕ, 0 < q ∧ ∀ z : Lattice d, q • z ∈ P := by
  refine ⟨P.index, Nat.pos_of_ne_zero hP.index_ne_zero, ?_⟩
  intro z
  exact P.nsmul_index_mem z

theorem FullyPeriodic.castLattice_image {d : ℕ} {A : Set (Lattice d)}
    (hA : FullyPeriodic A) : EuclideanFullyPeriodic (castLattice '' A) := by
  classical
  obtain ⟨P, hP, hPeriods⟩ := hA
  obtain ⟨q, hq, hqP⟩ := exists_positive_scalar_sublattice P hP
  refine ⟨scaledCoordinateBasis d q hq.ne', ?_⟩
  intro v hv
  change v ∈ Submodule.span ℤ (Set.range (scaledCoordinateBasis d q hq.ne')) at hv
  induction hv using Submodule.span_induction with
  | mem v hv =>
      obtain ⟨i, rfl⟩ := hv
      rw [scaledCoordinateBasis_eq_cast]
      exact (hPeriods _ (hqP (Pi.single i 1))).image castLattice
  | zero => exact period_zero _
  | add x y _ _ hx hy => exact hx.add hy
  | smul n x _ hx =>
      exact (periodSubgroup (castLattice '' A)).zsmul_mem hx n

end PeriodicTilingThree

end

end OAI
