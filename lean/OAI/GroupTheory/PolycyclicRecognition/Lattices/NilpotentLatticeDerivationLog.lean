import OAI.GroupTheory.PolycyclicRecognition.Geometry.AnalyticDerivationAction
import OAI.GroupTheory.PolycyclicRecognition.Lattices.NilpotentLatticeLinearAction
import OAI.GroupTheory.PolycyclicRecognition.Lattices.SmoothRealActionLattice
import OAI.GroupTheory.PolycyclicRecognition.Algebra.CyclicPowerIndex

namespace OAI

/-! # The cyclic lattice step from an actual derivation logarithm

The logarithm and its exponential equality remain a local algebraic
obligation. The real action and the Lie lattice are constructed here.
-/

noncomputable section
namespace PolycyclicRecognition.NilpotentLatticeCoordinates
variable {H : Type} [Group H] (C : NilpotentLatticeCoordinates H)

theorem cyclic_lattice_of_derivation_log (a : MulAut H)
    (D : LieDerivation ℝ C.carrier C.carrier)
    (hD : NormedSpace.exp (LinearMap.toContinuousLinearMap D.toLinearMap) =
      LinearMap.toContinuousLinearMap (C.automorphismLinear a)) :
    ∃ (S : SimplyConnectedSolvableLieModel) (Γ : Subgroup S.carrier),
      IsUniformLattice Γ ∧ Nonempty ((H ⋊[integerPowerAction a] Multiplicative ℤ) ≃* Γ) := by
  apply smooth_realAction_cyclic_lattice
    (PolynomialExponentialCoordinates.analyticDerivationAction D)
    (PolynomialExponentialCoordinates.analyticDerivationAction_smooth D)
    a C.lattice C.uniform C.equiv
  intro x
  change (C.equiv (a x) : C.carrier) = analyticDerivationFlow D 1 (C.equiv x)
  rw [analyticDerivationFlow, one_smul, analyticDerivationExp_apply, hD]
  change (C.equiv (a x) : C.carrier) = C.automorphismLinear a (C.equiv x)
  rw [C.automorphismLinear_apply]
  exact (C.automorphism_on_lattice a x).symm

theorem cyclic_finiteIndex_lattice_of_derivation_log (a : MulAut H)
    {m : ℕ} (hm : 0 < m) (D : LieDerivation ℝ C.carrier C.carrier)
    (hD : NormedSpace.exp (LinearMap.toContinuousLinearMap D.toLinearMap) =
      LinearMap.toContinuousLinearMap (C.automorphismLinear (a ^ m))) :
    ∃ Γ : Subgroup (H ⋊[integerPowerAction a] Multiplicative ℤ), Γ.FiniteIndex ∧
      ∃ (S : SimplyConnectedSolvableLieModel) (Λ : Subgroup S.carrier),
        IsUniformLattice Λ ∧ Nonempty (Γ ≃* Λ) := by
  obtain ⟨S, Λ, hΛ, ⟨e⟩⟩ := C.cyclic_lattice_of_derivation_log (a ^ m) D hD
  exact ⟨(cyclicPowerMap a m).range, cyclicPowerMap_range_finiteIndex a hm,
    S, Λ, hΛ, ⟨(cyclicPowerRangeEquiv a hm).symm.trans e⟩⟩

end PolycyclicRecognition.NilpotentLatticeCoordinates

end

end OAI
