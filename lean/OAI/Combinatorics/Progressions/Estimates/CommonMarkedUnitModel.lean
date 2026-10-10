import OAI.Combinatorics.Progressions.Dynamics.CommonMarkedUnitBudget
import OAI.Combinatorics.Progressions.Lattices.LocalMarkedLatticeCorrection

namespace OAI

section

namespace Erdos3.NativeRankRelation.CommonData

open Module
open scoped TensorProduct

attribute [local instance] NativeDegreeRankFamily.lie NativeDegreeRankFamily.algebra
  NativeDegreeRankFamily.topology NativeDegreeRankFamily.topologicalAdd
  NativeDegreeRankFamily.continuousSMul NativeDegreeRankFamily.hausdorff
  NativeIntegerExpansion.lie NativeIntegerExpansion.algebra
  NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd
  NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

def HasMarkedUnitModel {s r N : ℕ} [NeZero N] {b p q P M : ℝ}
    {W : NativeDegreeRankFamily s r (ZMod N) b} {out : Fin W.outputDim}
    {H : Finset (ZMod N)} {R : NativeRankRelation W out H p q}
    (D : R.CommonData P) (B : D.CoefficientBases M) (t : ℕ) (x : Fin t → ℚ)
    (l : ℕ) (Q : ℝ) : Prop :=
  ∃ d : ℕ,
    ∃ E : RationalFilteredNilmanifold
      (MarkedShiftQuotient D.coefficientFreeFiltration D.coefficientFreeGenerator
        D.coefficientWeight D.coefficientIsDependent t) (s + 1) d,
      ∃ T : E.MultidegreeStructure (mixedCorrelationDegree s),
        ∃ ξ : MarkedShiftQuotient D.coefficientFreeFiltration D.coefficientFreeGenerator
          D.coefficientWeight D.coefficientIsDependent t →ₗ[ℚ] ℚ,
          T.filtration = D.markedQuotientMultidegree t ∧
          T.ComplexityLE Q ∧ l ∣ E.grid ∧
          bchSubgroupCoordinates E.basis E.lattice = scaledIntegerGrid E.grid ∧
          (∀ i j, rationalLogHeight
            (E.basis.repr (markedQuotientDirection D.coefficientFreeFiltration D.coefficientFreeGenerator
              D.coefficientWeight D.coefficientIsDependent t (RationalTorus.basis t i)) j) ≤
                Q) ∧
          (∀ i, rationalLogHeight (ξ (E.basis i)) ≤ Q) ∧
          (∀ z ∈ markedShiftPolynomialSubmodule D.coefficientFreeFiltration D.coefficientFreeGenerator
              D.coefficientWeight D.coefficientIsDependent t s 1 r,
            ξ (lieQuotientMap (markedShiftSecondIdeal D.coefficientFreeFiltration D.coefficientFreeGenerator
                D.coefficientWeight D.coefficientIsDependent t) z) =
              B.freeFrequency D (markedShiftEval D.coefficientFreeFiltration D.coefficientFreeGenerator
                D.coefficientWeight D.coefficientIsDependent t x z)) ∧
          (∀ z : E.filtration.Group, z ∈ E.lattice → ∃ n : ℤ, ξ z.coord = n) ∧
          ∃ m : ℕ, 0 < m ∧ (m : ℝ) ≤ Real.exp Q ∧
            (∀ (u c : Fin t → ℝ) (h₀ h : ZMod N),
              D.scaledLocalAffineCorrectingElement t u c h₀ m h ∈ E.realLattice) ∧
            (letI := moduleTopology ℝ (ℝ ⊗[ℚ] MarkedShiftQuotient D.coefficientFreeFiltration
                D.coefficientFreeGenerator D.coefficientWeight D.coefficientIsDependent t)
             letI : IsTopologicalAddGroup (ℝ ⊗[ℚ] MarkedShiftQuotient D.coefficientFreeFiltration
                D.coefficientFreeGenerator D.coefficientWeight D.coefficientIsDependent t) :=
                  IsModuleTopology.isTopologicalAddGroup ℝ _
             letI := realification_moduleTopology_t2 E.basis
             ∃ n : ℕ, 0 < n ∧ (n : ℝ) ≤ Real.exp Q ∧
               ∃ V : E.UnitVerticalObservable (E.filtration.realification.subgroup (s + 1))
                 (Fin n) Q, V.frequency = ξ)

theorem exists_native_marked_unit_model (s : ℕ) (hs : 1 ≤ s) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {r N : ℕ} [NeZero N] {b p q P M : ℝ}
      {W : NativeDegreeRankFamily s r (ZMod N) b} {out : Fin W.outputDim}
      {H : Finset (ZMod N)} {R : NativeRankRelation W out H p q}
      (D : R.CommonData P) (B : D.CoefficientBases M) (t : ℕ) (x : Fin t → ℚ) (l : ℕ),
      0 ≤ M → b ≤ M → (t : ℝ) ≤ M → (∀ i, rationalLogHeight (x i) ≤ M) →
      0 < l → (l : ℝ) ≤ Real.exp M →
      D.HasMarkedUnitModel B t x l ((M + C) ^ C) := by
  obtain ⟨a, _, hmodel⟩ := exists_native_marked_local_correction_model s hs
  obtain ⟨cUnit, _, hunit⟩ := RationalFilteredNilmanifold.exists_canonical_prescribed_unit_with_budget (s + 1)
  obtain ⟨C, hC, hbudget⟩ := exists_commonMarkedUnit_budget a cUnit
  refine ⟨C, hC, ?_⟩
  intro r N _ b p q P M W out H R D B t x l hM hbM ht hx hl hlM
  unfold HasMarkedUnitModel
  obtain ⟨hbase, hobs, hscale⟩ := hbudget M hM
  obtain ⟨d, E, T, ξ, hTF, hT, hdiv, hcoords, hdirection, hξ, hpreserve, hintegral,
      m, hm, hmb, hmem⟩ := hmodel D B t x l hM hbM ht hx hl hlM
  have hbase0 : 0 ≤ (M + a) ^ a := by positivity
  refine ⟨d, E, T, ξ, hTF, hT.mono T hbase, hdiv, hcoords,
    (fun i j => (hdirection i j).trans hbase), (fun i => (hξ i).trans hbase),
    hpreserve, hintegral, m, hm, hmb.trans (Real.exp_le_exp.mpr hscale), hmem, ?_⟩
  exact hunit E hbase0 hT.1 ξ hξ hintegral ((M + C) ^ C) hobs

end Erdos3.NativeRankRelation.CommonData

end

end OAI
