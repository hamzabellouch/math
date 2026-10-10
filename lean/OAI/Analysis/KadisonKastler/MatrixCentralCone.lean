import OAI.Analysis.KadisonKastler.MatrixCentralCorner
import OAI.Analysis.KadisonKastler.ModularPositiveCone

namespace OAI

/-! # Matrix corner maps preserve the generated positive cone

Both directions of the corner partial isometry are positive sums of
modular quadratic operators. The central-vector projection therefore
preserves this cone as well.
-/

namespace KadisonKastler

open Generator
open scoped BigOperators

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {M : VonNeumannAlgebra H}

omit [CompleteSpace H] in
private theorem complex_ofReal_smul (r : ℝ) (η : H) : Complex.ofReal r • η = r • η := by
  simpa only [Complex.coe_algebraMap] using (IsScalarTower.algebraMap_smul ℂ r η)

theorem modularPositiveCone_sum_mem (J : H ≃ₗᵢ⋆[ℂ] H) (ξ : H)
    {ι : Type*} (s : Finset ι) (v : ι → H)
    (hv : ∀ i ∈ s, v i ∈ modularPositiveCone (M := M) J ξ) :
    ∑ i ∈ s, v i ∈ modularPositiveCone (M := M) J ξ := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa only [Finset.sum_empty] using zero_mem_modularPositiveCone (M := M) J ξ
  | @insert i s hi ih =>
    rw [Finset.sum_insert hi]
    exact (modularPositiveCone J ξ).add_mem (hv i (Finset.mem_insert_self i s))
      (ih (fun j hj => hv j (Finset.mem_insert_of_mem hj)))

variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
  (E : MatrixUnitSystem ι (Algebra M))
  (J : H ≃ₗᵢ⋆[ℂ] H) (hJ : Function.Involutive J)
  (hright : ∀ a : Algebra M, conjugationOperator J a.val ∈ M.commutant)
  (ξ : H)

include hright in
theorem matrixCentralColumn_preserves_positiveCone (o : ι) {η : H}
    (hη : η ∈ modularPositiveCone (M := M) J ξ) :
    matrixCentralColumn E J hJ o η ∈ modularPositiveCone (M := M) J ξ := by
  have hs : ∑ i, modularQuadratic J (E.entry i o) η ∈ modularPositiveCone (M := M) J ξ :=
    modularPositiveCone_sum_mem J ξ Finset.univ _
      (fun i _ => modularQuadratic_preserves_positiveCone J hJ hright ξ _ hη)
  have hc : 0 < (Real.sqrt (Fintype.card ι))⁻¹ :=
    inv_pos.mpr (Real.sqrt_pos.mpr (Nat.cast_pos.mpr Fintype.card_pos))
  have h := (modularPositiveCone (M := M) J ξ).smul_mem hc hs
  change Complex.ofReal ((Real.sqrt (Fintype.card ι))⁻¹) •
    ((∑ i, (E.entry i o).val * conjugationOperator J (E.entry i o).val) η) ∈ _
  simpa only [sum_apply,modularQuadratic,mul_apply_eq_comp,← complex_ofReal_smul] using h

include hright in
theorem matrixCentralColumn_star_preserves_positiveCone (o : ι) {η : H}
    (hη : η ∈ modularPositiveCone (M := M) J ξ) :
    star (matrixCentralColumn E J hJ o) η ∈ modularPositiveCone (M := M) J ξ := by
  have hs : ∑ i, modularQuadratic J (E.entry o i) η ∈ modularPositiveCone (M := M) J ξ :=
    modularPositiveCone_sum_mem J ξ Finset.univ _
      (fun i _ => modularQuadratic_preserves_positiveCone J hJ hright ξ _ hη)
  have hc : 0 < (Real.sqrt (Fintype.card ι))⁻¹ :=
    inv_pos.mpr (Real.sqrt_pos.mpr (Nat.cast_pos.mpr Fintype.card_pos))
  have h := (modularPositiveCone (M := M) J ξ).smul_mem hc hs
  have hcomm (i j k l : ι) : Commute (E.entry i j).val
      (conjugationOperator J (E.entry k l).val) :=
    VonNeumannAlgebra.mem_commutant_iff.mp (hright (E.entry k l))
      (E.entry i j).val (E.entry i j).property
  change star (pairedMatrixColumn (E.map M.toStarSubalgebra.subtype)
    (conjugateMatrixUnits J hJ (E.map M.toStarSubalgebra.subtype)) o) η ∈ _
  rw [pairedMatrixColumn_star _ _ hcomm]
  change Complex.ofReal ((Real.sqrt (Fintype.card ι))⁻¹) •
    ((∑ i, (E.entry o i).val * conjugationOperator J (E.entry o i).val) η) ∈ _
  simpa only [sum_apply,modularQuadratic,mul_apply_eq_comp,← complex_ofReal_smul] using h

include hJ hright in
theorem matrixCentralProjection_preserves_positiveCone (o : ι) {η : H}
    (hη : η ∈ modularPositiveCone (M := M) J ξ) :
    (centralVectorSpace (matrixUnitConcreteAlgebra E) J).starProjection η ∈
      modularPositiveCone (M := M) J ξ := by
  rw [← matrixCentralColumn_final E J hJ hright o,mul_apply_eq_comp]
  exact matrixCentralColumn_preserves_positiveCone E J hJ hright ξ o
    (matrixCentralColumn_star_preserves_positiveCone E J hJ hright ξ o hη)

end

end KadisonKastler

end OAI
