import OAI.Analysis.FiniteFactor.CrossedProduct.TorusCharacters

namespace OAI

namespace FiniteFactor
open MeasureTheory Filter Set
open scoped ENNReal ComplexConjugate
noncomputable section

def sourceTorusRotationStep (θ : SourceCoordinate → ℝ) (x : SourceTorus) : SourceTorus :=
  x + sourceTorusQuotient θ

theorem sourceTorusRotationStep_preserving (θ : SourceCoordinate → ℝ) :
    MeasurePreserving (sourceTorusRotationStep θ) sourceTorusHaar sourceTorusHaar := by
  have hm (i : SourceCoordinate) : Measurable (fun z : UnitAddCircle => z + (θ i : UnitAddCircle)) := by fun_prop
  refine ⟨by unfold sourceTorusRotationStep; fun_prop,?_⟩
  change (Measure.infinitePi _).map (fun x i => x i + (θ i : UnitAddCircle)) = _
  rw [Measure.infinitePi_map_pi _ hm]
  simp only [(measurePreserving_add_right (volume : Measure UnitAddCircle) _).map_eq]

theorem sourceCharacter_translate (v : SourceCoordinate →₀ ℤ) (x y : SourceTorus) :
    sourceCharacter v (x+y) = sourceCharacter v x * sourceCharacter v y := by
  simp only [sourceCharacter, ContinuousMap.coe_mk,Pi.add_apply,smul_add,Finsupp.sum,
    Finset.sum_add_distrib]
  simp [fourier,AddCircle.toCircle_add]

/-- Rational independence rules out every nonconstant character eigenvalue 1. -/
theorem sourceCharacter_nonresonant (θ : SourceCoordinate → ℝ)
    (hr : SourceRationalIndependent θ) (v : SourceCoordinate →₀ ℤ) (hv : v ≠ 0) :
    sourceCharacter v (sourceTorusQuotient θ) ≠ 1 := by
  intro h
  have hz : v.sum (fun i n => n • (θ i : UnitAddCircle)) = 0 := by
    apply AddCircle.injective_toCircle one_ne_zero
    apply Subtype.ext
    simpa [sourceCharacter,fourier,sourceTorusQuotient] using h
  have he : ((v.sum fun i n => (n : ℝ)*θ i : ℝ) : UnitAddCircle) =
      v.sum (fun i n => n • (θ i : UnitAddCircle)) := by
    unfold Finsupp.sum
    induction v.support using Finset.induction_on with
    | empty => simp
    | @insert i s hi ih =>
      rw [Finset.sum_insert hi,Finset.sum_insert hi,AddCircle.coe_add,ih]
      congr 1
      simpa only [zsmul_eq_mul] using (AddCircle.coe_zsmul (1 : ℝ) (n := v i) (x := θ i))
  rw [← he,AddCircle.coe_eq_zero_iff] at hz
  obtain ⟨c,hc⟩ := hz
  exact hv (hr v c (by simpa using hc.symm)).1

theorem sourceCharacterL2_rotation (θ : SourceCoordinate → ℝ) (v : SourceCoordinate →₀ ℤ) :
    Lp.compMeasurePreserving (sourceTorusRotationStep θ) (sourceTorusRotationStep_preserving θ)
      (sourceCharacterL2 v) = sourceCharacter v (sourceTorusQuotient θ) • sourceCharacterL2 v := by
  apply Lp.ext
  have he := ContinuousMap.coeFn_toLp (𝕜 := ℂ) (p := (2 : ℝ≥0∞)) sourceTorusHaar (sourceCharacter v)
  filter_upwards [Lp.coeFn_compMeasurePreserving (sourceCharacterL2 v) (sourceTorusRotationStep_preserving θ),
    (sourceTorusRotationStep_preserving θ).quasiMeasurePreserving.ae he,he,
    Lp.coeFn_smul (sourceCharacter v (sourceTorusQuotient θ)) (sourceCharacterL2 v)]
    with x hc ht hx hs
  rw [hc,Function.comp_apply,ht,hs,Pi.smul_apply,smul_eq_mul,hx]
  exact (sourceCharacter_translate v x (sourceTorusQuotient θ)).trans (mul_comm _ _)

end
end FiniteFactor

end OAI
