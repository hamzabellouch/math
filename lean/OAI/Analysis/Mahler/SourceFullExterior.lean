import OAI.Analysis.Mahler.SourceRawOrientation

namespace OAI

open ContinuousAlternatingMap Filter
open scoped Topology
namespace Mahler
noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E]

def sourceComplexBoundaryForm (u : E → ℂ) (k : ℕ) (x : E) : E [⋀^Fin (2*k+1)]→L[ℝ] ℂ :=
  sourceReindex (sourceBoundarySlots k) (continuousSourceBoundaryForm u k x)

omit [FiniteDimensional ℝ E] in
lemma contDiffAt_dcLinear_source [FiniteDimensional ℝ E] {u : E → ℂ} {x : E}
    (hu : ContDiffAt ℝ 3 u x) : ContDiffAt ℝ 2 (dcLinear u) x := by
  have hd : ContDiffAt ℝ 2 (fderiv ℝ u) x := hu.fderiv_right (by norm_num)
  exact (((-1/4 : ℂ) • (ContinuousLinearMap.compL ℝ E E ℂ).flip complexStructure).contDiff.contDiffAt.comp x hd)

lemma sourceComplexBoundaryForm_raw {u : E → ℂ} {y : E}
    (ha : DifferentiableAt ℝ (dcLinear u) y) (k : ℕ) :
    (sourceComplexBoundaryForm u k y).toAlternatingMap =
      (rawBoundary (dcLinear u y).toLinearMap (rawFirstJet (fderiv ℝ (dcLinear u) y)) k).alternatization.domDomCongr
        (sourceBoundarySlots k) := by
  rw [rawBoundary_alternatization, rawFirstJet_alternatization ha]
  change (wedge _ _).domDomCongr _ = _
  rw [continuousWedgePower_toAlternatingMap]
  rfl

/-- The exterior derivative identity in every degree.
C3 of the potential supplies all product rules and the symmetric second
jet of dc; neither closedness nor a Stokes identity is assumed. -/
theorem extDeriv_sourceComplexBoundaryForm {u : E → ℂ} {x : E}
    (hu : ContDiffAt ℝ 3 u x) (k : ℕ) :
    (extDeriv (sourceComplexBoundaryForm u k) x).toAlternatingMap =
      (wedgePower (extDeriv (oneForm (dcLinear u)) x).toAlternatingMap (k+1)).domDomCongr
        (sourceTopSlots k) := by
  have ha := contDiffAt_dcLinear_source hu
  have hω : DifferentiableAt ℝ (sourceComplexBoundaryForm u k) x :=
    ((sourceReindexCLM (E := E) (sourceBoundarySlots k)).contDiff.contDiffAt.comp x
      (contDiffAt_sourceBoundaryForm hu k)).differentiableAt one_ne_zero
  have heq : ∀ᶠ y in 𝓝 x, (sourceComplexBoundaryForm u k y).toAlternatingMap =
      (rawBoundary (dcLinear u y).toLinearMap (rawFirstJet (fderiv ℝ (dcLinear u) y)) k).alternatization.domDomCongr
        (sourceBoundarySlots k) :=
    (ha.eventually (by norm_num)).mono (fun y hy => sourceComplexBoundaryForm_raw
      (hy.differentiableAt (by norm_num)) k)
  have hd := extDeriv_of_reindexed_raw (sourceBoundarySlots k) hω heq
    (rawBoundary_hasRawFDerivAt ha k)
  rw [rawBoundaryVariation_closed _ _ _ _ (rawSecondJet_closed ha) k] at hd
  calc
    (extDeriv (sourceComplexBoundaryForm u k) x).toAlternatingMap = _ := hd
    _ = (wedgePower (rawFirstJet (fderiv ℝ (dcLinear u) x)).alternatization (k+1)).domDomCongr
        (sourceTopSlots k) := by
      let reindexPair := Equiv.sumCongr (finSumFinEquiv : Fin 1 ⊕ Fin 1 ≃ Fin 2)
        (Equiv.refl (WedgePowerSlots k))
      have slots : reindexPair.trans (sourceTopSlots k) =
          (Equiv.sumAssoc (Fin 1) (Fin 1) (WedgePowerSlots k)).trans
            ((Equiv.sumCongr (Equiv.refl (Fin 1)) (sourceBoundarySlots k)).trans
              (rawFrontFin (2*k+1))) := by
        ext index
        simp only [sourceTopSlots, Equiv.trans_apply, reindexPair,
          Equiv.symm_apply_apply]
      let baseForm := wedge
        (rawPrefix (rawCovectorVariation (rawLinearJet (fderiv ℝ (dcLinear u) x)))).alternatization
        (wedgePower (rawFirstJet (fderiv ℝ (dcLinear u) x)).alternatization k)
      exact (congrArg (fun equivalence => baseForm.domDomCongr equivalence) slots.symm).trans
        (congrArg (fun form : E [⋀^WedgePowerSlots (k+1)]→ₗ[ℝ] ℂ =>
          form.domDomCongr (sourceTopSlots k))
          (rawMain_firstJet (fderiv ℝ (dcLinear u) x) k))
    _ = _ := by rw [rawFirstJet_alternatization (ha.differentiableAt (by norm_num))]

end
end Mahler

end OAI
