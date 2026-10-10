import Mathlib
import OAI.Analysis.CoulombIonization.RadialBounds.PatchAverageSubmeanBarrier

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

namespace CoulombAtom

 def thinFieldUniversalConstant : ℝ := (1+localFieldUniversalConstant)*
    (4+1024*localFieldUniversalConstant+(512*localFieldUniversalConstant)^2)
lemma thinFieldUniversalConstant_pos : 0 < thinFieldUniversalConstant := by
  have := localFieldUniversalConstant_pos
  unfold thinFieldUniversalConstant
  positivity
lemma thinFieldUniversalConstant_one_le : 1 ≤ thinFieldUniversalConstant := by
  have hC := localFieldUniversalConstant_pos
  have hT := sq_nonneg (512*localFieldUniversalConstant)
  unfold thinFieldUniversalConstant
  nlinarith

lemma thinFieldBase_nonneg {a b D B : ℝ} (ha : 0 < a) (hb : 0 < b) (hD : 0 ≤ D) (hB : 0 ≤ B) :
    0 ≤ thinFieldBase a b D B := by
  unfold thinFieldBase
  exact add_nonneg (localFieldScale_nonneg ha hD hB)
    (by have := localizationIMSConstant_nonneg; positivity)

lemma countSqScale_le_thinFieldBase {a b D B : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hD : 0 ≤ D) (_hB : 0 ≤ B) :
    B/a^2 ≤ thinFieldBase a b D B := by
  have h1 : 0 ≤ (1/a^4+1/a)^2+1/a^4+D/a := by positivity
  have h2 : 0 ≤ localizationIMSConstant*Real.sqrt B/(b^2*a) := by
    have := localizationIMSConstant_nonneg
    positivity
  unfold thinFieldBase localFieldScale
  linarith

lemma thin_majorants_le_uniform {a b D B : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hD : 0 ≤ D) (hB : 0 ≤ B) :
    thinOutMajorant a b D B ≤ thinFieldUniversalConstant*thinFieldBase a b D B ∧
    thinFieldMajorant a b D B ≤ thinFieldUniversalConstant*thinFieldBase a b D B := by
  let U := thinFieldBase a b D B
  let C := localFieldUniversalConstant
  let T := 4+1024*C+(512*C)^2
  have hU : 0 ≤ U := thinFieldBase_nonneg ha hb hD hB
  have hC : 0 ≤ C := localFieldUniversalConstant_pos.le
  have hT : 4 ≤ T := by
    dsimp [T]
    nlinarith [sq_nonneg (512*C)]
  have hTU := mul_le_mul_of_nonneg_right hT hU
  have hBU : B/a^2 ≤ U := countSqScale_le_thinFieldBase ha hb hD hB
  have ho : thinOutMajorant a b D B ≤ T*U := by
    have h := mul_le_mul_of_nonneg_left hBU (sq_nonneg (512*C))
    change 1024*C*U+(512*C)^2*B/a^2 ≤ T*U
    calc _ = 1024*C*U+(512*C)^2*(B/a^2) := by ring
         _ ≤ 1024*C*U+(512*C)^2*U := add_le_add le_rfl h
         _ ≤ T*U := by dsimp [T]; nlinarith
  have ho' : thinOutMajorant a b D B ≤ thinFieldUniversalConstant*U := by
    calc _ ≤ T*U := ho
         _ ≤ (1+C)*T*U := by nlinarith [mul_nonneg hC (mul_nonneg (by linarith : 0 ≤ T) hU)]
         _ = _ := rfl
  have hf : thinFieldMajorant a b D B ≤ C*T*U := by
    have h : U+(thinOutMajorant a b D B+B/a^2)/2 ≤ T*U := by linarith
    exact (mul_le_mul_of_nonneg_left h hC).trans_eq (by ring)
  refine ⟨ho',hf.trans ?_⟩
  change C*T*U ≤ (1+C)*T*U
  nlinarith [mul_nonneg (by linarith : 0 ≤ T) hU]

theorem freshOutMaximum_thin_bound {N : ℕ} {ψ : FormVector N}
    (hψ : SobolevFermion ψ) (hm : formMass ψ = 1) (y : Space) {a r b Z lam : ℝ}
    (ha : 0 < a) (hr : 0 ≤ r) (hra : r ≤ 6*a) (hb : 0 < b) (hba : b ≤ a)
    (hsep : 20*a ≤ ‖y‖) (hZ : 0 ≤ Z) (hlam : 0 < lam) :
    freshOutMaximumSecondMoment (coreFirstRadialCut y hr hb) (coreFirstRadialCut_partition y hr hb) ψ Z lam ≤
      thinFieldUniversalConstant*thinFieldBase a b (max (corePriceExcess Z lam ψ) 0)
        (rawCountMoment ψ y (16*a)) := by
  let E := CoreObservationEnsemble.initial ψ hψ
  have hh := E.thin_out_bound y ha hr hra hb hba hsep
    (by simpa [E,CoreObservationEnsemble.initial_mass] using hm) hZ hlam
  rw [CoreObservationEnsemble.initial_outMoment ψ hψ y hr hb (by linarith) hZ hlam.le,
    CoreObservationEnsemble.initial_excess,CoreObservationEnsemble.initial_countMoment] at hh
  exact hh.trans (thin_majorants_le_uniform ha hb (le_max_right _ _) (rawCountMoment_nonneg _ _ _)).1

theorem freshPatchMass_thin_bound {N : ℕ} {ψ : FormVector N}
    (hψ : SobolevFermion ψ) (hm : formMass ψ = 1) (y : Space) {a r b Z lam : ℝ}
    (ha : 0 < a) (hr : 0 ≤ r) (hra : r ≤ 6*a) (hb : 0 < b) (hrb : 4*b < r) (hba : b ≤ a)
    (hsep : 20*a ≤ ‖y‖) (hZ : 0 ≤ Z) (hlam : 0 < lam) :
    freshPatchMass (coreFirstRadialCut y hr hb) (coreFirstRadialCut_partition y hr hb) ψ Z lam y (r-4*b) ≤
      768*a*Real.sqrt (thinFieldUniversalConstant*thinFieldBase a b (max (corePriceExcess Z lam ψ) 0)
        (rawCountMoment ψ y (16*a))) := by
  let E := CoreObservationEnsemble.initial ψ hψ
  apply freshPatchMass_le_ballField hψ hm y ha hr hra hb hrb (by linarith) hZ hlam.le
    (mul_nonneg thinFieldUniversalConstant_pos.le
      (thinFieldBase_nonneg ha hb (le_max_right _ _) (rawCountMoment_nonneg _ _ _)))
  intro z hz
  have hh := E.thin_field_bound y z ha hr hra hb hba hsep hz
    (by simpa [E,CoreObservationEnsemble.initial_mass] using hm) hZ hlam
  rw [CoreObservationEnsemble.initial_excess,CoreObservationEnsemble.initial_countMoment] at hh
  exact hh.trans (thin_majorants_le_uniform ha hb (le_max_right _ _) (rawCountMoment_nonneg _ _ _)).2

end CoulombAtom

end

end OAI
