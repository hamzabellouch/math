import Mathlib
import OAI.Analysis.CoulombIonization.FieldAnalysis.RetainedPatchDensity
import OAI.Analysis.CoulombIonization.Localization.FormRawLaw

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory Set Filter Metric
open scoped BigOperators

namespace CoulombNeumann
open CoulombAtom CoulombAnalysis

lemma retainedSmear_mono {N : ℕ} {b : ℝ} (hb : 0 < b)
    {S T : Finset (Fin N)} (hST : S ⊆ T) (x : Configuration N) (z : Space) :
    retainedSmear b S x z ≤ retainedSmear b T x z := by
  apply Finset.sum_le_sum_of_subset_of_nonneg hST
  intro i _ _
  exact varthetaScaled_nonneg hb _

lemma rawBallCount_le_retainedPatch_mass {N : ℕ} {b a r R : ℝ} (hb : 0 < b)
    (hr : a+Real.sqrt 3*b ≤ r) (hR : r ≤ R)
    (S : Finset (Fin N)) (x : Configuration N) (y : Space)
    (hS : ∀ i, ‖x i-y‖ < a → i ∈ S) :
    rawBallCount y a x ≤ ∫ z in ball 0 r, retainedPatchLp hb S x y R z ∂ballMeasure R := by
  classical
  let T : Finset (Fin N) := Finset.univ.filter (fun i => ‖x i-y‖ < a)
  have hT : T ⊆ S := fun i hi => hS i (Finset.mem_filter.mp hi).2
  have hm : ∀ i ∈ T, ‖x i-y‖+Real.sqrt 3*b ≤ r := by
    intro i hi
    have hi0 := (Finset.mem_filter.mp hi).2
    linarith
  have he : rawBallCount y a x = (T.card:ℝ) := by
    exact Finset.sum_boole _ _
  rw [he]
  have hi : Integrable (fun z => retainedSmear b T x (y+z)) (ballMeasure r) :=
    (retainedPatch_memLp hb T x y r).integrable (Fact.out : (1:ENNReal) ≤ 5/3)
  have hj : Integrable (fun z => retainedSmear b S x (y+z)) (ballMeasure r) :=
    (retainedPatch_memLp hb S x y r).integrable (Fact.out : (1:ENNReal) ≤ 5/3)
  have hmass : (∫ z, retainedSmear b T x (y+z) ∂ballMeasure r) = (T.card:ℝ) :=
    (integral_congr_ae (retainedPatchLp_ae hb T x y r)).symm.trans
      (retainedPatchLp_mass hb T x y hm)
  rw [integral_congr_ae (ae_restrict_of_ae (retainedPatchLp_ae hb S x y R))]
  change _ ≤ ∫ z, retainedSmear b S x (y+z) ∂((volume.restrict (ball 0 R)).restrict (ball 0 r))
  rw [Measure.restrict_restrict_of_subset (ball_subset_ball hR)]
  change _ ≤ ∫ z, retainedSmear b S x (y+z) ∂ballMeasure r
  rw [←hmass]
  exact integral_mono hi hj (fun z => retainedSmear_mono hb hT x (y+z))

end CoulombNeumann

end

end OAI
