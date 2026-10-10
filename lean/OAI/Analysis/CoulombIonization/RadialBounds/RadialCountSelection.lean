import Mathlib
import OAI.Analysis.CoulombIonization.Fermionic.CutCountDomination

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory Set Filter
open scoped BigOperators

namespace CoulombAtom
open CoulombRadialAveraging

lemma cutOutNumber_le_total {N : ℕ} (c : Fin N → Fin 2) : cutOutNumber c ≤ N := by
  have h := cutNumbers_sum c
  omega

lemma rawStripCount_measurable {N : ℕ} (y : Space) (t b : ℝ) :
    Measurable (rawStripCount (N := N) y t b) :=
  slidingCount_measurable (fun i => configuration_distance_measurable y i)
    measurable_const (7*b) b

lemma rawStripCount_nonneg {N : ℕ} (y : Space) (t b : ℝ) (x : Configuration N) :
    0 ≤ rawStripCount y t b x := slidingCount_nonneg _ _ _ _

lemma rawStripCount_le {N : ℕ} (y : Space) (t b : ℝ) (x : Configuration N) :
    rawStripCount y t b x ≤ N := slidingCount_le _ _ _ _

lemma norm_sq_le_of_nonneg {x B : ℝ} (h : 0 ≤ x) (hB : x ≤ B) : ‖x^2‖ ≤ B^2 := by
  rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
  exact pow_le_pow_left₀ h hB 2

lemma radialCut_out_second_moment {N : ℕ} {ψ : FormVector N} (hψ : SobolevVector ψ)
    (y : Space) {t b R : ℝ} (ht : 0 ≤ t) (hb : 0 < b) (hR : t+b ≤ R) :
    (∑ c : Fin N → Fin 2, (cutOutNumber c:ℝ)^2*formMass
      (orderedCutForm (coreFirstRadialCut y ht hb)
        (coreFirstRadialCut_partition y ht hb) ψ c)) ≤
      ∫ x, rawBallCount y R x^2 ∂formRawLaw ψ := by
  rw [spatialCutExpectation_outMoment _ _ _ (fun n => (n:ℝ)^2)]
  apply spatialCutExpectation_le_raw _ _ hψ
    (fun _ => measurable_const) (A := (N:ℝ)^2)
    (fun c _ => norm_sq_le_of_nonneg (Nat.cast_nonneg _) (by exact_mod_cast cutOutNumber_le_total c))
    ((rawBallCount_measurable y R).pow_const 2) (B := (N:ℝ)^2)
    (fun x => norm_sq_le_of_nonneg (rawBallCount_nonneg _ _ _) (rawBallCount_le _ _ _))
  intro c x hx
  exact pow_le_pow_left₀ (Nat.cast_nonneg _) (radialCut_outNumber_le_rawBall y ht hb hR c x hx) 2

lemma radialCut_deleted_second_moment {N : ℕ} {ψ : FormVector N} (hψ : SobolevVector ψ)
    (y : Space) {t b : ℝ} (ht : 0 ≤ t) (hb : 0 < b) :
    spatialCutExpectation (coreFirstRadialCut y ht hb)
      (coreFirstRadialCut_partition y ht hb) ψ (fun c x => cutDeletedCount y t b c x^2) ≤
      ∫ x, rawStripCount y t b x^2 ∂formRawLaw ψ := by
  apply spatialCutExpectation_le_raw _ _ hψ
    (fun c => (cutDeletedCount_measurable y t b c).pow_const 2) (A := (N:ℝ)^2)
    (fun c x => norm_sq_le_of_nonneg (cutDeletedCount_nonneg _ _ _ _ _) (cutDeletedCount_le _ _ _ _ _))
    ((rawStripCount_measurable y t b).pow_const 2) (B := (N:ℝ)^2)
    (fun x => norm_sq_le_of_nonneg (rawStripCount_nonneg _ _ _ _) (rawStripCount_le _ _ _ _))
  intro c x hx
  exact pow_le_pow_left₀ (cutDeletedCount_nonneg _ _ _ _ _)
    (radialCut_deleted_le_rawStrip y ht hb c x hx) 2

theorem radial_cut_radius_selection {N : ℕ} {ψ : FormVector N} (hψ : SobolevVector ψ)
    (y : Space) {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (hba : b < a) :
    ∃ t ∈ Icc (5*a) (6*a), ∃ ht : 0 ≤ t,
      let p := coreFirstRadialCut y ht hb
      let hp := coreFirstRadialCut_partition y ht hb
      (∑ c : Fin N → Fin 2, (cutOutNumber c:ℝ)^2*formMass (orderedCutForm p hp ψ c)) ≤
        (∫ x, rawBallCount y (7*a) x^2 ∂formRawLaw ψ) ∧
      spatialCutExpectation p hp ψ (fun c x => cutDeletedCount y t b c x^2) ≤
        (8*b/a)*(∫ x, rawBallCount y (7*a) x^2 ∂formRawLaw ψ) := by
  obtain ⟨t,ht,hdel⟩ := radial_raw_radius_selection hψ y ha hb.le hba
  have ht0 : 0 ≤ t := by linarith [ht.1]
  refine ⟨t,ht,ht0,?_,?_⟩
  · exact radialCut_out_second_moment hψ y ht0 hb (by linarith [ht.2])
  · exact (radialCut_deleted_second_moment hψ y ht0 hb).trans hdel

end CoulombAtom

end

end OAI
