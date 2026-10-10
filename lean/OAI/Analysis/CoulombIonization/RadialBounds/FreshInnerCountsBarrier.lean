import Mathlib
import OAI.Analysis.CoulombIonization.FieldAnalysis.PuncturedGreenBarrier
import OAI.Analysis.CoulombIonization.RadialBounds.LocalCountGapBarrier
import OAI.Analysis.CoulombIonization.FieldAnalysis.RetainedInnerMassBarrier

namespace OAI

noncomputable section

namespace CoulombAtom

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory Set Filter Metric
open scoped BigOperators

lemma radialCut_inner_labels {L : ℕ} (y : Space) {t b : ℝ}
    (ht : 0 ≤ t) (hb : 0 < b) (c : Fin L → Fin 2) (x : Configuration L)
    (hx : (spatialProduct (coreFirstRadialCut y ht hb)
      (coreFirstRadialCut_partition y ht hb) c).value x ≠ 0)
    (i : Fin L) (hi : ‖x i-y‖ < t) : c i ≠ 0 := by
  classical
  intro hc
  change (∏ j, (coreFirstRadialCut y ht hb (c j)).value (x j)) ≠ 0 at hx
  apply ((Finset.prod_ne_zero_iff.mp hx) i (Finset.mem_univ i))
  rw [hc]
  exact coreFirstRadialCut_core_zero y ht hb (x i) (by
    simpa only [radialPatchCore,mem_compl_iff,mem_ofPred_eq,not_le] using hi)

lemma radialCut_inner_count {L : ℕ} (y : Space) {a t b : ℝ}
    (ht : 0 ≤ t) (hb : 0 < b) (hat : a ≤ t) (c : Fin L → Fin 2) (x : Configuration L)
    (hx : (spatialProduct (coreFirstRadialCut y ht hb)
      (coreFirstRadialCut_partition y ht hb) c).value x ≠ 0) :
    rawBallCount y a (cutOutPositions c x) = rawBallCount y a x := by
  classical
  rw [rawBallCount,sum_cutOutPositions c x (fun z => if ‖z-y‖ < a then 1 else 0)]
  apply Finset.sum_congr rfl
  intro i _
  by_cases hi : ‖x i-y‖ < a
  · rw [ite_eq_left (radialCut_inner_labels y ht hb c x hx i (hi.trans_le hat))]
  · simp only [hi,ite_false,ite_self]

theorem radial_fresh_inner_second_moment {L : ℕ} {ψ : FormVector L}
    (hψ : SobolevVector ψ) (y : Space) {a t b : ℝ}
    (ht : 0 ≤ t) (hb : 0 < b) (hat : a ≤ t) :
    let p := coreFirstRadialCut y ht hb
    let hp := coreFirstRadialCut_partition y ht hb
    (∑ c : Fin L → Fin 2, ∑ s : Spins (cutOutNumber c), ∫ u,
      rawBallCount y a u^2*formMass (coreSlice (orderedCutForm p hp ψ c) s u)) =
      ∫ x, rawBallCount y a x^2 ∂formRawLaw ψ := by
  dsimp only
  rw [←spatialCutExpectation_raw (coreFirstRadialCut y ht hb)
    (coreFirstRadialCut_partition y ht hb) hψ ((rawBallCount_measurable y a).pow_const 2)
    (fun x => norm_sq_le_of_nonneg (rawBallCount_nonneg y a x) (rawBallCount_le y a x))]
  unfold spatialCutExpectation
  apply Finset.sum_congr rfl
  intro c _
  rw [cutOuter_expectation_eq_full (coreFirstRadialCut y ht hb)
    (coreFirstRadialCut_partition y ht hb) hψ c ((rawBallCount_measurable y a).pow_const 2)
    (fun u => norm_sq_le_of_nonneg (rawBallCount_nonneg y a u) (rawBallCount_le y a u))]
  apply Finset.sum_congr rfl
  intro s _
  apply integral_congr_ae (ae_of_all _ _)
  intro x
  by_cases hx : (spatialProduct (coreFirstRadialCut y ht hb)
      (coreFirstRadialCut_partition y ht hb) c).value x = 0
  · simp only [multiplyForm,hx,Complex.ofReal_zero,zero_mul,norm_zero,
      zero_pow (by decide : 2 ≠ 0),mul_zero]
  · rw [radialCut_inner_count y ht hb hat c x hx]

open MeasureTheory Set Filter Metric
open scoped BigOperators ContDiff

open CoulombAnalysis CoulombNeumann

def localPatchDensityCap (R : ℝ) : ℝ :=
  (tfPatchCapConstant/R^4/((5/3:ℝ)*tfKinetic))^(3/2:ℝ)

lemma localPatchDensityCap_nonneg (R : ℝ) : 0 ≤ localPatchDensityCap R := by
  unfold localPatchDensityCap
  apply Real.rpow_nonneg
  exact div_nonneg (div_nonneg tfPatchCapConstant_pos.le (by positivity))
    (mul_nonneg (by norm_num) tfKinetic_pos.le)

lemma radial_inner_count_sq_gap {L : ℕ} {ψ : FormVector L}
    (hψ : SobolevVector ψ) (y : Space) {a t b : ℝ}
    (_ha : 0 < a) (ht : 0 ≤ t) (hb : 0 < b) (hba : 3*b ≤ a)
    (hat : 8*a < t-4*b) (hy : t ≤ ‖y‖) (Z lam : ℝ)
    (c : Fin L → Fin 2) (s : Spins (cutOutNumber c)) :
    let p := coreFirstRadialCut y ht hb
    let hp := coreFirstRadialCut_partition y ht hb
    let χ := orderedCutForm p hp ψ c
    ∀ᵐ u, rawBallCount y a u^2*formMass (coreSlice χ s u) ≤
      2*(localPatchDensityCap (t-4*b)*((4*a)^3*(Real.pi*4/3)))^2*
        formMass (coreSlice χ s u)+
      512*a*weightedPatchGap χ s Z lam y (t-4*b) hb (radialPatchRetention L y t b c s) u := by
  dsimp only
  filter_upwards [radialPatchMinimizer_density_cap hψ y ht hb (by linarith) hy Z lam c s] with u hu
  let σ := retainedPatchLp hb (radialPatchRetention L y t b c s u) u y (t-4*b)
  let Φ := conditionalPatchField (orderedCutForm (coreFirstRadialCut y ht hb)
    (coreFirstRadialCut_partition y ht hb) ψ c) s Z lam y (t-4*b) u
  have hσ : NonnegDensity σ := retainedPatchLp_nonneg hb _ _ _ _
  have hm : rawBallCount y a u ≤ ∫ z in ball 0 (2*a), σ z ∂ballMeasure (t-4*b) := by
    have hsqrt : Real.sqrt 3 ≤ (3:ℝ) := by nlinarith [Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 3), Real.sqrt_nonneg (3:ℝ)]
    apply rawBallCount_le_retainedPatch_mass hb
      (le_trans (by nlinarith) (show a+3*b ≤ 2*a by linarith))
      (by linarith)
    intro i hi
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ i,by linarith⟩
  have hc : ∀ᵐ x ∂ballMeasure (t-4*b), ‖x‖ ≤ 2*(2*a) →
      tfPatchMinimizer (t-4*b) tfKinetic tfKinetic_pos Φ x ≤ localPatchDensityCap (t-4*b) := by
    filter_upwards [hu] with x hx
    intro hn
    exact hx (by linarith)
  have hh := local_mass_sq_le_gap (by linarith : 0 < 2*a) (by linarith : 4*(2*a) < t-4*b)
    tfKinetic tfKinetic_pos Φ hσ (localPatchDensityCap_nonneg _) hc
  have hs := (sq_le_sq₀ (rawBallCount_nonneg y a u)
    (integral_nonneg_of_ae (ae_restrict_of_ae hσ))).mpr hm
  have hh0 := mul_le_mul_of_nonneg_right (hs.trans hh)
    (formMass_nonneg (coreSlice (orderedCutForm (coreFirstRadialCut y ht hb)
      (coreFirstRadialCut_partition y ht hb) ψ c) s u))
  dsimp only [weightedPatchGap]
  convert hh0 using 1
  dsimp only [σ, Φ]
  ring

theorem radial_inner_second_moment_gap {L : ℕ} {ψ : FormVector L}
    (hψ : SobolevFermion ψ) (y : Space) {a t b : ℝ}
    (ha : 0 < a) (ht : 0 ≤ t) (hb : 0 < b) (hba : 3*b ≤ a)
    (hat : 8*a < t-4*b) (hy : t ≤ ‖y‖)
    {Z lam : ℝ} (hZ : 0 ≤ Z) (hlam : 0 < lam)
    {g : Space → ℝ} (hg : ContDiff ℝ ∞ g) (hcg : HasCompactSupport g)
    (hgn : ∫ z : Space, (g z)^2 = 1) (hr : IsRadial g) (hgs : tsupport g ⊆ ball 0 1) :
    let p := coreFirstRadialCut y ht hb
    let hp := coreFirstRadialCut_partition y ht hb
    (∫ x, rawBallCount y a x^2 ∂formRawLaw ψ) ≤
      2*(localPatchDensityCap (t-4*b)*((4*a)^3*(Real.pi*4/3)))^2*formMass ψ+
      512*a*(∑ c : Fin L → Fin 2, ∑ s : Spins (cutOutNumber c), ∫ u,
        weightedPatchGap (orderedCutForm p hp ψ c) s Z lam y (t-4*b) hb
          (radialPatchRetention L y t b c s) u) := by
  let p := coreFirstRadialCut y ht hb
  let hp := coreFirstRadialCut_partition y ht hb
  let K := 2*(localPatchDensityCap (t-4*b)*((4*a)^3*(Real.pi*4/3)))^2
  let χ := fun c => orderedCutForm p hp ψ c
  have hχ (c : Fin L → Fin 2) := orderedCutForm_sobolev p hp hψ.sobolevVector c
  have hgap (c : Fin L → Fin 2) (s : Spins (cutOutNumber c)) :
      Integrable (weightedPatchGap (χ c) s Z lam y (t-4*b) hb (radialPatchRetention L y t b c s)) :=
    radial_weightedPatchGap_integrable hψ y ht hb (by linarith) hy hZ hlam hg hcg hgn hr hgs c s
  have hraw (c : Fin L → Fin 2) (s : Spins (cutOutNumber c)) :
      Integrable (fun u => rawBallCount y a u^2*formMass (coreSlice (χ c) s u)) := by
    apply (hχ c).coreSlice_mass_integrable s |>.bdd_mul
      (((rawBallCount_measurable y a).pow_const 2).aestronglyMeasurable)
    exact ae_of_all _ (fun u => norm_sq_le_of_nonneg (rawBallCount_nonneg y a u) (rawBallCount_le y a u))
  dsimp only
  rw [←radial_fresh_inner_second_moment hψ.sobolevVector y ht hb (by linarith : a ≤ t)]
  change (∑ c, ∑ s, ∫ u, rawBallCount y a u^2*formMass (coreSlice (χ c) s u)) ≤ K*formMass ψ+_
  calc
    _ ≤ ∑ c : Fin L → Fin 2, ∑ s : Spins (cutOutNumber c), ∫ u,
        (K*formMass (coreSlice (χ c) s u)+512*a*
          weightedPatchGap (χ c) s Z lam y (t-4*b) hb (radialPatchRetention L y t b c s) u) := by
      apply Finset.sum_le_sum; intro c _
      apply Finset.sum_le_sum; intro s _
      exact integral_mono_ae (hraw c s)
        (((hχ c).coreSlice_mass_integrable s).const_mul K |>.add ((hgap c s).const_mul (512*a)))
        (radial_inner_count_sq_gap hψ.sobolevVector y ha ht hb hba hat hy Z lam c s)
    _ = _ := by
      have he (c : Fin L → Fin 2) (s : Spins (cutOutNumber c)) :
          (∫ u, (K*formMass (coreSlice (χ c) s u)+512*a*
            weightedPatchGap (χ c) s Z lam y (t-4*b) hb (radialPatchRetention L y t b c s) u)) =
          K*(∫ u, formMass (coreSlice (χ c) s u))+512*a*(∫ u,
            weightedPatchGap (χ c) s Z lam y (t-4*b) hb (radialPatchRetention L y t b c s) u) := by
        rw [integral_add (((hχ c).coreSlice_mass_integrable s).const_mul K)
          ((hgap c s).const_mul (512*a)),integral_const_mul,integral_const_mul]
      simp_rw [he,Finset.sum_add_distrib,←Finset.mul_sum]
      simp_rw [show ∀ c, (∑ s, ∫ u, formMass (coreSlice (χ c) s u)) = formMass (χ c) from fun c => (hχ c).integral_coreSlice_mass]
      rw [orderedCutForm_mass_sum p hp hψ.sobolevVector]

end CoulombAtom

end

end OAI
