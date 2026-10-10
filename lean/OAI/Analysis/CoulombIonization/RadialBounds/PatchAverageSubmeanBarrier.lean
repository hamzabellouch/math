import Mathlib
import OAI.Analysis.CoulombIonization.Variational.SelectedPatchBudget
import OAI.Analysis.CoulombIonization.FieldAnalysis.PatchMassSubmeanBarrier

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory Set Metric Filter
open scoped BigOperators

namespace CoulombAtom

lemma patchMass_average_le_submean {N M : ℕ} {ψ : FormVector (N+M)}
    (hψ : SobolevVector ψ) (y : Space) {a R Z lam : ℝ}
    (ha : 0 < a) (hR : 0 < R) (hsep : R+2*a ≤ ‖y‖) (hZ : 0 ≤ Z) (hlam : 0 ≤ lam)
    (hi : ∀ s : Spins M, Integrable (weightedPatchMass ψ s Z lam y R)) :
    (∑ s : Spins M, ∫ u, weightedPatchMass ψ s Z lam y R u) ≤
      (4*R*Real.sqrt (1/(a^3*(Real.pi*4/3))))*
      (Real.sqrt (∫ z in closedBall y (R+a), coreLawAverage ψ (coreFieldSquare Z lam z))*
        Real.sqrt (formMass ψ)) := by
  let F (s : Spins M) (u : Configuration M) := ∫ z in closedBall y (R+a), coreFieldSquare Z lam z (coreSlice ψ s u)
  let W (s : Spins M) (u : Configuration M) := formMass (coreSlice ψ s u)
  let K := 4*R*Real.sqrt (1/(a^3*(Real.pi*4/3)))
  have hF (s : Spins M) : Integrable (F s) := coreFieldSquare_ball_statistic_integrable hψ s y ha (by linarith) hZ hlam
  have hW (s : Spins M) : Integrable (W s) := hψ.coreSlice_mass_integrable s
  have hFn (s : Spins M) (u : Configuration M) : 0 ≤ F s u := integral_nonneg (fun _ => coreFieldSquare_nonneg _ _ _ _)
  have hWn (s : Spins M) (u : Configuration M) : 0 ≤ W s u := formMass_nonneg _
  have hh (s : Spins M) : (∫ u, weightedPatchMass ψ s Z lam y R u) ≤
      K*∫ u, Real.sqrt (F s u)*Real.sqrt (W s u) := by
    rw [←integral_const_mul]
    apply integral_mono_ae (hi s) ((integrable_sqrt_mul_sqrt (hF s) (hW s) (hFn s) (hWn s)).const_mul K)
    filter_upwards [hψ.ae_coreSlice s] with u hu
    exact weightedPatchMass_le_submean ψ s u hu y ha hR hsep hZ hlam
  have hs := Finset.sum_le_sum (s := Finset.univ) (fun s _ => hh s)
  rw [←Finset.mul_sum] at hs
  have hc := sum_integral_sqrt_mul_sqrt_le (fun _ : Spins M => volume) F W hF hW hFn hWn
  have hend := hs.trans (mul_le_mul_of_nonneg_left hc (by dsimp [K]; positivity))
  have heF : (∑ s : Spins M, ∫ u, F s u) =
      ∫ z in closedBall y (R+a), coreLawAverage ψ (coreFieldSquare Z lam z) :=
    coreFieldSquare_ball_fubini hψ y ha (by linarith) hZ hlam
  have heW : (∑ s : Spins M, ∫ u, W s u) = formMass ψ := hψ.integral_coreSlice_mass
  rwa [heF,heW] at hend

lemma freshPatchMass_le_field_integral {N : ℕ} {ψ : FormVector N}
    (hψ : SobolevFermion ψ) (hm : formMass ψ = 1) (y : Space) {a r b Z lam : ℝ}
    (ha : 0 < a) (hr : 0 ≤ r) (hb : 0 < b) (hrb : 4*b < r)
    (hsep : r-4*b+2*a ≤ ‖y‖) (hy : r ≤ ‖y‖) (hZ : 0 ≤ Z) (hlam : 0 ≤ lam) :
    freshPatchMass (coreFirstRadialCut y hr hb) (coreFirstRadialCut_partition y hr hb) ψ Z lam y (r-4*b) ≤
      (4*(r-4*b)*Real.sqrt (1/(a^3*(Real.pi*4/3))))*
      Real.sqrt (∫ z in closedBall y (r-4*b+a),
        ((CoreObservationEnsemble.initial ψ hψ).observe (coreFirstRadialCut y hr hb)
          (coreFirstRadialCut_partition y hr hb)).fieldMoment Z lam z) := by
  let p := coreFirstRadialCut y hr hb
  let hp := coreFirstRadialCut_partition y hr hb
  let K := 4*(r-4*b)*Real.sqrt (1/(a^3*(Real.pi*4/3)))
  let F (c : Fin N → Fin 2) := ∫ z in closedBall y (r-4*b+a),
    coreLawAverage (orderedCutForm p hp ψ c) (coreFieldSquare Z lam z)
  let W (c : Fin N → Fin 2) := formMass (orderedCutForm p hp ψ c)
  have hFn (c) : 0 ≤ F c := integral_nonneg (fun _ =>
    Finset.sum_nonneg (fun _ _ => integral_nonneg (fun _ => coreFieldSquare_nonneg _ _ _ _)))
  have hWn (c) : 0 ≤ W c := formMass_nonneg _
  have hh := Finset.sum_le_sum (s := Finset.univ) (fun c (_ : c ∈ Finset.univ) =>
    patchMass_average_le_submean (orderedCutForm_sobolev p hp hψ.sobolevVector c) y ha
      (sub_pos.mpr hrb) hsep hZ hlam
      (fun s => radial_weightedPatchMass_integrable hψ.sobolevVector y hr hb hrb hy Z lam c s))
  change freshPatchMass p hp ψ Z lam y (r-4*b) ≤
    ∑ c, K*(Real.sqrt (F c)*Real.sqrt (W c)) at hh
  rw [←Finset.mul_sum] at hh
  have hc := Real.sum_sqrt_mul_sqrt_le Finset.univ hFn hWn
  have hend := hh.trans (mul_le_mul_of_nonneg_left hc (by dsimp [K]; positivity))
  have heW : (∑ c, W c) = 1 := (orderedCutForm_mass_sum p hp hψ.sobolevVector).trans hm
  have heF : (∑ c, F c) = ∫ z in closedBall y (r-4*b+a),
      ((CoreObservationEnsemble.initial ψ hψ).observe p hp).fieldMoment Z lam z := by
    simp_rw [CoreObservationEnsemble.initial_observe_fieldMoment ψ hψ p hp hZ hlam]
    rw [integral_finsetSum]
    intro c _
    exact coreLawAverage_fieldSquare_ball_integrable (orderedCutForm_sobolev p hp hψ.sobolevVector c)
      y ha (by linarith) hZ hlam
  rw [heW,Real.sqrt_one,mul_one,heF] at hend
  exact hend

theorem freshPatchMass_le_ballField {N : ℕ} {ψ : FormVector N}
    (hψ : SobolevFermion ψ) (hm : formMass ψ = 1) (y : Space) {a r b Z lam Q : ℝ}
    (ha : 0 < a) (hr : 0 ≤ r) (hra : r ≤ 6*a) (hb : 0 < b) (hrb : 4*b < r)
    (hsep : 10*a ≤ ‖y‖) (hZ : 0 ≤ Z) (hlam : 0 ≤ lam) (_hQn : 0 ≤ Q)
    (hQ : ∀ z ∈ closedBall y (8*a),
      ((CoreObservationEnsemble.initial ψ hψ).observe (coreFirstRadialCut y hr hb)
          (coreFirstRadialCut_partition y hr hb)).fieldMoment Z lam z ≤ Q) :
    freshPatchMass (coreFirstRadialCut y hr hb) (coreFirstRadialCut_partition y hr hb) ψ Z lam y (r-4*b) ≤
      768*a*Real.sqrt Q := by
  let E := (CoreObservationEnsemble.initial ψ hψ).observe (coreFirstRadialCut y hr hb)
    (coreFirstRadialCut_partition y hr hb)
  let R := r-4*b
  let K := 4*R*Real.sqrt (1/(a^3*(Real.pi*4/3)))
  let V := (8*a)^3*(Real.pi*4/3)
  have hR : 0 < R := by dsimp [R]; linarith
  have hRa : R ≤ 6*a := by dsimp [R]; linarith
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hV : 0 ≤ V := by dsimp [V]; positivity
  have hh := freshPatchMass_le_field_integral hψ hm y ha hr hb hrb
    (by linarith : r-4*b+2*a ≤ ‖y‖) (by linarith) hZ hlam
  have hi8 := E.fieldMoment_ball_integrable y ha (by linarith : 8*a+a ≤ ‖y‖) hZ hlam
  have hsub : closedBall y (R+a) ⊆ closedBall y (8*a) := closedBall_subset_closedBall (by linarith)
  have hinc := setIntegral_mono_set hi8 (ae_of_all _ (fun z => E.fieldMoment_nonneg Z lam z))
    (ae_of_all _ hsub)
  have hc : IntegrableOn (fun _ : Space => Q) (closedBall y (8*a)) :=
    integrableOn_const (isCompact_closedBall y (8*a)).measure_lt_top.ne
  have hbnd := hinc.trans (setIntegral_mono_on hi8 hc isClosed_closedBall.measurableSet hQ)
  rw [integral_const,Measure.real,Measure.restrict_apply_univ,smul_eq_mul,
    ←Measure.real,space_closedBall_real y (by positivity)] at hbnd
  have ht := hh.trans (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hbnd) hK)
  have hv : (1/(a^3*(Real.pi*4/3)))*V = 512 := by
    dsimp [V]
    field_simp [ha.ne',Real.pi_ne_zero]
    ring
  have he : K*Real.sqrt (V*Q) = 4*R*Real.sqrt 512*Real.sqrt Q := by
    dsimp [K]
    rw [Real.sqrt_mul hV]
    calc
      _ = 4*R*(Real.sqrt (1/(a^3*(Real.pi*4/3)))*Real.sqrt V)*Real.sqrt Q := by ring
      _ = _ := by rw [←Real.sqrt_mul (by positivity : 0 ≤ 1/(a^3*(Real.pi*4/3))),hv]
  change _ ≤ K*Real.sqrt (V*Q) at ht
  rw [he] at ht
  have hroot : Real.sqrt (512:ℝ) ≤ 32 := by nlinarith [Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 512)]
  have hcoef := mul_le_mul (by linarith : 4*R ≤ 24*a) hroot (Real.sqrt_nonneg 512) (by positivity : 0 ≤ 24*a)
  have hc' : 4*R*Real.sqrt 512 ≤ 768*a := by nlinarith
  exact ht.trans (mul_le_mul_of_nonneg_right hc' (Real.sqrt_nonneg Q))

end CoulombAtom

end

end OAI
