import Mathlib
import OAI.Analysis.CoulombIonization.FieldAnalysis.CoreSubmeanSquareBarrier

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory Filter Set Metric
open scoped BigOperators

namespace CoulombAtom
open CoulombAnalysis

lemma core_field_square_ball_integrable {N : ℕ} {ψ : FormVector N}
    (hψ : SobolevVector ψ) (y : Space) {A d : ℝ}
    (hd : 0 < d) (hsep : A+d ≤ ‖y‖) {Z lam : ℝ} (hZ : 0 ≤ Z) (hlam : 0 ≤ lam) :
    IntegrableOn (fun z => (max (normalizedCoreField Z lam ψ z) 0)^2) (closedBall y A) := by
  let w : Space → ℝ := (closedBall y A).indicator (fun _ => 1)
  have hwm : Measurable w := measurable_const.indicator isClosed_closedBall.measurableSet
  have hwn (z : Space) : 0 ≤ w z := by
    by_cases hz : z ∈ closedBall y A <;> simp [w,hz]
  have hwi : Integrable w := bounded_compact_integrable hwm (isCompact_closedBall y A)
    (by intro z hz; by_contra hz0; exact hz (by simp [w,hz0]))
    (B := 1) (fun z => by by_cases hz : z ∈ closedBall y A <;> simp [w,hz])
  have hwsep : ∀ z, w z ≠ 0 → d ≤ ‖z‖ := by
    intro z hz
    have hzd : ‖z-y‖ ≤ A := by
      by_contra hh
      have hn : z ∉ closedBall y A := by simpa only [mem_closedBall,dist_eq_norm] using hh
      exact hz (by simp [w,hn])
    have htri := norm_le_norm_sub_add y z
    rw [norm_sub_rev y z] at htri
    linarith
  have hi := positive_core_pair_integrable hψ hwi hwm hwn hZ hlam hd hwsep 2
  rw [←integrable_indicator_iff isClosed_closedBall.measurableSet]
  have heq : (closedBall y A).indicator (fun z => (max (normalizedCoreField Z lam ψ z) 0)^2) =
      (fun z => w z * (max (normalizedCoreField Z lam ψ z) 0)^2) := by
    funext z
    by_cases hz : z ∈ closedBall y A <;> simp [w,hz]
  rw [heq]
  simpa only [mul_comm] using hi

theorem conditional_out_maximum_sq_le_ball_average {N M : ℕ} (ψ : FormVector (N+M))
    (s : Spins M) (u : Configuration M) (hψ : SobolevVector (coreSlice ψ s u))
    (y : Space) {a R B Z lam : ℝ} (_ha : 0 ≤ a) (hR : 0 < R)
    (hsep : a+2*R ≤ ‖y‖) (hu : ∀ i, ‖u i-y‖ ≤ a)
    (hZ : 0 ≤ Z) (hlam : 0 ≤ lam) {η : Space → ℝ}
    (hm : Measurable η) (hn : ∀ z, 0 ≤ η z)
    (hs : ∀ z, η z ≠ 0 → ‖z‖ ≤ R) (hb : ∀ z, |η z| ≤ B)
    (hr : IsRadial η) (h1 : ∫ z, η z = 1) :
    conditionalOutMaximum Z lam ψ s u^2 ≤
      B*∫ z in closedBall y (a+R), (max (normalizedCoreField Z lam (coreSlice ψ s u) z) 0)^2 := by
  let F : Space → ℝ := fun z => (max (normalizedCoreField Z lam (coreSlice ψ s u) z) 0)^2
  have hB : 0 ≤ B := (abs_nonneg (η 0)).trans (hb 0)
  have hFi : IntegrableOn F (closedBall y (a+R)) :=
    core_field_square_ball_integrable hψ y hR (by linarith) hZ hlam
  have hQ : 0 ≤ B*∫ z in closedBall y (a+R), F z :=
    mul_nonneg hB (integral_nonneg (fun z => sq_nonneg _))
  have hF (i : Fin M) : F (u i) ≤ B*∫ z in closedBall y (a+R), F z := by
    have hnuc : 2*R ≤ ‖u i‖ := by
      have htri := norm_le_norm_sub_add y (u i)
      rw [norm_sub_rev y (u i)] at htri
      linarith [hu i]
    have hi := normalizedCoreField_radial_submean_sq hψ hm hR hn hs hb hr h1 (u i) hnuc hZ hlam
    apply hi.trans
    let k := translatedDensity η (u i)
    have hkm : Measurable k := translatedDensity_measurable hm _
    have hkn (z : Space) : 0 ≤ k z := hn (z-u i)
    have hki : Integrable k := bounded_compact_integrable hkm (isCompact_closedBall _ _)
      (translatedDensity_support hs _) (fun z => hb (z-u i))
    have hks : ∀ z, k z ≠ 0 → R ≤ ‖z‖ := by
      intro z hz
      have htri := norm_le_norm_sub_add (u i) z
      rw [norm_sub_rev (u i) z] at htri
      linarith [hs (z-u i) hz]
    have hleft := positive_core_pair_integrable hψ hki hkm hkn hZ hlam hR hks 2
    rw [←integral_const_mul,←integral_indicator isClosed_closedBall.measurableSet]
    apply integral_mono hleft ((integrable_indicator_iff isClosed_closedBall.measurableSet).2 (hFi.const_mul B))
    intro z
    by_cases hz : z ∈ closedBall y (a+R)
    · rw [indicator_of_mem hz]
      simpa only [k,translatedDensity,F,mul_comm] using
        mul_le_mul_of_nonneg_left ((le_abs_self _).trans (hb (z-u i)))
          (sq_nonneg (max (normalizedCoreField Z lam (coreSlice ψ s u) z) 0))
    · rw [indicator_of_notMem hz]
      have hk0 : η (z-u i) = 0 := by
        by_contra hk
        have hnz := norm_sub_le_norm_sub_add_norm_sub z (u i) y
        have hh := hs (z-u i) hk
        exact hz (by rw [mem_closedBall,dist_eq_norm]; linarith [hu i])
      simp only [k,translatedDensity,hk0,mul_zero,le_refl]
  have hh : conditionalOutMaximum Z lam ψ s u ≤
      Real.sqrt (B*∫ z in closedBall y (a+R), F z) := by
    apply conditionalOutMaximum_le _ _ _ _ _ (Real.sqrt_nonneg _)
    intro i
    apply (le_max_left _ _).trans
    apply (sq_le_sq₀ (le_max_right _ _) (Real.sqrt_nonneg _)).mp
    rw [Real.sq_sqrt hQ]
    exact hF i
  have hh2 := (sq_le_sq₀ (conditionalOutMaximum_nonneg _ _ _ _ _) (Real.sqrt_nonneg _)).mpr hh
  rwa [Real.sq_sqrt hQ] at hh2

end CoulombAtom

end

end OAI
