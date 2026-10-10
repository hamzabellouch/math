import Mathlib
import OAI.Analysis.CoulombIonization.Variational.ExpectedFullPotential
import OAI.Analysis.CoulombIonization.Variational.IntegrableCutTower

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory Filter Set Metric
open scoped BigOperators ENNReal ContDiff

namespace CoulombAtom
open CoulombAnalysis CoulombNeumann

lemma retainedPatchLocalPotential_raw_le_ae {M : ℕ} (y : Space) {R q : ℝ}
    (hqR : q ≤ R) {b : ℝ} (hb : 0 < b)
    (S : Configuration M → Finset (Fin M)) :
    ∀ᵐ u, (∫ z in ball 0 q, ‖retainedPatchLp hb (S u) u y R z‖/‖z‖) ≤
      rawLocalPotential y (q+Real.sqrt 3*b) u := by
  classical
  have he : ∀ᵐ u : Configuration M, ∀ i, u i ≠ y := by
    exact (ae_all_iff.mpr fun i => Measure.ae_eval_ne (fun _ : Fin M => (volume : Measure Space)) i y)
  filter_upwards [he] with u hu
  apply (retainedPatchLp_local_potential_le hb hqR (S u) u y (fun i _ => hu i)).trans
  have heq (i : Fin M) : (ball y (q+Real.sqrt 3*b)).indicator (fun z => 1/‖y-z‖) (u i) =
      if ‖u i-y‖ < q+Real.sqrt 3*b then 1/‖u i-y‖ else 0 := by
    simp only [indicator_apply,mem_ball,dist_eq_norm,norm_sub_rev]
  simp_rw [heq]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun i _ _ => by
    split_ifs <;> positivity)

lemma weightedPatchLocalPotential_raw_integral_le {N M : ℕ} {ψ : FormVector (N+M)}
    (hψ : SobolevVector ψ) (s : Spins M) (y : Space) {R q : ℝ}
    (hq : 0 < q) (hqR : q ≤ R) {b : ℝ} (hb : 0 < b)
    (S : Configuration M → Finset (Fin M)) (hS : ∀ i, MeasurableSet {u | i ∈ S u}) :
    (∫ u, weightedPatchLocalPotential ψ s y R q hb S u) ≤
      ∫ u, rawLocalPotential y (q+Real.sqrt 3*b) u*formMass (coreSlice ψ s u) := by
  apply integral_mono_ae (weightedPatchLocalPotential_integrable hψ s y hq hqR hb S hS)
    (rawLocalPotential_core_integrable hψ s y _)
  filter_upwards [retainedPatchLocalPotential_raw_le_ae y hqR hb S] with u hu
  simpa only [weightedPatchLocalPotential,mul_comm (formMass (coreSlice ψ s u))] using
    mul_le_mul_of_nonneg_left hu (formMass_nonneg (coreSlice ψ s u))

theorem radial_full_potential_comparison {N : ℕ} {ψ : FormVector N}
    (hψ : SobolevFermion ψ) (y : Space) {t b : ℝ} (ht : 0 ≤ t) (hb : 0 < b)
    (htb : 7*b < t) (hy : t ≤ ‖y‖) {Z lam : ℝ} (hZ : 0 ≤ Z) (hlam : 0 < lam)
    {g : Space → ℝ} (hg : ContDiff ℝ ∞ g) (hcg : HasCompactSupport g)
    (hgn : ∫ z : Space, (g z)^2 = 1) (hrad : IsRadial g) (hgs : tsupport g ⊆ ball 0 1)
    {q : ℝ} (hq : 0 < q) (hqR : q ≤ 3*(t-4*b)/4) :
    let p := coreFirstRadialCut y ht hb
    let hp := coreFirstRadialCut_partition y ht hb
    let χ := fun c : Fin N → Fin 2 => orderedCutForm p hp ψ c
    (∑ c : Fin N → Fin 2, ∑ s : Spins (cutOutNumber c), ∫ u,
      weightedPatchTestAbs (χ c) s Z lam y (t-4*b) hb
        (radialPatchRetention N y t b c s) (fun x => 1/‖x‖) u) ≤
      Real.sqrt (formMass ψ)*Real.sqrt ((2/q)*
        (∑ c : Fin N → Fin 2, ∑ s : Spins (cutOutNumber c), ∫ u,
          weightedPatchGap (χ c) s Z lam y (t-4*b) hb (radialPatchRetention N y t b c s) u))+
      (∫ x, rawLocalPotential y (q+Real.sqrt 3*b) x ∂formRawLaw ψ)+
      (2*Real.pi*tfPatchDensityCapConstant*q^2/(t-4*b)^6)*formMass ψ := by
  dsimp only
  have hqR' : q ≤ t-4*b := by linarith
  apply (radial_full_absolute_control hψ y ht hb htb hy hZ hlam hg hcg hgn hrad hgs hq hqR).trans
  apply add_le_add _ le_rfl
  apply add_le_add le_rfl
  apply le_trans (Finset.sum_le_sum (s := Finset.univ) (fun c _ =>
    Finset.sum_le_sum (s := Finset.univ) (fun s _ =>
      weightedPatchLocalPotential_raw_integral_le
        (orderedCutForm_sobolev _ _ hψ.sobolevVector c) s y hq hqR' hb _
        (radialPatchRetention_measurable N y t b c s))))
  exact fresh_cut_raw_local_control _ _ hψ.sobolevVector y _

end CoulombAtom

end

end OAI
