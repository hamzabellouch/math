import Mathlib
import OAI.Analysis.CoulombIonization.Variational.PatchCenterIntegrable
import OAI.Analysis.CoulombIonization.Variational.FullPotentialComparison
import OAI.Analysis.CoulombIonization.FieldAnalysis.FreshFieldTower

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory Filter Set Metric
open scoped BigOperators ENNReal ContDiff

namespace CoulombAnalysis

lemma center_raw_error_of_loss {m a p f r d l : ℝ}
    (hm : 0 ≤ m) (hd : 0 ≤ d) (hl : 0 ≤ r-f) (hb : r-f ≤ l) :
    |(a-(r+d))*m-m*(a-p)| ≤ m*|f-p|+l*m+d*m := by
  have he : (a-(r+d))*m-m*(a-p) = -(m*(f-p))-(r-f)*m-d*m := by ring
  rw [he]
  apply (abs_sub _ _).trans
  apply (add_le_add (abs_sub _ _) le_rfl).trans
  rw [abs_neg,abs_mul,abs_of_nonneg hm,abs_of_nonneg (mul_nonneg hl hm),
    abs_of_nonneg (mul_nonneg hd hm)]
  exact add_le_add (add_le_add le_rfl (mul_le_mul_of_nonneg_right hb hm)) le_rfl

end CoulombAnalysis
namespace CoulombAtom
open CoulombAnalysis CoulombNeumann

lemma radial_branch_center_raw_bound {N : ℕ} (y : Space) {t b : ℝ} (hb : 0 < b)
    (htb : 7*b < t) (c : Fin N → Fin 2) (s : Spins (cutOutNumber c))
    {ψ : FormVector (cutCoreNumber c+cutOutNumber c)} (hψ : SobolevVector ψ) (Z lam : ℝ)
    (hc : Integrable (weightedPatchCenter ψ s Z lam y (t-4*b)))
    (hi : Integrable (weightedPatchTestAbs ψ s Z lam y (t-4*b) hb
      (radialPatchRetention N y t b c s) (fun x => 1/‖x‖))) :
    |(∫ u, (normalizedCoreField Z lam (coreSlice ψ s u) y-rawPotential y u)*
        formMass (coreSlice ψ s u))-(∫ u, weightedPatchCenter ψ s Z lam y (t-4*b) u)| ≤
      (∫ u, weightedPatchTestAbs ψ s Z lam y (t-4*b) hb
        (radialPatchRetention N y t b c s) (fun x => 1/‖x‖) u)+
      (∫ u, rawLocalPotential y (Real.sqrt 3*b) u*formMass (coreSlice ψ s u))+
      (∫ u, outerDeletedPotential y t b u*formMass (coreSlice ψ s u)) := by
  have hf : Integrable (fun u => (normalizedCoreField Z lam (coreSlice ψ s u) y-rawPotential y u)*
      formMass (coreSlice ψ s u)) := by
    convert (normalizedCoreField_weighted_integrable hψ s Z lam y).sub
      (rawPotential_coreSlice_integrable hψ s y) using 1
    funext u
    exact sub_mul _ _ _
  have hl := rawLocalPotential_core_integrable hψ s y (Real.sqrt 3*b)
  have hd := weighted_outerDeletedPotential_integrable hψ s y htb
  have he : ∀ᵐ u, |(normalizedCoreField Z lam (coreSlice ψ s u) y-rawPotential y u)*
      formMass (coreSlice ψ s u)-weightedPatchCenter ψ s Z lam y (t-4*b) u| ≤
      weightedPatchTestAbs ψ s Z lam y (t-4*b) hb
        (radialPatchRetention N y t b c s) (fun x => 1/‖x‖) u+
      rawLocalPotential y (Real.sqrt 3*b) u*formMass (coreSlice ψ s u)+
      outerDeletedPotential y t b u*formMass (coreSlice ψ s u) := by
    filter_upwards [radial_fine_potential_loss_ae y (t := t) hb c s] with u hu
    simp only [weightedPatchCenter,conditionalPatchCenter,weightedPatchTestAbs,
      ←tfBallPotential_sub_at_zero,rawPotential_retained_deleted y t b u]
    exact center_raw_error_of_loss (formMass_nonneg _) (outerDeletedPotential_nonneg y t b u) hu.1 hu.2
  rw [←integral_sub hf hc]
  apply (abs_integral_le_integral_abs).trans
  have hh := integral_mono_ae (hf.sub hc).abs ((hi.add hl).add hd) he
  simp only [Pi.sub_apply,Pi.add_apply] at hh
  have hi1 := integral_add (hi.add hl) hd
  have hi2 := integral_add hi hl
  simp only [Pi.add_apply] at hi1 hi2
  rw [hi1,hi2] at hh
  exact hh

theorem radial_center_raw_comparison {N : ℕ} {ψ : FormVector N}
    (hψ : SobolevFermion ψ) (y : Space) {t b : ℝ} (ht : 0 ≤ t) (hb : 0 < b)
    (htb : 7*b < t) (hy : t ≤ ‖y‖) {Z lam : ℝ} (hZ : 0 ≤ Z) (hlam : 0 < lam)
    {g : Space → ℝ} (hg : ContDiff ℝ ∞ g) (hcg : HasCompactSupport g)
    (hgn : ∫ z : Space, (g z)^2 = 1) (hrad : IsRadial g) (hgs : tsupport g ⊆ ball 0 1)
    {q : ℝ} (hq : 0 < q) (hqR : q ≤ 3*(t-4*b)/4) :
    let p := coreFirstRadialCut y ht hb
    let hp := coreFirstRadialCut_partition y ht hb
    let χ := fun c : Fin N → Fin 2 => orderedCutForm p hp ψ c
    |(Z/‖y‖-lam)*formMass ψ-(∫ x, rawPotential y x ∂formRawLaw ψ)-
      (∑ c : Fin N → Fin 2, ∑ s : Spins (cutOutNumber c), ∫ u,
        weightedPatchCenter (χ c) s Z lam y (t-4*b) u)| ≤
      (∑ c : Fin N → Fin 2, ∑ s : Spins (cutOutNumber c), ∫ u,
        weightedPatchTestAbs (χ c) s Z lam y (t-4*b) hb
          (radialPatchRetention N y t b c s) (fun x => 1/‖x‖) u)+
      (∫ x, rawLocalPotential y (Real.sqrt 3*b) x ∂formRawLaw ψ)+
      Real.sqrt (formMass ψ)*Real.sqrt
        (∑ c : Fin N → Fin 2, ∑ s : Spins (cutOutNumber c), ∫ u,
          (outerDeletedCount y t b u)^2*formMass (coreSlice (χ c) s u))/(t-7*b) := by
  dsimp only
  let p := coreFirstRadialCut y ht hb
  let hp := coreFirstRadialCut_partition y ht hb
  let χ := fun c : Fin N → Fin 2 => orderedCutForm p hp ψ c
  have hR : 0 < t-4*b := by linarith
  have hχ (c : Fin N → Fin 2) : SobolevVector (χ c) := orderedCutForm_sobolev p hp hψ.sobolevVector c
  have hc (c : Fin N → Fin 2) (s : Spins (cutOutNumber c))
      (u : Configuration (cutOutNumber c)) (v : Configuration (cutCoreNumber c)) (i : Fin (cutCoreNumber c))
      (hi : v i ∉ radialPatchCore y t) : FormZeroAt (coreSlice (χ c) s u) v := by
    apply FormZeroAt.coreSlice
    exact orderedCutForm_core_hole _ _ ψ c (radialPatchCore y t)ᶜ
      (coreFirstRadialCut_core_zero y ht hb) (coreFirstRadialCut_core_deriv_zero y ht hb)
      (joinLists v u) i (by simpa only [joinLists_left,mem_compl_iff] using hi)
  have hbranch (c : Fin N → Fin 2) (s : Spins (cutOutNumber c)) :=
    radial_branch_center_raw_bound y hb htb c s (hχ c) Z lam
      (weightedPatchCenter_integrable (hχ c) s y hR Z lam hb (radialPatchCore y t) (hc c s)
        (radialPatch_nuclear_distance hb hy) (radialPatch_core_distance y hb))
      (weightedPatchFull_integrable_and_bound (hχ c) s (radialPatchCore y t) (hc c s) y
        hR hb hb (radialPatch_nuclear_distance hb hy) (radialPatch_core_distance y hb) hq hqR hb _
        (radialPatchRetention_measurable N y t b c s) Z lam
        (radial_weightedPatchGap_integrable hψ y ht hb htb hy hZ hlam hg hcg hgn hrad hgs c s)).1
  rw [←fresh_cut_field_tower p hp hψ.sobolevVector Z lam y,←Finset.sum_sub_distrib]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  have hh := Finset.sum_le_sum (s := Finset.univ) (fun c _ =>
    (Finset.abs_sum_le_sum_abs (fun s : Spins (cutOutNumber c) =>
      (∫ u, (normalizedCoreField Z lam (coreSlice (χ c) s u) y-rawPotential y u)*formMass (coreSlice (χ c) s u))-
      (∫ u, weightedPatchCenter (χ c) s Z lam y (t-4*b) u)) Finset.univ).trans
      (Finset.sum_le_sum (s := Finset.univ) (fun s _ => hbranch c s)))
  simp only [Finset.sum_sub_distrib,Finset.sum_add_distrib] at hh
  apply hh.trans
  exact add_le_add
    (add_le_add le_rfl (fresh_cut_raw_local_control p hp hψ.sobolevVector y (Real.sqrt 3*b)))
    (fresh_cut_deleted_potential_bound p hp hψ.sobolevVector y htb)

theorem radial_center_field_quantitative {N : ℕ} {ψ : FormVector N}
    (hψ : SobolevFermion ψ) (y : Space) {t b : ℝ} (ht : 0 ≤ t) (hb : 0 < b)
    (htb : 7*b < t) (hy : t ≤ ‖y‖) {Z lam : ℝ} (hZ : 0 ≤ Z) (hlam : 0 < lam)
    {g : Space → ℝ} (hg : ContDiff ℝ ∞ g) (hcg : HasCompactSupport g)
    (hgn : ∫ z : Space, (g z)^2 = 1) (hrad : IsRadial g) (hgs : tsupport g ⊆ ball 0 1)
    {q : ℝ} (hq : 0 < q) (hqR : q ≤ 3*(t-4*b)/4) :
    let p := coreFirstRadialCut y ht hb
    let hp := coreFirstRadialCut_partition y ht hb
    let χ := fun c : Fin N → Fin 2 => orderedCutForm p hp ψ c
    |(Z/‖y‖-lam)*formMass ψ-(∫ x, rawPotential y x ∂formRawLaw ψ)-
      (∑ c : Fin N → Fin 2, ∑ s : Spins (cutOutNumber c), ∫ u,
        weightedPatchCenter (χ c) s Z lam y (t-4*b) u)| ≤
      Real.sqrt (formMass ψ)*Real.sqrt ((2/q)*
        (∑ c : Fin N → Fin 2, ∑ s : Spins (cutOutNumber c), ∫ u,
          weightedPatchGap (χ c) s Z lam y (t-4*b) hb (radialPatchRetention N y t b c s) u))+
      (∫ x, rawLocalPotential y (q+Real.sqrt 3*b) x ∂formRawLaw ψ)+
      (2*Real.pi*tfPatchDensityCapConstant*q^2/(t-4*b)^6)*formMass ψ+
      (∫ x, rawLocalPotential y (Real.sqrt 3*b) x ∂formRawLaw ψ)+
      Real.sqrt (formMass ψ)*Real.sqrt
        (∑ c : Fin N → Fin 2, ∑ s : Spins (cutOutNumber c), ∫ u,
          (outerDeletedCount y t b u)^2*formMass (coreSlice (χ c) s u))/(t-7*b) := by
  apply (radial_center_raw_comparison hψ y ht hb htb hy hZ hlam hg hcg hgn hrad hgs hq hqR).trans
  exact add_le_add (add_le_add
    (radial_full_potential_comparison hψ y ht hb htb hy hZ hlam hg hcg hgn hrad hgs hq hqR)
    le_rfl) le_rfl

end CoulombAtom

end

end OAI
