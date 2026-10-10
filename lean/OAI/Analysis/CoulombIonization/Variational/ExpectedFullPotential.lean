import Mathlib
import OAI.Analysis.CoulombIonization.ThomasFermi.PatchFullPotential
import OAI.Analysis.CoulombIonization.Localization.PatchLocalObservable

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory Filter Set Metric
open scoped BigOperators ENNReal ContDiff

namespace CoulombAtom
open CoulombAnalysis CoulombNeumann

lemma weightedPatchFull_le {N M : ℕ} {ψ : FormVector (N+M)}
    (hψ : SobolevVector ψ) (s : Spins M) (A : Set Space)
    (hcore : ∀ u x i, x i ∉ A → FormZeroAt (coreSlice ψ s u) x)
    (y : Space) {R d r q b : ℝ} (hR : 0 < R) (hd : 0 < d) (hr : 0 < r)
    (hnuc : ∀ z ∈ closedBall y R, r ≤ ‖z‖)
    (hsep : ∀ a ∈ A, ∀ z ∈ closedBall y R, d ≤ ‖a-z‖)
    (hq : 0 < q) (hqR : q ≤ 3*R/4) (hb : 0 < b)
    (S : Configuration M → Finset (Fin M)) (Z lam : ℝ) :
    ∀ᵐ u, weightedPatchTestAbs ψ s Z lam y R hb S (fun x => 1/‖x‖) u ≤
      weightedPatchTestAbs ψ s Z lam y R hb S (fun x => 1/max ‖x‖ q) u+
      weightedPatchLocalPotential ψ s y R q hb S u+
      (2*Real.pi*tfPatchDensityCapConstant*q^2/R^6)*formMass (coreSlice ψ s u) := by
  have hqR' : q < R := by linarith
  filter_upwards [hψ.ae_coreSlice s] with u hu
  have he := tfBallPotential_truncated_triangle hq hqR' (retainedPatchLp hb (S u) u y R) _
    (conditionalPatchMinimizer_truncation_loss ψ s u hu A (hcore u) y hR hd hr hnuc hsep hq hqR Z lam)
  rw [tfBallPotential_sub_at_zero] at he
  have hw := mul_le_mul_of_nonneg_left he (formMass_nonneg (coreSlice ψ s u))
  simpa only [weightedPatchTestAbs,weightedPatchLocalPotential,mul_add,mul_comm
    (formMass (coreSlice ψ s u)) (2*Real.pi*tfPatchDensityCapConstant*q^2/R^6)] using hw

lemma weightedPatchFull_integrable_and_bound {N M : ℕ} {ψ : FormVector (N+M)}
    (hψ : SobolevVector ψ) (s : Spins M) (A : Set Space)
    (hcore : ∀ u x i, x i ∉ A → FormZeroAt (coreSlice ψ s u) x)
    (y : Space) {R d r q b : ℝ} (hR : 0 < R) (hd : 0 < d) (hr : 0 < r)
    (hnuc : ∀ z ∈ closedBall y R, r ≤ ‖z‖)
    (hsep : ∀ a ∈ A, ∀ z ∈ closedBall y R, d ≤ ‖a-z‖)
    (hq : 0 < q) (hqR : q ≤ 3*R/4) (hb : 0 < b)
    (S : Configuration M → Finset (Fin M)) (hS : ∀ i, MeasurableSet {u | i ∈ S u})
    (Z lam : ℝ) (hi : Integrable (weightedPatchGap ψ s Z lam y R hb S)) :
    Integrable (weightedPatchTestAbs ψ s Z lam y R hb S (fun x => 1/‖x‖)) ∧
    (∫ u, weightedPatchTestAbs ψ s Z lam y R hb S (fun x => 1/‖x‖) u) ≤
      (∫ u, weightedPatchTestAbs ψ s Z lam y R hb S (fun x => 1/max ‖x‖ q) u)+
      (∫ u, weightedPatchLocalPotential ψ s y R q hb S u)+
      (2*Real.pi*tfPatchDensityCapConstant*q^2/R^6)*(∫ u, formMass (coreSlice ψ s u)) := by
  have hqR' : q < R := by linarith
  have ht := weightedPatchTruncatedAbs_integrable hψ s Z lam y hq hqR' hb S hS hi
  have hl := weightedPatchLocalPotential_integrable hψ s y hq hqR'.le hb S hS
  have hc := (hψ.coreSlice_mass_integrable s).const_mul (2*Real.pi*tfPatchDensityCapConstant*q^2/R^6)
  have hbnd := weightedPatchFull_le hψ s A hcore y hR hd hr hnuc hsep hq hqR hb S Z lam
  have hker : MemLp (fun x : TFSpace => 1/‖x‖) (5/2) (ballMeasure R) := by
    simpa only [one_div] using nuclear_memLp R
  have hm : AEStronglyMeasurable (weightedPatchTestAbs ψ s Z lam y R hb S (fun x => 1/‖x‖)) := by
    have he := (hψ.coreSlice_mass_integrable s).aestronglyMeasurable.mul
      (patchTestError_aestronglyMeasurable hψ s Z lam y R hb S hS hker).norm
    convert he using 1
    rfl
  have hfull : Integrable (weightedPatchTestAbs ψ s Z lam y R hb S (fun x => 1/‖x‖)) := by
    apply ((ht.add hl).add hc).mono' hm
    filter_upwards [hbnd] with u hu
    have hn : 0 ≤ weightedPatchTestAbs ψ s Z lam y R hb S (fun x => 1/‖x‖) u :=
      mul_nonneg (formMass_nonneg _) (abs_nonneg _)
    rw [Real.norm_of_nonneg hn]
    exact hu
  refine ⟨hfull,?_⟩
  have hh := integral_mono_ae hfull ((ht.add hl).add hc) hbnd
  have he := integral_add (ht.add hl) hc
  have he' := integral_add ht hl
  simp only [Pi.add_apply] at he he' hh
  rw [he, he', integral_const_mul] at hh
  exact hh

theorem radial_full_absolute_control {N : ℕ} {ψ : FormVector N}
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
      (∑ c : Fin N → Fin 2, ∑ s : Spins (cutOutNumber c), ∫ u,
        weightedPatchLocalPotential (χ c) s y (t-4*b) q hb (radialPatchRetention N y t b c s) u)+
      (2*Real.pi*tfPatchDensityCapConstant*q^2/(t-4*b)^6)*formMass ψ := by
  dsimp only
  let p := coreFirstRadialCut y ht hb
  let hp := coreFirstRadialCut_partition y ht hb
  let χ := fun c : Fin N → Fin 2 => orderedCutForm p hp ψ c
  have hR : 0 < t-4*b := by linarith
  have hqR' : q < t-4*b := by linarith
  have hχ (c : Fin N → Fin 2) : SobolevVector (χ c) := orderedCutForm_sobolev p hp hψ.sobolevVector c
  have hc (c : Fin N → Fin 2) (s : Spins (cutOutNumber c))
      (u : Configuration (cutOutNumber c)) (v : Configuration (cutCoreNumber c)) (i : Fin (cutCoreNumber c))
      (hi : v i ∉ radialPatchCore y t) : FormZeroAt (coreSlice (χ c) s u) v := by
    apply FormZeroAt.coreSlice
    exact orderedCutForm_core_hole _ _ ψ c (radialPatchCore y t)ᶜ
      (coreFirstRadialCut_core_zero y ht hb) (coreFirstRadialCut_core_deriv_zero y ht hb)
      (joinLists v u) i (by simpa only [joinLists_left,mem_compl_iff] using hi)
  have hbranch (c : Fin N → Fin 2) (s : Spins (cutOutNumber c)) :=
    (weightedPatchFull_integrable_and_bound (hχ c) s (radialPatchCore y t) (hc c s) y hR hb hb
      (radialPatch_nuclear_distance hb hy) (radialPatch_core_distance y hb) hq hqR hb _
      (radialPatchRetention_measurable N y t b c s) Z lam
      (radial_weightedPatchGap_integrable hψ y ht hb htb hy hZ hlam hg hcg hgn hrad hgs c s)).2
  have hsum := Finset.sum_le_sum (s := Finset.univ) (fun c _ =>
    Finset.sum_le_sum (s := Finset.univ) (fun s _ => hbranch c s))
  simp only [Finset.sum_add_distrib,←Finset.mul_sum] at hsum
  have hmass : (∑ c : Fin N → Fin 2, ∑ s : Spins (cutOutNumber c), ∫ u,
      formMass (coreSlice (χ c) s u)) = formMass ψ := by
    simp_rw [SobolevVector.integral_coreSlice_mass (hχ _)]
    exact orderedCutForm_mass_sum p hp hψ.sobolevVector
  rw [hmass] at hsum
  exact hsum.trans (add_le_add (add_le_add
    (radial_truncated_absolute_control hψ y ht hb htb hy hZ hlam hg hcg hgn hrad hgs hq hqR') le_rfl) le_rfl)

end CoulombAtom

end

end OAI
