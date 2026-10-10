import Mathlib
import OAI.Analysis.CoulombIonization.FieldAnalysis.DeletedFieldBudget
import OAI.Analysis.CoulombIonization.RadialBounds.RadialSelectedCounts

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory Set Filter Metric
open scoped BigOperators ContDiff

namespace CoulombAtom
open CoulombAnalysis CoulombNeumann

def freshPatchMass {L : ℕ} (p : Fin 2 → SmoothMultiplier spaceDirections)
    (hp : ∀ x, ∑ a, (p a).value x^2 = 1) (ψ : FormVector L)
    (Z lam : ℝ) (y : Space) (R : ℝ) : ℝ :=
  ∑ c : Fin L → Fin 2, ∑ s : Spins (cutOutNumber c), ∫ u,
    weightedPatchMass (orderedCutForm p hp ψ c) s Z lam y R u

lemma freshPatchMass_nonneg {L : ℕ} (p : Fin 2 → SmoothMultiplier spaceDirections)
    (hp : ∀ x, ∑ a, (p a).value x^2 = 1) (ψ : FormVector L)
    (Z lam : ℝ) (y : Space) (R : ℝ) : 0 ≤ freshPatchMass p hp ψ Z lam y R := by
  apply Finset.sum_nonneg; intro c _
  apply Finset.sum_nonneg; intro s _
  exact integral_nonneg (weightedPatchMass_nonneg _ _ _ _ _ _)

lemma radial_weightedPatchMass_integrable {L : ℕ} {ψ : FormVector L} (hψ : SobolevVector ψ)
    (y : Space) {t b : ℝ} (ht : 0 ≤ t) (hb : 0 < b) (htb : 4*b < t) (hy : t ≤ ‖y‖)
    (Z lam : ℝ) (c : Fin L → Fin 2) (s : Spins (cutOutNumber c)) :
    Integrable (weightedPatchMass (orderedCutForm (coreFirstRadialCut y ht hb)
      (coreFirstRadialCut_partition y ht hb) ψ c) s Z lam y (t-4*b)) := by
  apply weightedPatchMass_integrable
    (orderedCutForm_sobolev (coreFirstRadialCut y ht hb) (coreFirstRadialCut_partition y ht hb) hψ c)
    s y (sub_pos.mpr htb) Z lam hb (radialPatchCore y t) _
    (radialPatch_nuclear_distance hb hy) (radialPatch_core_distance y hb)
  intro u x i hi
  apply FormZeroAt.coreSlice
  exact orderedCutForm_core_hole _ _ ψ c (radialPatchCore y t)ᶜ
    (coreFirstRadialCut_core_zero y ht hb) (coreFirstRadialCut_core_deriv_zero y ht hb)
    (joinLists x u) i (by simpa only [joinLists_left,mem_compl_iff] using hi)

lemma radial_fresh_tail_split {L : ℕ} {ψ : FormVector L} (hψ : SobolevVector ψ)
    (y : Space) {t b : ℝ} (ht : 0 ≤ t) (hb : 0 < b) (htb : 4*b < t) (hy : t ≤ ‖y‖)
    (Z lam K : ℝ) :
    let p := coreFirstRadialCut y ht hb
    let hp := coreFirstRadialCut_partition y ht hb
    (∑ c : Fin L → Fin 2, ∑ s : Spins (cutOutNumber c), ∫ u,
      conditionalFieldSum Z lam (orderedCutForm p hp ψ c) s u-
      conditionalRetainedFieldSum Z lam (orderedCutForm p hp ψ c) s (radialPatchRetention L y t b c s) u+
      K*weightedPatchMass (orderedCutForm p hp ψ c) s Z lam y (t-4*b) u) =
    (∑ c : Fin L → Fin 2, ∑ s : Spins (cutOutNumber c), ∫ u,
      conditionalFieldSum Z lam (orderedCutForm p hp ψ c) s u-
      conditionalRetainedFieldSum Z lam (orderedCutForm p hp ψ c) s (radialPatchRetention L y t b c s) u)+
      K*freshPatchMass p hp ψ Z lam y (t-4*b) := by
  dsimp only
  simp only [freshPatchMass,Finset.mul_sum,←Finset.sum_add_distrib]
  apply Finset.sum_congr rfl; intro c _
  apply Finset.sum_congr rfl; intro s _
  have hχ := orderedCutForm_sobolev (coreFirstRadialCut y ht hb) (coreFirstRadialCut_partition y ht hb) hψ c
  have hh := integral_add
    ((conditionalFieldSum_integrable hχ Z lam s).sub
      (conditionalRetainedFieldSum_integrable hχ Z lam s _ (radialPatchRetention_measurable L y t b c s)))
    ((radial_weightedPatchMass_integrable hψ y ht hb htb hy Z lam c s).const_mul K)
  simpa only [Pi.sub_apply,integral_const_mul] using hh

theorem selected_fresh_patch_budget {L : ℕ} {ψ : FormVector L}
    (hψ : SobolevFermion ψ) (hm : formMass ψ = 1) (y : Space) {a b : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hba : 7*b < 5*a) (hy : 6*a+2*b ≤ ‖y‖)
    {Z lam : ℝ} (hZ : 0 ≤ Z) (hlam : 0 < lam)
    {g : Space → ℝ} (hg : ContDiff ℝ ∞ g) (hcg : HasCompactSupport g)
    (hgn : ∫ z : Space, (g z)^2 = 1) (hr : IsRadial g) (hgs : tsupport g ⊆ ball 0 1) :
    ∃ t ∈ Icc (5*a) (6*a), ∃ ht : 0 ≤ t,
      let p := coreFirstRadialCut y ht hb
      let hp := coreFirstRadialCut_partition y ht hb
      let B := ∫ x, rawBallCount y (7*a) x^2 ∂formRawLaw ψ
      (∑ c : Fin L → Fin 2, ∑ s : Spins (cutOutNumber c), ∫ u,
        weightedPatchGap (orderedCutForm p hp ψ c) s Z lam y (t-4*b) hb
          (radialPatchRetention L y t b c s) u) ≤
        corePriceExcess Z lam ψ+
        (3/2:ℝ)*(Real.pi*smoothTransitionBound/b)^2*((8*b/a)*B)^(1/2:ℝ)+
        b⁻¹^2*neumannRemainderConstant*(B^(2/3:ℝ)+B^(1/2:ℝ))+
        (((2*Real.pi+1)/2)/b)*B^(1/2:ℝ)+
        Real.sqrt (freshOutMaximumSecondMoment p hp ψ Z lam)*Real.sqrt ((8*b/a)*B)+
        ((packetDirichlet g/2)*b⁻¹^2)*freshPatchMass p hp ψ Z lam y (t-4*b) := by
  obtain ⟨t,ht,ht0,hd,hfirst,h43,hims⟩ :=
    radial_fresh_selected_counts hψ.sobolevVector hm y ha hb (by linarith)
  refine ⟨t,ht,ht0,?_⟩
  have htb : 7*b < t := lt_of_lt_of_le hba ht.1
  have hty : t+2*b ≤ ‖y‖ := le_trans (by linarith [ht.2]) hy
  have he := radial_fresh_patch_budget hψ y hb htb (by linarith) hZ hlam hg hcg hgn hr hgs
  dsimp only at he ⊢
  rw [radial_fresh_tail_split hψ.sobolevVector y _ hb (by linarith) (by linarith)] at he
  have hdel := radial_deleted_field_budget hψ.sobolevVector y ht0 hb hty hZ hlam.le
  dsimp only at hdel
  have hds := mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hd)
    (Real.sqrt_nonneg (freshOutMaximumSecondMoment (coreFirstRadialCut y ht0 hb) (coreFirstRadialCut_partition y ht0 hb) ψ Z lam))
  have h43' := mul_le_mul_of_nonneg_left h43
    (mul_nonneg (sq_nonneg b⁻¹) neumannRemainderConstant_pos.le)
  have hfirst' := mul_le_mul_of_nonneg_left hfirst
    (by positivity : 0 ≤ (((2*Real.pi+1)/2)/b))
  linarith

end CoulombAtom

end

end OAI
