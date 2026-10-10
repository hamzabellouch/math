import Mathlib
import OAI.Analysis.CoulombIonization.RadialBounds.RadialInside
import OAI.Analysis.CoulombIonization.Variational.CutCoreNumber
import OAI.Analysis.CoulombIonization.FormDomain.CoreKinetic

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
open MeasureTheory Filter
open scoped Topology BigOperators ContDiff InnerProductSpace Convolution
open Filter
open scoped Topology InnerProductSpace
open MeasureTheory Complex Filter
open scoped Topology InnerProductSpace
open MeasureTheory Complex Filter
open scoped Topology InnerProductSpace ContDiff
open MeasureTheory Filter
open scoped Topology BigOperators ContDiff InnerProductSpace Convolution
open MeasureTheory Filter
open scoped Topology BigOperators ContDiff InnerProductSpace
open MeasureTheory Filter
open scoped Topology BigOperators ContDiff InnerProductSpace ENNReal
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open Set Filter Topology InnerProductSpace Laplacian
open MeasureTheory Filter
open scoped Topology
open MeasureTheory Filter
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter
open scoped Topology BigOperators InnerProductSpace
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter
open scoped Topology BigOperators Pointwise
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric Topology InnerProductSpace Laplacian
open scoped Convolution
open scoped RealInnerProductSpace
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric Topology InnerProductSpace Laplacian
open MeasureTheory Filter Set Metric Topology InnerProductSpace Laplacian
open MeasureTheory Filter Set Metric Topology
open MeasureTheory Set Filter Metric Topology InnerProductSpace Laplacian
open MeasureTheory Set Filter Metric Topology InnerProductSpace Laplacian
open MeasureTheory Filter Set Metric Topology
open MeasureTheory Filter Set Metric Topology
open MeasureTheory Filter Set Metric Topology InnerProductSpace Laplacian
open Filter Set Metric Topology InnerProductSpace Laplacian
open MeasureTheory Filter Set Metric Topology
open MeasureTheory Filter Set Metric Topology
open MeasureTheory Filter Set Metric Topology
open MeasureTheory Filter Set Metric Topology
open Filter
open scoped Topology
open MeasureTheory Filter Set Metric Topology
open MeasureTheory Filter Set Metric Topology
open MeasureTheory Complex Filter
open scoped Topology InnerProductSpace ContDiff BigOperators
open MeasureTheory Filter Set
open scoped Topology BigOperators
open MeasureTheory Filter
open scoped Topology BigOperators InnerProductSpace
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open scoped BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped Topology BigOperators
open MeasureTheory Filter
open scoped Topology BigOperators
namespace CoulombAtom

lemma orderedCutForm_zero_of_factor {L : ℕ}
    (p : Fin 2 → SmoothMultiplier spaceDirections)
    (hp : ∀ x, ∑ h : Fin 2, (p h).value x ^ 2 = 1)
    (ψ : FormVector L) (b : Fin L → Fin 2)
    (s : Spins (cutCoreNumber b + cutOutNumber b))
    (x : Configuration (cutCoreNumber b + cutOutNumber b)) (i : Fin (cutOutNumber b))
    (hzero : (p 1).value (x (finSumFinEquiv (Sum.inr i))) = 0) :
    (orderedCutForm p hp ψ b).value s x = 0 := by
  classical
  rw [orderedCutForm_value]
  change (spatialProductValue p (coreCutLabels (cutCoreNumber b) (cutOutNumber b)) x : ℂ) * _ = 0
  have hh : spatialProductValue p (coreCutLabels (cutCoreNumber b) (cutOutNumber b)) x = 0 := by
    apply Finset.prod_eq_zero (Finset.mem_univ (finSumFinEquiv (Sum.inr i)))
    simpa only [coreCutLabels,joinLists_right] using hzero
  rw [hh,Complex.ofReal_zero,zero_mul]

lemma cut_exterior_energy_lower {L : ℕ}
    (p : Fin 2 → SmoothMultiplier spaceDirections)
    (hp : ∀ x, ∑ h : Fin 2, (p h).value x ^ 2 = 1)
    {ψ : FormVector L} (hψ : SobolevVector ψ) (b : Fin L → Fin 2)
    {Z R : ℝ} (hZ : 0 ≤ Z) (hR : 0 < R)
    (hs : ∀ x, ‖x‖ < R → (p 1).value x = 0) :
    -(Z/R) * cutOutNumber b * formMass (multiplyForm (spatialProduct p hp b) ψ) ≤
      formEnergy Z (multiplyForm (spatialProduct p hp b) ψ) - cutCoreEnergy p hp Z ψ b := by
  have hq := orderedCutForm_sobolev p hp hψ b
  have hn := outNuclear_le hq hR (fun s x i hx => orderedCutForm_zero_of_factor p hp ψ b s x i (hs _ hx))
  have he := exterior_energy_lower hq Z
  rw [orderedCutForm_mass] at hn
  rw [orderedCutForm_energy] at he
  change -Z * outNuclear (orderedCutForm p hp ψ b) ≤
    formEnergy Z (multiplyForm (spatialProduct p hp b) ψ) - cutCoreEnergy p hp Z ψ b at he
  have hh := mul_le_mul_of_nonpos_left hn (neg_nonpos.mpr hZ)
  calc
    _ = -Z * ((cutOutNumber b : ℝ)/R * formMass (multiplyForm (spatialProduct p hp b) ψ)) := by ring
    _ ≤ _ := hh.trans he

def cutExpectedOut {L : ℕ} (p : Fin 2 → SmoothMultiplier spaceDirections)
    (hp : ∀ x, ∑ h : Fin 2, (p h).value x ^ 2 = 1) (ψ : FormVector L) : ℝ :=
  ∑ b : Fin L → Fin 2, cutOutNumber b * formMass (multiplyForm (spatialProduct p hp b) ψ)

lemma cutExpectedOut_nonneg {L : ℕ} (p : Fin 2 → SmoothMultiplier spaceDirections)
    (hp : ∀ x, ∑ h : Fin 2, (p h).value x ^ 2 = 1) (ψ : FormVector L) :
    0 ≤ cutExpectedOut p hp ψ :=
  Finset.sum_nonneg fun _ _ => mul_nonneg (Nat.cast_nonneg _) (formMass_nonneg _)

theorem fock_priced_exterior_bound {L : ℕ}
    (p : Fin 2 → SmoothMultiplier spaceDirections)
    (hp : ∀ x, ∑ h : Fin 2, (p h).value x ^ 2 = 1)
    {ψ : FormVector L} (hψ : SobolevFermion ψ) {Z lam ε R : ℝ}
    (hZ : 0 ≤ Z) (hlam : 0 < lam) (hR : 0 < R)
    (hs : ∀ x, ‖x‖ < R → (p 1).value x = 0)
    (hm : formMass ψ = 1)
    (he : formEnergy Z ψ + lam * L ≤ priceEnergy (energy Z) lam + ε) :
    (lam-Z/R) * cutExpectedOut p hp ψ ≤
      ε + (1/2:ℝ) * weightedParticleCount ψ (spatialErrorWeight p) := by
  have hh := fock_cut_deletion p hp hψ hZ hlam hm he
  apply le_trans _ hh
  unfold cutExpectedOut
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum; intro b _
  have hp' := cut_exterior_energy_lower p hp hψ.sobolevVector b hZ hR hs
  nlinarith

lemma weightedParticleCount_le_const {L : ℕ} {ψ : FormVector L}
    (hψ : SobolevVector ψ) (w : Space → ℝ)
    (hw : ∀ s i, Integrable (fun x => w (x i) * ‖ψ.value s x‖^2))
    {C : ℝ} (hC : ∀ x, w x ≤ C) :
    weightedParticleCount ψ w ≤ C * L * formMass ψ := by
  have hh (s : Spins L) (i : Fin L) :
      (∫ x, w (x i) * ‖ψ.value s x‖^2) ≤ C * (∫ x, ‖ψ.value s x‖^2) := by
    rw [← integral_const_mul]
    apply integral_mono (hw s i) ((hψ.1 s).norm.integrable_sq.const_mul C)
    intro x
    exact mul_le_mul_of_nonneg_right (hC (x i)) (sq_nonneg _)
  calc
    _ ≤ ∑ s : Spins L, ∑ _i : Fin L, C * (∫ x, ‖ψ.value s x‖^2) :=
      Finset.sum_le_sum fun s _ => Finset.sum_le_sum fun i _ => hh s i
    _ = _ := by
      simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,formMass]
      simp_rw [← mul_assoc,← Finset.mul_sum]
      ring

theorem radial_priced_exterior_bound {L : ℕ} {ψ : FormVector L}
    (hψ : SobolevFermion ψ) {Z lam ε R : ℝ}
    (hZ : 0 ≤ Z) (hlam : 0 < lam) (hR : 0 < R)
    (hm : formMass ψ = 1)
    (he : formEnergy Z ψ + lam * L ≤ priceEnergy (energy Z) lam + ε) :
    (lam-Z/R) * cutExpectedOut (radialCut 0 hR.le hR) (radialCut_partition 0 hR.le hR) ψ ≤
      ε + (3/2:ℝ) * (Real.pi * smoothTransitionBound / R)^2 * L := by
  have hcut := fock_priced_exterior_bound (radialCut 0 hR.le hR)
    (radialCut_partition 0 hR.le hR) hψ hZ hlam hR
    (fun x hx => (radialCut_inner hR.le hR (by simpa only [sub_zero] using hx.le)).2) hm he
  have hb : ∀ x, spatialErrorWeight (radialCut 0 hR.le hR) x ≤
      3 * (Real.pi * smoothTransitionBound / R)^2 := by
    intro x
    have hh := radialCut_error_bound 0 hR.le hR x
    split_ifs at hh with hx
    · simpa only [mul_one] using hh
    · simp only [mul_zero] at hh
      exact hh.trans (by positivity)
  have hw := weightedParticleCount_le_const hψ.sobolevVector _
    (fun s i => spatial_error_weight_integrable _ hψ.sobolevVector s i) hb
  rw [hm,mul_one] at hw
  linarith

end CoulombAtom

open MeasureTheory Filter
open scoped Topology BigOperators

end

end OAI
