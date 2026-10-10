import Mathlib
import OAI.Analysis.CoulombRadii.Variational.CorrectionDensity

namespace OAI

section
section
noncomputable section
open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
namespace NeutralAtom
open scoped Convolution
open ContinuousLinearMap

def tfReaction (t : ℝ) : ℝ := 4*Real.pi*kTF*(max t 0)^(3/2 : ℝ)

def cutoffReaction (a : ℝ) (F : Position → ℝ) : Position → ℝ :=
  {x : Position | a ≤ ‖x‖}.indicator (fun x => tfReaction (F x))

def screenedPotential (lam : ℝ) (σ : Position → ℝ) (x : Position) : ℝ :=
  lam*coulombKernel x-potentialOf σ x

def barrierSource (a : ℝ) (U σ p : Position → ℝ) (x : Position) : ℝ :=
  (4*Real.pi)*({y : Position | ‖y‖ < a}.indicator σ x)-
    (4*Real.pi)*p x+cutoffReaction a U x

theorem tfReaction_nonneg (t : ℝ) : 0 ≤ tfReaction t := by
  have := kTF_pos
  unfold tfReaction
  positivity

theorem tfReaction_monotone : Monotone tfReaction := by
  intro x y hxy
  unfold tfReaction
  have := kTF_pos
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply Real.rpow_le_rpow (le_max_right _ _) (max_le_max hxy le_rfl)
  norm_num

theorem tfReaction_continuous : Continuous tfReaction := by
  exact continuous_const.mul ((Real.continuous_rpow_const (by norm_num : (0:ℝ)≤3/2)).comp
    (continuous_id.max continuous_const))

theorem cutoffReaction_locallyIntegrable {a A : ℝ} {F : Position → ℝ}
    (hm : Measurable F) (hbd : ∀ x, a ≤ ‖x‖ → F x ≤ A) :
    LocallyIntegrable (cutoffReaction a F) := by
  have hmeas : Measurable (cutoffReaction a F) :=
    (tfReaction_continuous.measurable.comp hm).indicator
      (isClosed_le continuous_const continuous_norm).measurableSet
  apply (locallyIntegrable_const (tfReaction A)).mono hmeas.aestronglyMeasurable
  apply Filter.Eventually.of_forall
  intro x
  by_cases hx : a ≤ ‖x‖
  · have hh := tfReaction_monotone (hbd x hx)
    simpa [cutoffReaction, hx, Real.norm_eq_abs,
      abs_of_nonneg (tfReaction_nonneg _)] using hh
  · simp [cutoffReaction, hx]

theorem screenedPotential_measurable {lam A : ℝ} {σ : Position → ℝ}
    (hσ : Integrable σ) (hσpos : ∀ x, 0 ≤ σ x) (hσbd : ∀ x, σ x ≤ A) :
    Measurable (screenedPotential lam σ) :=
  (measurable_const.mul measurable_coulombKernel).sub
    (potentialOf_continuous hσ hσpos hσbd).measurable

theorem screenedPotential_upper {lam a : ℝ} {σ : Position → ℝ}
    (ha : 0 < a) (hσpos : ∀ x, 0 ≤ σ x) {x : Position} (hx : a ≤ ‖x‖) :
    screenedPotential lam σ x ≤ |lam|/a := by
  have hK : 0 ≤ coulombKernel x := coulombKernel_nonneg x
  have hKa : coulombKernel x ≤ a⁻¹ := inv_anti₀ ha hx
  have hp := potentialOf_nonneg hσpos x
  dsimp [screenedPotential]
  calc
    lam*coulombKernel x-potentialOf σ x ≤ lam*coulombKernel x := sub_le_self _ hp
    _ ≤ |lam| *coulombKernel x := mul_le_mul_of_nonneg_right (le_abs_self _) hK
    _ ≤ |lam| *a⁻¹ := mul_le_mul_of_nonneg_left hKa (abs_nonneg _)
    _ = _ := by rw [div_eq_mul_inv]

theorem barrier_difference_weakGE {U σ p e : Position → ℝ}
    {lam a S c AU Aσ Ap Ae : ℝ} (ha : 0 < a)
    (hU : Continuous (fun x => U x-lam*coulombKernel x))
    (hUbd : ∀ x, a ≤ ‖x‖ → U x ≤ AU)
    (hσ : Integrable σ) (hσpos : ∀ x, 0 ≤ σ x) (hσbd : ∀ x, σ x ≤ Aσ)
    (hp : Integrable p) (hppos : ∀ x, 0 ≤ p x) (hpbd : ∀ x, p x ≤ Ap)
    (he : Integrable e) (hepos : ∀ x, 0 ≤ e x) (hebd : ∀ x, e x ≤ Ae)
    (hw : WeakNuclearSubsolution U lam (Metric.ball 0 S) (barrierSource a U σ p))
    (hband : ∀ x ∈ Metric.ball (0 : Position) S, a ≤ ‖x‖ →
      (4*Real.pi)*σ x ≤ tfReaction (screenedPotential lam σ x)+(4*Real.pi)*e x) :
    WeakLaplacianGE
      (fun x => U x-screenedPotential lam σ x-potentialOf (fun y => p y+e y) x-c)
      (Metric.ball 0 S) (fun x => cutoffReaction a U x-cutoffReaction a (screenedPotential lam σ) x) := by
  have hmU : Measurable U := by
    have hm : Measurable (fun x => U x-lam*coulombKernel x+lam*coulombKernel x) :=
      hU.measurable.add (measurable_coulombKernel.const_mul lam)
    simpa only [sub_add_cancel] using hm
  have hiU := cutoffReaction_locallyIntegrable hmU hUbd
  have hiF := cutoffReaction_locallyIntegrable
    (screenedPotential_measurable (lam := lam) hσ hσpos hσbd)
    (fun x hx => screenedPotential_upper ha hσpos hx)
  have hiσ : LocallyIntegrable (fun x => (4*Real.pi)*({x : Position | ‖x‖ < a}.indicator σ) x) :=
    (hσ.locallyIntegrable.indicator
      (isOpen_lt continuous_norm continuous_const).measurableSet).smul (4*Real.pi)
  have his : LocallyIntegrable (barrierSource a U σ p) :=
    (hiσ.sub (hp.locallyIntegrable.smul (4*Real.pi))).add hiU
  apply cancel_nuclear_source hU hσ hσpos hσbd
    (hp.add he) (fun x => add_nonneg (hppos x) (hepos x))
    (fun x => add_le_add (hpbd x) (hebd x))
    (his.locallyIntegrableOn _) ((hiU.sub hiF).locallyIntegrableOn _) hw
  intro x hx
  change cutoffReaction a U x-cutoffReaction a (screenedPotential lam σ) x ≤
    barrierSource a U σ p x-(4*Real.pi)*σ x+(4*Real.pi)*(p x+e x)
  by_cases hin : ‖x‖ < a
  · simp only [barrierSource, cutoffReaction, Set.indicator, Set.mem_ofPred_eq,
      ite_eq_left hin, ite_eq_right (not_le.mpr hin), sub_self]
    have he0 := hepos x
    nlinarith [Real.pi_pos]
  · have hout : a ≤ ‖x‖ := le_of_not_gt hin
    have hh := hband x hx hout
    simp only [barrierSource, cutoffReaction, Set.indicator, Set.mem_ofPred_eq,
      ite_eq_right hin, ite_eq_left hout, mul_zero]
    linarith

theorem positive_barrier_comparison {U σ p e : Position → ℝ}
    {lam a S c AU Aσ Ap Ae : ℝ} (ha : 0 < a) (hS : 0 < S) (hc : 0 ≤ c)
    (hU : Continuous (fun x => U x-lam*coulombKernel x))
    (hUbd : ∀ x, a ≤ ‖x‖ → U x ≤ AU)
    (hσ : Integrable σ) (hσpos : ∀ x, 0 ≤ σ x) (hσbd : ∀ x, σ x ≤ Aσ)
    (hp : Integrable p) (hppos : ∀ x, 0 ≤ p x) (hpbd : ∀ x, p x ≤ Ap)
    (he : Integrable e) (hepos : ∀ x, 0 ≤ e x) (hebd : ∀ x, e x ≤ Ae)
    (hw : WeakNuclearSubsolution U lam (Metric.ball 0 S) (barrierSource a U σ p))
    (hband : ∀ x ∈ Metric.ball (0 : Position) S, a ≤ ‖x‖ →
      (4*Real.pi)*σ x ≤ tfReaction (screenedPotential lam σ x)+(4*Real.pi)*e x)
    (hbdy : ∀ x : Position, ‖x‖ = S →
      U x-screenedPotential lam σ x-potentialOf (fun y => p y+e y) x-c ≤ 0) :
    ∀ x ∈ Metric.closedBall (0 : Position) S,
      U x ≤ screenedPotential lam σ x+potentialOf (fun y => p y+e y) x+c := by
  have hmU : Measurable U := by
    have hm : Measurable (fun x => U x-lam*coulombKernel x+lam*coulombKernel x) :=
      hU.measurable.add (measurable_coulombKernel.const_mul lam)
    simpa only [sub_add_cancel] using hm
  have hiU := cutoffReaction_locallyIntegrable hmU hUbd
  have hiF := cutoffReaction_locallyIntegrable
    (screenedPotential_measurable (lam := lam) hσ hσpos hσbd)
    (fun x hx => screenedPotential_upper ha hσpos hx)
  have hη := hp.add he
  have hηpos : ∀ x, 0 ≤ p x+e x := fun x => add_nonneg (hppos x) (hepos x)
  have hηbd : ∀ x, p x+e x ≤ Ap+Ae := fun x => add_le_add (hpbd x) (hebd x)
  have hcont : Continuous (fun x => U x-screenedPotential lam σ x-
      potentialOf (fun y => p y+e y) x-c) := by
    have hh := ((hU.add (potentialOf_continuous hσ hσpos hσbd)).sub
      (potentialOf_continuous hη hηpos hηbd)).sub (continuous_const (y := c))
    convert hh using 1
    funext x
    change U x-(lam*coulombKernel x-potentialOf σ x)-potentialOf (p+e) x-c =
      U x-lam*coulombKernel x+potentialOf σ x-potentialOf (p+e) x-c
    ring
  apply weak_comparison_closedBall hS hc hcont.continuousOn
    (fun x _ => potentialOf_nonneg hηpos x) hbdy
    (barrier_difference_weakGE ha hU hUbd hσ hσpos hσbd
      hp hppos hpbd he hepos hebd hw hband) ((hiU.sub hiF).locallyIntegrableOn _)
  intro x _ hx
  by_cases hax : a ≤ ‖x‖
  · simp only [cutoffReaction, Set.indicator, Set.mem_ofPred_eq, ite_eq_left hax]
    exact sub_nonneg.mpr (tfReaction_monotone hx.le)
  · simp [cutoffReaction, hax]

end NeutralAtom
end

end
end

end OAI
