import Mathlib
import OAI.Analysis.Conductivity.Variational.DerivativeEquiv

namespace OAI

noncomputable section
open MeasureTheory
open scoped ENNReal
open Matrix Filter Topology
open Set MeasureTheory Filter Topology
open scoped BigOperators
namespace ScalarConductivity

def transitionMajorant (θ δ t : ℝ) : ℝ :=
  periodicPulse (2 * δ) δ (t + δ) + periodicPulse (2 * δ) δ (t - θ + δ)

lemma transitionMajorant_smooth {θ δ : ℝ} (hδ : 0 < δ) :
    ContDiff ℝ (↑(⊤ : ℕ∞)) (transitionMajorant θ δ) := by
  have hp := periodicPulse_smooth (by positivity : 0 ≤ 2 * δ) hδ
  exact (hp.comp (contDiff_id.add contDiff_const)).add
    (hp.comp ((contDiff_id.sub contDiff_const).add contDiff_const))

lemma transitionMajorant_periodic (θ δ : ℝ) :
    Function.Periodic (transitionMajorant θ δ) 1 := by
  intro t
  simp only [transitionMajorant]
  rw [show t + 1 + δ = (t + δ) + 1 by ring,
    show t + 1 - θ + δ = (t - θ + δ) + 1 by ring,
    periodicPulse_periodic, periodicPulse_periodic]

lemma transitionMajorant_bounds {θ δ : ℝ} (hδ : 0 < δ) (hw : 3 * δ ≤ 1) (t : ℝ) :
    0 ≤ transitionMajorant θ δ t ∧ transitionMajorant θ δ t ≤ 2 := by
  have h₁ := periodicPulse_bounds hδ (by linarith : δ ≤ 2 * δ)
    (by linarith : 2 * δ + δ ≤ 1) (t + δ)
  have h₂ := periodicPulse_bounds hδ (by linarith : δ ≤ 2 * δ)
    (by linarith : 2 * δ + δ ≤ 1) (t - θ + δ)
  unfold transitionMajorant
  constructor <;> linarith [h₁.1, h₁.2, h₂.1, h₂.2]

lemma periodicPulse_shift_integral {θ δ : ℝ} (hθ : 0 ≤ θ) (hδ : 0 < δ)
    (hw : θ + δ ≤ 1) (r : ℝ) :
    (∫ t in (0 : ℝ)..1, periodicPulse θ δ (t + r)) = θ := by
  rw [intervalIntegral.integral_comp_add_right]
  have he := (periodicPulse_periodic θ δ).intervalIntegral_add_eq r 0
  simp only [zero_add] at he
  rw [zero_add, add_comm 1 r, he, periodicPulse_integral hθ hδ hw]

lemma transitionMajorant_integral {θ δ : ℝ} (hδ : 0 < δ) (hw : 3 * δ ≤ 1) :
    (∫ t in (0 : ℝ)..1, transitionMajorant θ δ t) = 4 * δ := by
  have hp := periodicPulse_smooth (by positivity : 0 ≤ 2 * δ) hδ
  have hi₁ : IntervalIntegrable (fun t : ℝ => periodicPulse (2 * δ) δ (t + δ)) volume 0 1 :=
    (hp.continuous.comp (continuous_id.add continuous_const)).intervalIntegrable _ _
  have hi₂ : IntervalIntegrable (fun t : ℝ => periodicPulse (2 * δ) δ (t - θ + δ)) volume 0 1 :=
    (hp.continuous.comp ((continuous_id.sub continuous_const).add continuous_const)).intervalIntegrable _ _
  dsimp [transitionMajorant]
  rw [intervalIntegral.integral_add hi₁ hi₂]
  simp_rw [show ∀ t : ℝ, t - θ + δ = t + (δ - θ) by intro t; ring]
  rw [periodicPulse_shift_integral (by positivity) hδ (by linarith),
    periodicPulse_shift_integral (by positivity) hδ (by linarith)]
  ring

lemma periodicPulse_impure_subset {θ δ t : ℝ} (hδ : 0 < δ) (hδθ : δ ≤ θ)
    (hw : θ + δ ≤ 1) (ht : t ∈ Icc 0 1)
    (hl : periodicPulse θ δ t ≠ 0) (hu : periodicPulse θ δ t ≠ 1) :
    t ∈ Ioo 0 δ ∪ Ioo θ (θ + δ) := by
  have hθ : 0 ≤ θ := hδ.le.trans hδθ
  rw [periodicPulse_eq hθ hδ hw ht] at hl hu
  by_cases htd : t < δ
  · left
    refine ⟨?_, htd⟩
    by_contra hn
    exact hl (flatPulse_zero_left hθ hδ (not_lt.mp hn))
  · right
    constructor
    · by_contra hn
      exact hu (flatPulse_one hδ (not_lt.mp htd) (not_lt.mp hn))
    · by_contra hn
      exact hl (flatPulse_zero_right hθ hδ (not_lt.mp hn))

lemma transitionMajorant_dominates {θ δ t : ℝ} (hδ : 0 < δ) (hδθ : δ ≤ θ)
    (hw : θ + δ ≤ 1) (hδw : 3 * δ ≤ 1)
    (hl : periodicPulse θ δ t ≠ 0) (hu : periodicPulse θ δ t ≠ 1) :
    1 ≤ transitionMajorant θ δ t := by
  let r := t - (⌊t⌋ : ℤ)
  have hr : r ∈ Icc (0 : ℝ) 1 :=
    ⟨Int.fract_nonneg _, (Int.fract_lt_one _).le⟩
  have hp : periodicPulse θ δ r = periodicPulse θ δ t := by
    simpa [r] using (periodicPulse_periodic θ δ).sub_zsmul_eq (x := t) ⌊t⌋
  have hm : transitionMajorant θ δ r = transitionMajorant θ δ t := by
    simpa [r] using (transitionMajorant_periodic θ δ).sub_zsmul_eq (x := t) ⌊t⌋
  rw [← hm]
  have hbase := periodicPulse_bounds hδ (by linarith : δ ≤ 2 * δ)
    (by linarith : 2 * δ + δ ≤ 1)
  have heq (v : ℝ) (hv : v ∈ Icc δ (2 * δ)) : periodicPulse (2 * δ) δ v = 1 := by
    rw [periodicPulse_eq (by positivity) hδ (by linarith)
      (show v ∈ Icc 0 1 from ⟨by linarith [hv.1], by linarith [hv.2]⟩)]
    exact flatPulse_one hδ hv.1 hv.2
  rcases periodicPulse_impure_subset hδ hδθ hw hr (by rwa [hp]) (by rwa [hp]) with hr' | hr'
  · unfold transitionMajorant
    rw [heq (r + δ) ⟨by linarith [hr'.1], by linarith [hr'.2]⟩]
    linarith [(hbase (r - θ + δ)).1]
  · unfold transitionMajorant
    rw [heq (r - θ + δ) ⟨by linarith [hr'.1], by linarith [hr'.2]⟩]
    linarith [(hbase (r + δ)).1]

end ScalarConductivity

end

end OAI
