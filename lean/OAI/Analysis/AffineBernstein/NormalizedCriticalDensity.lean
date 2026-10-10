import Mathlib
import OAI.Analysis.AffineBernstein.ABPCriticalDensity
import OAI.Analysis.AffineBernstein.NormalizedLogVariance

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
namespace AffineBernstein
noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal

section NormalizedCriticalDensity

/-- Uniform positive low-set measure, with no hidden ellipticity assumption. -/
theorem normalized_critical_density {n : ℕ} (hn : 1 ≤ n) {ρ R : ℝ}
    (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (hR : 1 ≤ R) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ v : Space n → ℝ, BalancedNormalized ρ R v →
      ∀ s : Space n → ℝ, ContDiff ℝ ∞ s → (∀ x, 0 ≤ s x) →
      (∀ x, inverseHessianTrace v s x ≤ 0) → ∀ a ∈ Metric.ball (0:Space n) (1/64:ℝ),
      ∀ ε : ℝ, 0 < ε → s a ≤ ε →
      δ ≤ (volume {x | x ∈ Metric.closedBall (0:Space n) (1/16:ℝ) ∧ s x ≤ 2*ε}).toReal := by
  obtain ⟨c,C,hc,hC,Hdet⟩ := normalized_balanced_det_bounds hρ hρ1 hR (n := n)
  let h := normalizedModulus ρ R (1/64:ℝ)/2
  have hh : 0 < h := half_pos (normalizedModulus_pos hρ)
  have hnp : 0 < (n:ℝ) := by exact_mod_cast hn
  let D := C*(2*(n:ℝ)/h)^n
  have hD : 0 < D := by dsimp [D]; positivity
  let δ := (volume (Metric.ball (0:Space n) (32:ℝ))).toReal/D
  have hballfin : volume (Metric.ball (0:Space n) (32:ℝ)) ≠ ⊤ := measure_ball_lt_top.ne
  have hballpos : 0 < volume (Metric.ball (0:Space n) (32:ℝ)) :=
    Metric.measure_ball_pos volume _ (by norm_num)
  have hδ : 0 < δ := div_pos (ENNReal.toReal_pos hballpos.ne' hballfin) hD
  refine ⟨δ,hδ,?_⟩
  intro v hv s hs hspos hLs a ha ε hε hsa
  let K := {x | tangentHeight v a x ≤ h}
  let B := Metric.closedBall (0:Space n) (1/16:ℝ)
  have hK : IsCompact K := by
    simpa only [K,mem_univ,true_and] using isCompact_tangent_sublevel isOpen_univ convex_univ hv.smooth.contDiffOn
      (fun x _ => hv.posDef x) (euclideanGraphComplete_entire hv.smooth) (mem_univ a) h
  have han : ‖a‖ < (1/64:ℝ) := by simpa only [Metric.mem_ball,dist_zero_right] using ha
  have ham : a ∈ Metric.ball (0:Space n) (1/4:ℝ) := by
    rw [Metric.mem_ball,dist_zero_right]; linarith
  have hsmall (x : Space n) (hx : x ∈ K) : x ∈ Metric.ball a (1/64:ℝ) := by
    apply normalized_modulus_of_sectionBalance hv.smooth hv.posDef
      (euclideanGraphComplete_entire hv.smooth) hv.zero hv.deriv_zero hρ hρ1 hR
      hv.balance hv.inner hv.outer ham (by norm_num : (0:ℝ)<1/64)
    refine ⟨mem_univ x,?_⟩
    have hx' : tangentHeight v a x ≤ h := hx
    have hh' := normalizedModulus_pos (R := R) (r := (1/64:ℝ)) hρ
    dsimp [h] at hx'
    linarith
  have hKB : K ⊆ B := by
    intro x hx
    have hxn : ‖x-a‖ < (1/64:ℝ) := by
      simpa only [Metric.mem_ball,dist_eq_norm] using hsmall x hx
    have H := norm_add_le (x-a) a
    rw [sub_add_cancel] at H
    rw [Metric.mem_closedBall,dist_zero_right]
    linarith
  have hKC (x : Space n) (hx : tangentHeight v a x ≤ h) : (hessian v x).det ≤ C := by
    have hxB := hKB hx
    have hxn : ‖x‖ ≤ (1/16:ℝ) := by simpa only [B,Metric.mem_closedBall,dist_zero_right] using hxB
    exact (Hdet v hv.smooth hv.posDef hv.maximal hv.zero hv.deriv_zero hv.balance hv.inner hv.outer x
      (by rw [Metric.mem_ball,dist_zero_right]; linarith)).2
  have habp := linearizedMA_critical_density hv.smooth hs hv.posDef hh hε
    (by norm_num : (0:ℝ)<1/64) hC.le hK (fun x hx => Metric.ball_subset_closedBall (hsmall x hx))
    hspos hsa hLs hKC
  norm_num only [show 1/(2*(1/64:ℝ))=(32:ℝ) by norm_num] at habp
  let L := {x | tangentHeight v a x ≤ h ∧ s x ≤ 2*ε}
  let T := {x | x ∈ B ∧ s x ≤ 2*ε}
  have hLT : L ⊆ T := fun _ hx => ⟨hKB hx.1,hx.2⟩
  have hTf : volume T ≠ ⊤ := ne_top_of_le_ne_top
    (isCompact_closedBall (0:Space n) (1/16:ℝ)).measure_lt_top.ne (measure_mono fun _ hx => hx.1)
  have hLf : volume L ≠ ⊤ := ne_top_of_le_ne_top hTf (measure_mono hLT)
  have hreal := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hLf) habp
  change (volume (Metric.ball (0:Space n) (32:ℝ))).toReal ≤
    (ENNReal.ofReal D * volume L).toReal at hreal
  rw [ENNReal.toReal_mul,ENNReal.toReal_ofReal hD.le] at hreal
  have hmono := ENNReal.toReal_mono hTf (measure_mono hLT)
  change δ ≤ (volume T).toReal
  exact ((div_le_iff₀ hD).mpr (by nlinarith)).trans hmono

end NormalizedCriticalDensity


end
end AffineBernstein
end

end OAI
