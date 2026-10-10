import Mathlib
import OAI.Analysis.AffineBernstein.NormalizedCriticalDensity
import OAI.Analysis.AffineBernstein.VarianceSeparation
import OAI.Analysis.AffineBernstein.EllipticComparison

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
namespace AffineBernstein
noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal

section SupersolutionHighSet

/-- A small value of a nonnegative supersolution forces almost all of the
fixed inner ball below any prescribed positive threshold. The small value
is quantitative and uniform in the generated normalized graph. -/
theorem normalized_supersolution_high_set_small {n : ℕ} (hn : 1 ≤ n) {ρ R : ℝ}
    (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (hR : 1 ≤ R) {η β : ℝ} (hη : 0 < η) (hβ : 0 < β) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ v : Space n → ℝ, BalancedNormalized ρ R v →
      ∀ s : Space n → ℝ, ContDiff ℝ ∞ s → (∀ x, 0 ≤ s x) →
      (∀ x, inverseHessianTrace v s x ≤ 0) → ∀ a ∈ Metric.ball (0:Space n) (1/64:ℝ),
      s a ≤ ε → (volume {x | x ∈ Metric.closedBall (0:Space n) (1/16:ℝ) ∧ η ≤ s x}).toReal < β := by
  obtain ⟨δ,hδ,Hδ⟩ := normalized_critical_density hn hρ hρ1 hR
  obtain ⟨V,hV,HV⟩ := normalized_log_variance hρ hρ1 hR (n := n)
  let T := V/(δ*β)+2
  have hdb : 0 < δ*β := mul_pos hδ hβ
  have hT : 2 ≤ T := by have H := div_nonneg hV hdb.le; dsimp [T]; linarith
  have hDT : δ*β*T=V+2*δ*β := by dsimp [T]; field_simp
  have hbig : V < δ*β*T^2 := by
    have hsq : T ≤ T^2 := by nlinarith
    have H := mul_le_mul_of_nonneg_left hsq hdb.le
    nlinarith
  let ε := η/(4*Real.exp T)
  have hε : 0 < ε := by dsimp [ε]; positivity
  refine ⟨ε,hε,?_⟩
  intro v hv s hs hspos hLs a ha hsa
  let r := fun x => s x+ε
  have hr : ContDiff ℝ ∞ r := hs.add contDiff_const
  have hrpos (x : Space n) : 0 < r x := by dsimp [r]; linarith [hspos x]
  have hLr (x : Space n) : inverseHessianTrace v r x ≤ 0 := by
    simpa only [r,inverseHessianTrace_add_constant] using hLs x
  let K := Metric.closedBall (0:Space n) (1/16:ℝ)
  let A := {x | x ∈ K ∧ r x ≤ 4*ε}
  let B := {x | x ∈ K ∧ η ≤ s x}
  have hK : IsCompact K := isCompact_closedBall _ _
  have hA : IsCompact A := compact_sublevel_in_compact hK hr.continuous (4*ε)
  have hB : IsCompact B := hK.inter_right (isClosed_le continuous_const hs.continuous)
  have hAl : δ ≤ (volume A).toReal := by
    have H := Hδ v hv r hr (fun x => (hrpos x).le) hLr a ha (2*ε) (by positivity)
      (by dsimp [r]; linarith)
    simpa only [show 2*(2*ε)=4*ε by ring] using H
  have hlogeq : Real.log η-Real.log (4*ε)=T := by
    rw [← Real.log_div hη.ne' (by positivity : 4*ε≠0)]
    have he : η/(4*ε)=Real.exp T := by dsimp [ε]; field_simp
    rw [he,Real.log_exp]
  have hsep : ∀ x ∈ A, ∀ y ∈ B, T ≤ Real.log (r y)-Real.log (r x) := by
    intro x hx y hy
    have hylo : η ≤ r y := by dsimp [r]; linarith [hy.2]
    have hxl := Real.log_le_log (hrpos x) hx.2
    have hyl := Real.log_le_log hη hylo
    linarith
  have hlow := variance_lower_of_separated_sets hK hA hB
    (fun x hx => hx.1) (fun x hx => hx.1) (hr.log (fun x => (hrpos x).ne')).continuous
    (by linarith : 0 ≤ T) hsep
  have hupper := HV v hv r hr hrpos hLr
  change (volume B).toReal < β
  by_contra h
  have hBl : β ≤ (volume B).toReal := le_of_not_gt h
  have hprod : δ*β ≤ (volume A).toReal*(volume B).toReal :=
    mul_le_mul hAl hBl hβ.le ENNReal.toReal_nonneg
  have H := mul_le_mul_of_nonneg_right hprod (sq_nonneg T)
  exact (not_lt_of_ge (H.trans (hlow.trans hupper))) hbig

end SupersolutionHighSet


end
end AffineBernstein
end

end OAI
