import OAI.Probability.RadialTransition.IdealSupports

namespace OAI

noncomputable section
open scoped BigOperators ENNReal NNReal
open MeasureTheory Set Filter
namespace RadialTransition

def phaseSlope (i : Fin 3) : Parameter := parameter (phaseMass/2*(phaseDensity i)^2) (phaseDensity i)
def phaseCenter : Parameter := parameter 1 (-3/4)
def targetSlope : Parameter := parameter (17*packingDensity/4) (5*packingDensity/3)
def phaseWindow (r : ℝ) : Set Parameter := Metric.closedBall phaseCenter r

def HasPhaseGroups (Q : Pressure) (x : Parameter) (r : ℝ) : Prop :=
  supportSet (onParameters Q) positiveParameters x = closure (convexHull ℝ
    {v : Parameter | v ∈ supportSet (onParameters Q) positiveParameters x ∧
      ∃ i : Fin 3, v ∈ Metric.closedBall (phaseSlope i) r})

lemma support_energy_small {Q : Pressure} {β h e d σ ε : ℝ}
    (hσ : 0 < σ) (hβ : σ < β) (hs : pressureSupport Q β h e d)
    (happ : ∀ s ∈ ({-σ,0,σ} : Set ℝ), |Q (β+s) h-bareLimit h| ≤ ε) :
    |e| ≤ 2*ε/σ := by
  have hm := hs (β-σ) h (by linarith)
  have hp := hs (β+σ) h (by linarith)
  have ha0 := abs_le.mp (happ 0 (by simp))
  have ham := abs_le.mp (happ (-σ) (by simp))
  have hap := abs_le.mp (happ σ (by simp))
  simp only [sub_self, mul_zero, add_zero, sub_eq_add_neg] at hm hp ha0 ham hap
  have heq := div_mul_cancel₀ (2*ε) hσ.ne'
  rw [abs_le]
  constructor <;> nlinarith

lemma phase_generator_distance {Q : Pressure} {β h U ε η σ u e : ℝ}
    (hβ : 0 < β) (hσ : 0 < σ) (hβσ : σ < β) (hη : 0 ≤ η)
    (hU : 4*packingDensity ≤ U) (hu : ActiveShift Q phaseMass β h u) (hub : u ∈ Icc (0:ℝ) U)
    (happ : ∀ v ∈ Icc (0:ℝ) U, |Q β (h+β*phaseMass*v)-bareLimit (h+β*phaseMass*v)| ≤ ε)
    (happe : ∀ s ∈ ({-σ,0,σ} : Set ℝ), |Q (β+s) (h+β*phaseMass*u)-bareLimit (h+β*phaseMass*u)| ≤ ε)
    (hsmall : 2*ε ≤ β*phaseMass/2*η^2)
    (hs : pressureSupport Q β (h+β*phaseMass*u) e u) :
    ∃ i : Fin 3, ‖parameter (e+phaseMass*u^2/2) u-phaseSlope i‖ ≤
      2*ε/σ+(1+phaseMass/2*(U+4*packingDensity))*η := by
  have he := support_energy_small hσ hβσ hs happe
  obtain ⟨i, hi⟩ := active_near_phase hβ.le hU hu hub happ
  have hc : 0 < β*phaseMass/2 := by have := phaseMass_pos; positivity
  have hdist : |u-phaseDensity i| ≤ η := by
    have hsq : (u-phaseDensity i)^2 ≤ η^2 := by nlinarith
    exact (sq_le_sq₀ (abs_nonneg _) hη).mp (by simpa only [sq_abs] using hsq)
  have hsum : |u+phaseDensity i| ≤ U+4*packingDensity := by
    rw [abs_of_nonneg (add_nonneg hub.1 (phaseDensity_bounds i).1)]
    linarith [hub.2, (phaseDensity_bounds i).2]
  have hdiff : |u^2-(phaseDensity i)^2| ≤ η*(U+4*packingDensity) := by
    rw [show u^2-(phaseDensity i)^2=(u-phaseDensity i)*(u+phaseDensity i) by ring, abs_mul]
    exact mul_le_mul hdist hsum (abs_nonneg _) hη
  have hA := phaseMass_pos
  have hshift : |e+phaseMass*u^2/2-phaseMass/2*(phaseDensity i)^2| ≤
      2*ε/σ+phaseMass/2*η*(U+4*packingDensity) := by
    calc
      _ = |e+phaseMass/2*(u^2-(phaseDensity i)^2)| := by congr 1; ring
      _ ≤ |e|+|phaseMass/2*(u^2-(phaseDensity i)^2)| := abs_add_le _ _
      _ = |e|+(phaseMass/2)*|u^2-(phaseDensity i)^2| := by rw [abs_mul, abs_of_pos (by positivity : 0 < phaseMass/2)]
      _ ≤ _ := by nlinarith [mul_le_mul_of_nonneg_left hdiff (by positivity : 0 ≤ phaseMass/2)]
  refine ⟨i, ?_⟩
  have hn := parameter_norm_le (parameter (e+phaseMass*u^2/2) u-phaseSlope i)
  change ‖parameter (e+phaseMass*u^2/2) u-phaseSlope i‖ ≤
    |e+phaseMass*u^2/2-phaseMass/2*(phaseDensity i)^2|+|u-phaseDensity i| at hn
  nlinarith

lemma phase_groups_of_generators {Q : Pressure} {x : Parameter} {G : Set Parameter} {r : ℝ}
    (hgen : supportSet (onParameters Q) positiveParameters x=closure (convexHull ℝ G))
    (hG : ∀ v ∈ G, ∃ i : Fin 3, v ∈ Metric.closedBall (phaseSlope i) r) :
    HasPhaseGroups Q x r := by
  apply le_antisymm
  · rw [hgen]
    apply closure_mono
    apply convexHull_mono
    intro v hv
    refine ⟨?_, hG v hv⟩
    exact subset_closure (subset_convexHull ℝ G hv)
  · apply closure_minimal _ (isClosed_supportSet _ _ _)
    exact convexHull_min (fun _ h => h.1) (convex_supportSet _ _ _)

end RadialTransition
end

end OAI
