import Mathlib
import OAI.Probability.SKBarriers.Coverage.PressureGapProbability
import OAI.Probability.SKBarriers.Coverage.FiniteRateAsymptotic

namespace OAI

section

section
noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic

def restrictedPressure {n d : ℕ} (β : ℝ) (S : Finset (ReplicaConfig n d)) : ℝ :=
  (∫ J, restrictedLogPartition β S J ∂disorderLaw n)/(n:ℝ)

theorem replicaGibbsMass_integral_le_of_finiteInf_gap {n d : ℕ} (hn : 0 < n) (hd : 0 < d)
    {β η e : ℝ} (hβ : β ≠ 0) (hη : 0 ≤ η)
    {S : Finset (ReplicaConfig n d)} (hS : S.Nonempty)
    (hlower : finiteParisiInf β-e ≤ quenchedPressure β n)
    (herror : 2*(d:ℝ)*e ≤ η)
    (hpressure : restrictedPressure β S ≤ (d:ℝ)*finiteParisiInf β-η) :
    (∫ J, replicaGibbsMass β J S ∂disorderLaw n) ≤
      Real.exp (-(n:ℝ)*η/4)+2*Real.exp (-(n:ℝ)*η^2/(16*Real.pi^2*β^2*(d:ℝ)^2)) := by
  apply replicaGibbsMass_integral_le_of_mean_gap hn hd hβ hη hS
  have hn0 : 0 < (n:ℝ) := by exact_mod_cast hn
  have hd0 : 0 ≤ (d:ℝ) := by positivity
  have H := mul_le_mul_of_nonneg_left hlower hd0
  have HP : restrictedPressure β S-(d:ℝ)*quenchedPressure β n ≤ -η/2 := by linarith
  unfold restrictedPressure quenchedPressure at HP
  have HN := mul_le_mul_of_nonneg_right HP hn0.le
  have he : ((∫ J, restrictedLogPartition β S J ∂disorderLaw n)/(n:ℝ)-
      (d:ℝ)*((∫ J, logPartition β J ∂disorderLaw n)/(n:ℝ)))*(n:ℝ) =
      (∫ J, restrictedLogPartition β S J ∂disorderLaw n)-
      (d:ℝ)*(∫ J, logPartition β J ∂disorderLaw n) := by field_simp [ne_of_gt hn0]
  rw [he] at HN
  linarith

theorem eventual_replicaGibbsMass_pressure_gap {β : ℝ} (hβ : 0 < β) (d : ℕ) (hd : 0 < d) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ n : ℕ in atTop, ∀ (S : Finset (ReplicaConfig n d)) (η : ℝ),
      S.Nonempty → 0 ≤ η → 2*(d:ℝ)*C*(n:ℝ)^(-(1:ℝ)/24) ≤ η →
      restrictedPressure β S ≤ (d:ℝ)*finiteParisiInf β-η →
      (∫ J, replicaGibbsMass β J S ∂disorderLaw n) ≤
        Real.exp (-(n:ℝ)*η/4)+2*Real.exp (-(n:ℝ)*η^2/(16*Real.pi^2*β^2*(d:ℝ)^2)) := by
  obtain ⟨C,hC,HC⟩ := quenchedPressure_quantitative_finiteInf hβ
  refine ⟨C,hC,?_⟩
  filter_upwards [HC,eventually_gt_atTop (0:ℕ)] with n hn hn0
  intro S η hS hη herr hpress
  apply replicaGibbsMass_integral_le_of_finiteInf_gap hn0 hd hβ.ne' hη hS hn.1 _ hpress
  simpa only [mul_assoc] using herr

end SK.Analytic

end
end

end

end OAI
