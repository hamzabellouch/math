import Mathlib
import OAI.Analysis.CoulombIonization.FieldAnalysis.RetainedSmear

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory Filter Set Metric
open scoped BigOperators ENNReal

namespace CoulombNeumann
open CoulombAtom CoulombAnalysis

lemma varthetaScaled_memLp {b : ℝ} (hb : 0 < b) : MemLp (varthetaScaled b) (5/3) := by
  apply bounded_compact_memLp (varthetaScaled_measurable b) (isCompact_closedBall (0:Space) (Real.sqrt 3*b))
  · intro x hx
    simpa only [mem_closedBall,dist_zero_right] using varthetaScaled_support_bound hb x hx
  · intro x
    rw [abs_of_nonneg (varthetaScaled_nonneg hb x)]
    exact varthetaScaled_le hb x

lemma varthetaScaled_potential_le {b : ℝ} (hb : 0 < b) {x : Space} (hx : x ≠ 0) :
    tfPotential (varthetaScaled b) x ≤ 1/‖x‖ := by
  have hh := radial_potential_le_point (varthetaScaled_integrable hb) (varthetaScaled_memLp hb)
    (varthetaScaled_nonneg hb) (fun _ _ h => varthetaScaled_radial b h)
    (by positivity : 0 ≤ Real.sqrt 3*b) (varthetaScaled_support_bound hb) hx
  simpa only [integral_varthetaScaled hb] using hh

lemma varthetaScaled_potential_eq_far {b : ℝ} (hb : 0 < b) {x : Space}
    (hx : Real.sqrt 3*b ≤ ‖x‖) : tfPotential (varthetaScaled b) x = 1/‖x‖ := by
  have hh := tfPotential_newton_exterior_closed (varthetaScaled_integrable hb)
    (varthetaScaled_memLp hb) (fun _ _ h => varthetaScaled_radial b h)
    (by positivity : 0 < Real.sqrt 3*b) (varthetaScaled_support_bound hb) hx
  simpa only [integral_varthetaScaled hb] using hh

lemma retainedSmear_potential {N : ℕ} {b : ℝ} (hb : 0 < b) (S : Finset (Fin N))
    (x : Configuration N) (y : Space) :
    tfPotential (retainedSmear b S x) y = ∑ i ∈ S, tfPotential (varthetaScaled b) (y-x i) := by
  simp only [tfPotential,retainedSmear,Finset.sum_div]
  rw [integral_finsetSum _ (fun i _ => translated_pole_integrable
    (varthetaScaled_integrable hb) (varthetaScaled_memLp hb) y (x i))]
  exact Finset.sum_congr rfl (fun i _ => integral_translated_pole (varthetaScaled b) y (x i))

theorem retainedSmear_potential_loss {N : ℕ} {b : ℝ} (hb : 0 < b) (S : Finset (Fin N))
    (x : Configuration N) (y : Space) (hxy : ∀ i ∈ S, x i ≠ y) :
    0 ≤ (∑ i ∈ S, 1/‖y-x i‖)-tfPotential (retainedSmear b S x) y ∧
      (∑ i ∈ S, 1/‖y-x i‖)-tfPotential (retainedSmear b S x) y ≤
        ∑ i ∈ S, (ball y (Real.sqrt 3*b)).indicator (fun z => 1/‖y-z‖) (x i) := by
  rw [retainedSmear_potential hb,←Finset.sum_sub_distrib]
  have hh (i : Fin N) (hi : i ∈ S) :
      0 ≤ 1/‖y-x i‖-tfPotential (varthetaScaled b) (y-x i) ∧
      1/‖y-x i‖-tfPotential (varthetaScaled b) (y-x i) ≤
        (ball y (Real.sqrt 3*b)).indicator (fun z => 1/‖y-z‖) (x i) := by
    have hn := tfPotential_nonneg (ae_of_all _ (varthetaScaled_nonneg hb)) (y-x i)
    have hle := varthetaScaled_potential_le hb (sub_ne_zero.mpr (hxy i hi).symm)
    refine ⟨sub_nonneg.mpr hle,?_⟩
    by_cases hB : x i ∈ ball y (Real.sqrt 3*b)
    · rw [indicator_of_mem hB]
      exact sub_le_self _ hn
    · rw [indicator_of_notMem hB,varthetaScaled_potential_eq_far hb (by
        simpa only [mem_ball,dist_eq_norm,norm_sub_rev,not_lt] using hB)]
      simp only [sub_self,le_refl]
  exact ⟨Finset.sum_nonneg (fun i hi => (hh i hi).1),
    Finset.sum_le_sum (fun i hi => (hh i hi).2)⟩

end CoulombNeumann

end

end OAI
