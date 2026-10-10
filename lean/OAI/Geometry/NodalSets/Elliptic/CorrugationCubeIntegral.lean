import Mathlib.MeasureTheory.Integral.Bochner.Set
import OAI.Geometry.NodalSets.Elliptic.CorrugationCubeMeasure

namespace OAI

namespace Yau.Geometry
open Yau.Jets Set Metric MeasureTheory Filter
noncomputable section

lemma coordinate_ball_ae_closed (y : Coord) {r : ℝ} (hr : 0 < r) :
    ball y r =ᵐ[volume] closedBall y r := by
  apply ae_eq_of_subset_of_measure_ge ball_subset_closedBall
  · rw [Real.volume_pi_ball y hr,Real.volume_pi_closedBall y hr.le]
  · exact measurableSet_ball.nullMeasurableSet
  · exact (isCompact_closedBall y r).measure_ne_top

lemma corrugation_cube_integral_sum (o : Coord) {L : ℝ} (hL : 0 < L)
    {n : ℕ} (hn : 0 < n) (f : Coord → ℝ)
    (hf : IntegrableOn f (Icc o (fun i ↦ o i+L))) :
    ∫ x in Icc o (fun i ↦ o i+L), f x =
      ∑ i : Fin 4 → Fin n, ∫ x in closedBall (corrugationCubeCenter o L n i) ((L/(n:ℝ))/2), f x := by
  let O := fun i : Fin 4 → Fin n ↦ ball (corrugationCubeCenter o L n i) ((L/(n:ℝ))/2)
  let Q := fun i : Fin 4 → Fin n ↦ closedBall (corrugationCubeCenter o L n i) ((L/(n:ℝ))/2)
  have hnR : (0:ℝ) < n := by exact_mod_cast hn
  have hR : 0 < (L/(n:ℝ))/2 := by positivity
  have heq : ∀ i, O i =ᵐ[volume] Q i := fun i ↦ coordinate_ball_ae_closed _ hR
  have hcover : (⋃ i, Q i) = Icc o (fun i ↦ o i+L) := by
    apply Set.Subset.antisymm
    · exact Set.iUnion_subset (fun i ↦ corrugationCube_closed_inside o hL hn i)
    · intro x hx
      obtain ⟨i,hi⟩ := corrugationCube_closed_cover o hL hn x hx
      exact Set.mem_iUnion.mpr ⟨i,hi⟩
  have hU : (⋃ i, O i) =ᵐ[volume] Icc o (fun i ↦ o i+L) := by
    rw [← hcover]
    exact Filter.EventuallyEqSet.iUnion heq
  have hsum := integral_iUnion_fintype (fun i ↦ measurableSet_ball (x := corrugationCubeCenter o L n i))
    (fun i j hij ↦ corrugationCube_balls_disjoint o hL hn i j hij)
    (fun i ↦ hf.mono_set (ball_subset_closedBall.trans (corrugationCube_closed_inside o hL hn i)))
  calc
    _ = ∫ x in ⋃ i, O i, f x := (setIntegral_congr_set hU).symm
    _ = ∑ i, ∫ x in O i, f x := hsum
    _ = _ := Finset.sum_congr rfl (fun i _ ↦ setIntegral_congr_set (heq i))

end
end Yau.Geometry

end OAI
