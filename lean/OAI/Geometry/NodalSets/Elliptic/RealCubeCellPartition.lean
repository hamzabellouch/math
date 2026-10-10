import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import OAI.Geometry.NodalSets.Elliptic.CorrugationCubePartition
import OAI.Geometry.NodalSets.Elliptic.RealScaledCubeIntegration

namespace OAI

namespace Yau.Geometry
open Yau.Jets MeasureTheory Set Function Metric
noncomputable section

def realCubeCell (n : ℕ) (k : Fin 4 → Fin n) : Set Yau.Jets.Coord :=
  realScaledCube 4 (corrugationCubeCenter (fun _ ↦ -1) 2 n k) (1/(n:ℝ))

lemma realCubeCell_closedBall {n : ℕ} (hn : 0 < n) (k : Fin 4 → Fin n) :
    realCubeCell n k = closedBall (corrugationCubeCenter (fun _ ↦ -1) 2 n k) ((2/(n:ℝ))/2) := by
  have hnR : (0:ℝ)<n := by exact_mod_cast hn
  rw [realCubeCell,realScaledCube_eq_closedBall 4 _ (div_pos zero_lt_one hnR)]
  congr 1
  ring

lemma realCubeCell_isCompact (n : ℕ) (k : Fin 4 → Fin n) : IsCompact (realCubeCell n k) :=
  realScaledCube_isCompact 4 _ _

lemma realCubeCell_subset {n : ℕ} (hn : 0 < n) (k : Fin 4 → Fin n) :
    realCubeCell n k ⊆ realFinCube 4 := by
  have hnR : (0:ℝ)<n := by exact_mod_cast hn
  rw [realCubeCell_closedBall hn k,← closure_ball _ (by positivity : (2/(n:ℝ))/2 ≠ 0)]
  have hb := (corrugationCube_ball_inside (fun _ ↦ -1) (by norm_num : (0:ℝ)<2) hn k).trans
    interior_subset
  have he : Icc (fun _ : Fin 4 ↦ (-1:ℝ)) (fun i ↦ (-1:ℝ)+2) = realFinCube 4 := by
    norm_num [realFinCube]
  rw [he] at hb
  exact closure_minimal hb (realFinCube_isCompact 4).isClosed

theorem realCubeCell_cover {n : ℕ} (hn : 0 < n) :
    (⋃ k : Fin 4 → Fin n, realCubeCell n k) = realFinCube 4 := by
  apply Subset.antisymm
  · exact iUnion_subset (realCubeCell_subset hn)
  · intro x hx
    have hx' : x ∈ Icc (fun _ : Fin 4 ↦ (-1:ℝ)) (fun i ↦ (-1:ℝ)+2) := by
      simpa [realFinCube,show (-1:ℝ)+2=1 by norm_num] using hx
    obtain ⟨k,hk⟩ := corrugationCube_closed_cover (fun _ ↦ -1) (by norm_num : (0:ℝ)<2) hn x hx'
    exact mem_iUnion.mpr ⟨k,by rwa [realCubeCell_closedBall hn k]⟩

lemma real_closedBall_ae_ball (c : Yau.Jets.Coord) (r : ℝ) :
    closedBall c r =ᵐ[volume] ball c r := by
  rw [ae_eq_set,closedBall_sdiff_ball,sdiff_eq_empty.mpr ball_subset_closedBall,measure_empty]
  exact ⟨Measure.addHaar_sphere volume c r,rfl⟩

lemma realCubeCell_pairwise_aedisjoint {n : ℕ} (hn : 0 < n) :
    Pairwise (AEDisjoint volume on (realCubeCell n)) := by
  intro k j hkj
  change AEDisjoint volume (realCubeCell n k) (realCubeCell n j)
  rw [realCubeCell_closedBall hn k,realCubeCell_closedBall hn j]
  exact (corrugationCube_balls_disjoint (fun _ ↦ -1) (by norm_num : (0:ℝ)<2) hn k j hkj).aedisjoint.congr
    (real_closedBall_ae_ball _ _) (real_closedBall_ae_ball _ _)

theorem realCubeCell_integral_sum {n : ℕ} (hn : 0 < n)
    (F : Yau.Jets.Coord → ℝ) (hF : IntegrableOn F (realFinCube 4)) :
    (∫ x in realFinCube 4, F x) = ∑ k : Fin 4 → Fin n, ∫ x in realCubeCell n k, F x := by
  have hi : IntegrableOn F (⋃ k : Fin 4 → Fin n, realCubeCell n k) := by
    rwa [realCubeCell_cover hn]
  have h := integral_iUnion_ae (fun k ↦ (realCubeCell_isCompact n k).measurableSet.nullMeasurableSet)
    (realCubeCell_pairwise_aedisjoint hn) hi
  simpa only [realCubeCell_cover hn,tsum_fintype] using h

lemma realCubeCell_mass {n : ℕ} (hn : 0 < n) (k : Fin 4 → Fin n) :
    (volume.restrict (realCubeCell n k)).real univ = (2/(n:ℝ))^4 := by
  have hnR : (0:ℝ)<n := by exact_mod_cast hn
  simpa only [realCubeCell,mul_one_div] using
    realScaledCube_mass 4 (corrugationCubeCenter (fun _ ↦ -1) 2 n k) (div_pos zero_lt_one hnR)

end
end Yau.Geometry

end OAI
