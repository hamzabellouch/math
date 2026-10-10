import Mathlib
import OAI.Analysis.Conductivity.Variational.PhysicalEndLocalLipschitz
import OAI.Analysis.Conductivity.Geometry.PhysicalCollarBand

namespace OAI

noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology

lemma sourceDirections_ne_zero_on_band {y : Fin 3 → ℝ}
    (hy : y∈sourceClosedCollarBand (-(1:ℝ)/100) (1/100)) :
    ∀ i,sourceComplexDirections y i≠0 := by
  intro i he
  have hr := congrArg Complex.re he
  have hi := congrArg Complex.im he
  fin_cases i
  · simp [sourceComplexDirections] at hr hi
    have hy0 : y 0=0 := hr.resolve_right (by norm_num [sourceLength])
    have hh := sourceRadial_pos_of_time hy.1
    simp [sourceRadial,hy0,hi] at hh
  · simp [sourceComplexDirections] at hr hi
    have hh : sourceCollarTime y=1 := by
      simp [sourceCollarTime,sourceCrossCoordinates,hr,hi]
    have ht := hy.2
    rw [hh] at ht
    norm_num at ht

lemma sourceBand_euclidean_bound {y : Fin 3 → ℝ}
    (hy : y∈sourceClosedCollarBand (-(1:ℝ)/100) (1/100)) :
    ‖WithLp.toLp 2 y‖≤(5:ℝ)/2 := by
  have hm : max |(sourceRadial y-sourceRadialCenter)/sourceRadialWidth| |y 2|≤101/100 := by
    have ht := hy.1
    change -(1:ℝ)/100≤1-max |(sourceRadial y-sourceRadialCenter)/sourceRadialWidth| |y 2| at ht
    linarith
  have hrad : sourceRadial y≤101/100 := by
    have hh := (le_abs_self ((sourceRadial y-sourceRadialCenter)/sourceRadialWidth)).trans
      ((le_max_left _ _).trans hm)
    norm_num [sourceRadialCenter,sourceRadialWidth,sourceHole,div_eq_mul_inv] at hh
    linarith
  have h0 : |y 0|≤17/10 := by
    have hh := (le_max_left (|y 0|/sourceLength) |y 1|).trans hrad
    norm_num [sourceLength,div_eq_mul_inv] at hh
    linarith
  have h1 : |y 1|≤11/10 := by
    have hh := (le_max_right (|y 0|/sourceLength) |y 1|).trans hrad
    linarith
  have h2 : |y 2|≤11/10 := by
    have hh := (le_max_right _ _).trans hm
    linarith
  have h0' := pow_le_pow_left₀ (abs_nonneg _) h0 2
  have h1' := pow_le_pow_left₀ (abs_nonneg _) h1 2
  have h2' := pow_le_pow_left₀ (abs_nonneg _) h2 2
  have hn := EuclideanSpace.real_norm_sq_eq (WithLp.toLp 2 y : R3)
  simp [Fin.sum_univ_succ] at hn
  simp only [sq_abs] at h0' h1' h2'
  nlinarith [norm_nonneg (WithLp.toLp 2 y : R3)]

lemma LocalLipAt.sub {E : Type*} [PseudoMetricSpace E] {p q : E → ℝ} {x : E}
    (hp : LocalLipAt p x) (hq : LocalLipAt q x) : LocalLipAt (fun y => p y-q y) x := by
  obtain ⟨K,t,ht,hK⟩ := hp
  obtain ⟨L,u,hu,hL⟩ := hq
  exact ⟨K+L,t∩u,inter_mem ht hu,(hK.mono inter_subset_left).sub (hL.mono inter_subset_right)⟩

end ScalarConductivity

end

end OAI
