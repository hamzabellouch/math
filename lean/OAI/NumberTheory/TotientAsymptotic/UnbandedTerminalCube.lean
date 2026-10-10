import OAI.NumberTheory.TotientAsymptotic.UnbandedCube
import OAI.NumberTheory.TotientAsymptotic.PrefixTerminalVolume
import OAI.NumberTheory.TotientAsymptotic.SimplexTerminalCap

namespace OAI

/-! A terminal lower bound survives unit-box thickening with its exact cost. -/
noncomputable section
open scoped BigOperators
open MeasureTheory
namespace TotientAsymptotic

theorem unbanded_grid_terminal_volume_bound (N : ℕ)
    (B β₀ t : ℝ) (β κ : Fin (N+1) → ℝ) (K : Finset (Fin (N+1) → ℕ))
    (hβ₀ : 0 < β₀) (hβ : ∀ i,0 < β i) (ht : 0 ≤ t)
    (hκ : ∀ i,1 ≤ κ i) (htop : ∀ i,β₀ ≤ κ i)
    (hstep : ∀ i j,i < j → β i*κ i ≤ κ j)
    (hK : ∀ b ∈ K,∃ u ∈ unitGridCell b,
      u ∈ enlargedSimplex (N+1) B β₀ β ∧ t ≤ u (Fin.last N)) :
    (K.card:ℝ) ≤ (∏ i,κ i)*
      ((max (B+prefixCubeCost (N+1)-g (N+1)*(t/κ (Fin.last N))) 0)^(N+1)/
        (((N+1).factorial:ℝ)*∏ i : Fin (N+1),g (i.val+1))) := by
  let C : Fin (N+1) → ℝ := fun i => -((N+1-i.val:ℕ):ℝ)^2
  let S := prefixRegion (N+1) (B+(N+1:ℝ)^2) 0 C ∩
    {u | t/κ (Fin.last N)-1 ≤ u (Fin.last N)}
  have hκpos (i) : 0 < κ i := zero_lt_one.trans_le (hκ i)
  have hp : 0 < ∏ i,κ i := Finset.prod_pos (fun i _ => hκpos i)
  have hd : LinearMap.det (simplexScale κ)≠0 := by
    rw [simplexScale_det]
    exact inv_ne_zero hp.ne'
  have hsub : gridRegion K ⊆ simplexScale κ ⁻¹' S := by
    intro v hv
    obtain ⟨b,hv⟩ := Set.mem_iUnion.mp hv
    obtain ⟨hb,hvb⟩ := Set.mem_iUnion.mp hv
    obtain ⟨u,hub,hu,hterminal⟩ := hK b hb
    have hdist := simplexScale_unit_distance hκ (unitGridCell_coordinate_distance hub hvb)
    refine ⟨?_,?_⟩
    · simpa only [Nat.cast_add,Nat.cast_one,C] using prefixRegion_unit_cube
        (enlargedSimplex_mapsTo hβ₀ hβ hκpos htop hstep hu) hdist
    · have ht' := div_le_div_of_nonneg_right hterminal (hκpos (Fin.last N)).le
      have hd' := (abs_le.mp (hdist (Fin.last N))).2
      rw [simplexScale_apply] at hd'
      change t/κ (Fin.last N)-1 ≤ simplexScale κ v (Fin.last N)
      linarith only [ht',hd']
  have hS : MeasurableSet S :=
    (measurableSet_prefixRegion _ _ _ _).inter
      (measurableSet_le measurable_const (measurable_pi_apply _))
  have hvol : volume (gridRegion K) ≤ ENNReal.ofReal (∏ i,κ i)*volume S := by
    apply (measure_mono hsub).trans_eq
    rw [← Measure.map_apply (simplexScale κ).continuous_of_finiteDimensional.measurable hS,
      Real.map_linearMap_volume_pi_eq_smul_volume_pi hd,simplexScale_det,
      inv_inv,abs_of_pos hp,Measure.smul_apply,smul_eq_mul]
  have hC : C (Fin.last N)= -1 := by simp [C]
  have hthreshold : C (Fin.last N) ≤ t/κ (Fin.last N)-1 := by
    rw [hC]
    have hh := div_nonneg ht (hκpos (Fin.last N)).le
    linarith only [hh]
  have hformula := volume_prefixRegion_terminal N (B+(N+1:ℝ)^2) 0 C hthreshold
  have hbudget : B+(N+1:ℝ)^2-0-(∑ i : Fin (N+1),g (i.val+1)*C i)-
      g (N+1)*(t/κ (Fin.last N)-1-C (Fin.last N))=
      B+prefixCubeCost (N+1)-g (N+1)*(t/κ (Fin.last N)) := by
    rw [hC]
    simp only [C,prefixCubeCost,mul_neg,Finset.sum_neg_distrib,Nat.cast_add,Nat.cast_one]
    ring
  rw [hbudget] at hformula
  change volume (gridRegion K) ≤ ENNReal.ofReal (∏ i,κ i)*
    volume (prefixRegion (N+1) (B+(N+1:ℝ)^2) 0 C ∩
      {u | t/κ (Fin.last N)-1 ≤ u (Fin.last N)}) at hvol
  rw [hformula,← ENNReal.ofReal_mul hp.le] at hvol
  have hh := ENNReal.toReal_mono ENNReal.ofReal_ne_top hvol
  have hden : 0 ≤ (((N+1).factorial:ℝ)*∏ i : Fin (N+1),g (i.val+1)) :=
    mul_nonneg (Nat.cast_nonneg _) (Finset.prod_nonneg (fun i _ => (g_pos _).le))
  have hnresult : 0 ≤ (∏ i,κ i)*
      ((max (B+prefixCubeCost (N+1)-g (N+1)*(t/κ (Fin.last N))) 0)^(N+1)/
        (((N+1).factorial:ℝ)*∏ i : Fin (N+1),g (i.val+1))) :=
    mul_nonneg hp.le (div_nonneg (pow_nonneg (le_max_right _ _) _) hden)
  simpa only [gridRegion_volume_real,ENNReal.toReal_ofReal hnresult] using hh

theorem unbanded_grid_terminal_exponential (N : ℕ)
    (B β₀ t : ℝ) (β κ : Fin (N+1) → ℝ) (K : Finset (Fin (N+1) → ℕ))
    (hB : 0 < B) (hβ₀ : 0 < β₀) (hβ : ∀ i,0 < β i) (ht : 0 ≤ t)
    (hκ : ∀ i,1 ≤ κ i) (htop : ∀ i,β₀ ≤ κ i)
    (hstep : ∀ i j,i < j → β i*κ i ≤ κ j)
    (hK : ∀ b ∈ K,∃ u ∈ unitGridCell b,
      u ∈ enlargedSimplex (N+1) B β₀ β ∧ t ≤ u (Fin.last N)) :
    (K.card:ℝ) ≤ (∏ i,κ i)*
      (Real.exp (-((N+1:ℕ):ℝ)*(g (N+1)*(t/κ (Fin.last N)))/
          (B+prefixCubeCost (N+1)))*
        (B+prefixCubeCost (N+1))^(N+1)/
          (((N+1).factorial:ℝ)*∏ i : Fin (N+1),g (i.val+1))) := by
  apply (unbanded_grid_terminal_volume_bound N B β₀ t β κ K hβ₀ hβ ht hκ htop hstep hK).trans
  apply mul_le_mul_of_nonneg_left _ (Finset.prod_nonneg (fun i _ => (hκ i).trans' zero_le_one))
  apply div_le_div_of_nonneg_right _
    (mul_nonneg (Nat.cast_nonneg _) (Finset.prod_nonneg (fun i _ => (g_pos _).le)))
  exact simplex_positive_part_power_bound
    (add_pos_of_pos_of_nonneg hB (prefixCubeCost_nonneg _))
    (mul_nonneg (g_pos _).le (div_nonneg ht (zero_le_one.trans (hκ _)))) (by omega)

end TotientAsymptotic

end

end OAI
