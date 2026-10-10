import OAI.NumberTheory.TotientAsymptotic.UnbandedCube
import OAI.NumberTheory.TotientAsymptotic.PrefixConcentration

namespace OAI

/-! The affine correction for the unit boxes in a coordinate-deviation count. -/
noncomputable section
open scoped BigOperators
open MeasureTheory
namespace TotientAsymptotic

def coordinateCubeShift (N : ℕ) : Fin N → ℝ :=
  ((prefixLinear N).equivOfDetNeZero (by rw [prefixLinear_det]; norm_num)).symm
    (fun i => ((N-i.val:ℕ):ℝ)^2)

lemma coordinateCubeShift_slack (N : ℕ) (i : Fin N) :
    prefixLinear N (coordinateCubeShift N) i = ((N-i.val:ℕ):ℝ)^2 := by
  have hh := ((prefixLinear N).equivOfDetNeZero
    (by rw [prefixLinear_det]; norm_num)).apply_symm_apply
      (fun i : Fin N => ((N-i.val:ℕ):ℝ)^2)
  exact congrFun hh i

lemma coordinateCubeShift_coordinate (N : ℕ) (i : Fin N) :
    coordinateCubeShift N i = ∑ j : Fin N,
      if i ≤ j then g (j.val-i.val)*((N-j.val:ℕ):ℝ)^2 else 0 := by
  rw [prefixLinear_coordinate N (coordinateCubeShift N) i]
  simp only [coordinateCubeShift_slack]

lemma coordinateCubeShift_nonneg (N : ℕ) (i : Fin N) :
    0 ≤ coordinateCubeShift N i := by
  rw [coordinateCubeShift_coordinate]
  apply Finset.sum_nonneg
  intro j _
  split_ifs
  · exact mul_nonneg (g_pos _).le (sq_nonneg _)
  · exact le_rfl

lemma coordinateCubeShift_budget (N : ℕ) :
    ∑ i : Fin N,a (i.val+1)*coordinateCubeShift N i =
      ∑ i : Fin N,g (i.val+1)*((N-i.val:ℕ):ℝ)^2 := by
  rw [←weighted_prefixLinear]
  simp only [coordinateCubeShift_slack]

lemma coordinateCubeShift_mem {N : ℕ} {B : ℝ} {u : Fin N → ℝ}
    (hu : u ∈ prefixRegion N (B+(N:ℝ)^2) 0
      (fun i => -((N-i.val:ℕ):ℝ)^2)) :
    u+coordinateCubeShift N ∈ prefixRegion N (B+prefixCubeCost N) 0 0 := by
  refine ⟨fun i => ?_,?_⟩
  · rw [map_add,Pi.add_apply,coordinateCubeShift_slack]
    have hh := hu.1 i
    change -((N-i.val:ℕ):ℝ)^2 ≤ prefixLinear N u i at hh
    change 0 ≤ prefixLinear N u i+((N-i.val:ℕ):ℝ)^2
    linarith only [hh]
  · simp only [Pi.add_apply,mul_add,Finset.sum_add_distrib,coordinateCubeShift_budget]
    have hh := hu.2
    simp only [sub_zero] at hh ⊢
    unfold prefixCubeCost
    linarith only [hh]

/-- A measurable coordinate event can be counted on the corrected simplex.
The pointwise premise will be supplied by the fixed-tolerance band arithmetic. -/
theorem coordinate_grid_volume_bound {N : ℕ} (hN : 0<N)
    (B β₀ : ℝ) (β κ : Fin N → ℝ) (K : Finset (Fin N → ℕ))
    (T : Set (Fin N → ℝ)) (hT : MeasurableSet T)
    (hβ₀ : 0<β₀) (hβ : ∀ i,0<β i) (hκ : ∀ i,1 ≤ κ i)
    (htop : ∀ i,β₀ ≤ κ i)
    (hstep : ∀ i j,i<j → β i*κ i ≤ κ j)
    (hK : ∀ b∈K,∃ u∈unitGridCell b,u∈enlargedSimplex N B β₀ β ∧
      ∀ v∈unitGridCell b,simplexScale κ v+coordinateCubeShift N∈T) :
    (K.card:ℝ) ≤ (∏ i,κ i)*
      (volume (prefixRegion N (B+prefixCubeCost N) 0 0 ∩ T)).toReal := by
  let S := prefixRegion N (B+prefixCubeCost N) 0 0 ∩ T
  have hκpos (i) : 0<κ i := zero_lt_one.trans_le (hκ i)
  have hp : 0<∏ i,κ i := Finset.prod_pos (fun i _ => hκpos i)
  have hd : LinearMap.det (simplexScale κ)≠0 := by
    rw [simplexScale_det]
    exact inv_ne_zero hp.ne'
  have hS : MeasurableSet S := (measurableSet_prefixRegion _ _ _ _).inter hT
  have hsub : gridRegion K ⊆ simplexScale κ ⁻¹'
      ((fun u => u+coordinateCubeShift N) ⁻¹' S) := by
    intro v hv
    obtain ⟨b,hv⟩ := Set.mem_iUnion.mp hv
    obtain ⟨hb,hvb⟩ := Set.mem_iUnion.mp hv
    obtain ⟨u,hub,hu,hevent⟩ := hK b hb
    refine ⟨?_,hevent v hvb⟩
    apply coordinateCubeShift_mem
    exact prefixRegion_unit_cube (enlargedSimplex_mapsTo hβ₀ hβ hκpos htop hstep hu)
      (simplexScale_unit_distance hκ (unitGridCell_coordinate_distance hub hvb))
  have hvol : volume (gridRegion K) ≤ ENNReal.ofReal (∏ i,κ i)*volume S := by
    apply (measure_mono hsub).trans_eq
    rw [←Measure.map_apply (simplexScale κ).continuous_of_finiteDimensional.measurable
      (hS.preimage (by fun_prop)),
      Real.map_linearMap_volume_pi_eq_smul_volume_pi hd,simplexScale_det,
      inv_inv,abs_of_pos hp,Measure.smul_apply,smul_eq_mul,
      measure_preimage_add_right]
  have hfin : volume S≠⊤ := ne_top_of_le_ne_top
    (prefixRegion_volume_ne_top hN _) (measure_mono Set.inter_subset_left)
  have hh := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hfin) hvol
  simpa only [gridRegion_volume_real,ENNReal.toReal_mul,ENNReal.toReal_ofReal hp.le] using hh

end TotientAsymptotic

end

end OAI
