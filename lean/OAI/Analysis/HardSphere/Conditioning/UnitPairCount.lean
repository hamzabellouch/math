import Mathlib
import OAI.Analysis.HardSphere.Geometry.UnitCenter

namespace OAI

noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology BigOperators
open scoped BigOperators ComplexConjugate
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
open MeasureTheory ProbabilityTheory Real Complex
open scoped ENNReal ComplexConjugate
open ProbabilityTheory
open MeasureTheory Filter Set
open scoped ENNReal Topology
open MeasureTheory Set
open scoped ENNReal
namespace HardSphere
open MeasureTheory Set Filter SphericalCoordinates
open scoped ENNReal

def unitPairCount {n K : ℕ} {L : Length} (hL : L.val=(K:ℝ))
    (p : Fin n → Prop) [DecidablePred p] (v : CubeCell K) (X : Configuration n L) : ℝ :=
  (unitOccupation hL p v X:ℝ)*((unitOccupation hL p v X:ℝ)-1)

lemma unitPairCount_nonneg {n K : ℕ} {L : Length} (hL : L.val=(K:ℝ))
    (p : Fin n → Prop) [DecidablePred p] (v : CubeCell K) (X : Configuration n L) :
    0≤unitPairCount hL p v X := by
  unfold unitPairCount
  by_cases h : unitOccupation hL p v X=0
  · simp only [h,Nat.cast_zero,zero_mul,le_refl]
  · have hp : (1:ℝ)≤unitOccupation hL p v X := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr h
    exact mul_nonneg (Nat.cast_nonneg _) (sub_nonneg.mpr hp)

lemma unitPairCount_measurable {n K : ℕ} {L : Length} (hL : L.val=(K:ℝ))
    (p : Fin n → Prop) [DecidablePred p] (v : CubeCell K) : Measurable (unitPairCount hL p v) := by
  have hm : Measurable (fun X : Configuration n L ↦ fun i ↦ unitSite hL (X i)) :=
    Measurable.of_eval (fun i ↦ (measurable_unitSite hL).comp (measurable_pi_apply i))
  let W : (Fin n → CubeCell K) → ℝ := fun σ ↦
    (Fintype.card {i : {i // p i} // σ i.val=v}:ℝ)*((Fintype.card {i : {i // p i} // σ i.val=v}:ℝ)-1)
  have hW : Measurable W := measurable_of_finite W
  change Measurable (W ∘ fun X : Configuration n L ↦ fun i ↦ unitSite hL (X i))
  exact hW.comp hm

lemma spatialPartition_cell_weight {n K : ℕ} {L : Length} (hL : L.val=(K:ℝ))
    (A : Finset (Torus L)) (H : ℝ) (X : Configuration n L) :
    (∑ v : CubeCell K, if spatialSiteDistance L A (unitCenter L v)+1≤H then
      unitPairCount hL (fun _ ↦ True) v X else 0)≤
    ∑ σ : Fin n → Bool, (∑ v : CubeCell K, unitPairCount hL (fun i ↦ σ i=true) v X)*
      ‖(productPartition n L (spatialInside L A H) (spatialOutside L A H) σ).toFun X‖^2 := by
  classical
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_le_sum
  intro v _
  by_cases hv : spatialSiteDistance L A (unitCenter L v)+1≤H
  · rw [ite_eq_left hv]
    apply le_of_eq
    have hp := productPartition_norm_unity (spatialInside L A H) (spatialOutside L A H)
      (spatialInside_real L A H) (spatialOutside_real L A H) (spatialPartition_unity L A H) X
    calc
      _ = unitPairCount hL (fun _ ↦ True) v X*
          (∑ σ : Fin n → Bool, ‖(productPartition n L (spatialInside L A H) (spatialOutside L A H) σ).toFun X‖^2) := by rw [hp,mul_one]
      _ = ∑ σ : Fin n → Bool, unitPairCount hL (fun _ ↦ True) v X*
          ‖(productPartition n L (spatialInside L A H) (spatialOutside L A H) σ).toFun X‖^2 := Finset.mul_sum ..
      _ = _ := by
        apply Finset.sum_congr rfl
        intro σ _
        by_cases hz : (productPartition n L (spatialInside L A H) (spatialOutside L A H) σ).toFun X=0
        · simp only [hz,norm_zero,zero_pow (by norm_num : 2≠0),mul_zero]
        · unfold unitPairCount
          rw [spatialPartition_cell_occupation hL A H σ X hz v hv]
  · rw [ite_eq_right hv]
    exact Finset.sum_nonneg (fun σ _ ↦ mul_nonneg (unitPairCount_nonneg hL _ v X) (sq_nonneg _))

lemma spatialPartition_cell_integral {n K : ℕ} {L : Length} (hL : L.val=(K:ℝ))
    (A : Finset (Torus L)) (H : ℝ) {r : ℝ} (hr : 0<r) (u : Jet n L)
    (hu : u∈dirichletDomain n L r) :
    (∑ v : CubeCell K, (Ici (spatialSiteDistance L A (unitCenter L v)+1)).indicator
      (fun _ : ℝ ↦ ENNReal.ofReal (1/(64*Real.sqrt 3)*r)*
        (∫⁻ X, ENNReal.ofReal (unitPairCount hL (fun _ ↦ True) v X)*ENNReal.ofReal (‖u.1 X‖^2))) H)≤
      ENNReal.ofReal (spatialPartitionEnergy L A H u) := by
  classical
  let w := fun σ : Fin n → Bool ↦ productPartition n L (spatialInside L A H) (spatialOutside L A H) σ
  let c : ℝ := 1/(64*Real.sqrt 3)*r
  have hc : 0≤c := by dsimp [c]; positivity
  let q := fun (p : Fin n → Prop) [DecidablePred p] (v : CubeCell K) (X : Configuration n L) ↦ unitPairCount hL p v X
  have hcoe : ∀ᵐ X ∂volume, ∀ σ, (w σ).onScalar u.1 X=(w σ).toFun X*u.1 X :=
    ae_all_iff.mpr (fun σ ↦ (w σ).coe_onScalar u.1)
  have hm (σ : Fin n → Bool) : Measurable (fun X : Configuration n L ↦
      ENNReal.ofReal (c*∑ v : CubeCell K, q (fun i ↦ σ i=true) v X)*ENNReal.ofReal (‖(w σ).onScalar u.1 X‖^2)) :=
    ((Finset.measurable_sum _ (fun v _ ↦ unitPairCount_measurable hL _ v)).const_mul c).ennreal_ofReal.mul
      ((Lp.stronglyMeasurable ((w σ).onScalar u.1)).measurable.norm.pow_const 2).ennreal_ofReal
  have hn (σ : Fin n → Bool) (X : Configuration n L) : 0≤∑ v : CubeCell K, q (fun i ↦ σ i=true) v X :=
    Finset.sum_nonneg (fun v _ ↦ unitPairCount_nonneg hL _ v X)
  have havg : (∫⁻ X, ENNReal.ofReal (c*(∑ v : CubeCell K, if spatialSiteDistance L A (unitCenter L v)+1≤H then q (fun _ ↦ True) v X else 0))*ENNReal.ofReal (‖u.1 X‖^2))≤
      ENNReal.ofReal (spatialPartitionEnergy L A H u) := by
    calc
      _ ≤ ∫⁻ X, ∑ σ : Fin n → Bool, ENNReal.ofReal (c*∑ v : CubeCell K, q (fun i ↦ σ i=true) v X)*ENNReal.ofReal (‖(w σ).onScalar u.1 X‖^2) := by
        apply lintegral_mono_ae
        filter_upwards [hcoe] with X hX
        have hh := ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left (spatialPartition_cell_weight hL A H X) hc)
        conv_rhs at hh => rw [Finset.mul_sum]
        have hp (σ : Fin n → Bool) : 0≤c*((∑ v : CubeCell K, q (fun i ↦ σ i=true) v X)*‖(w σ).toFun X‖^2) :=
          mul_nonneg hc (mul_nonneg (hn σ X) (sq_nonneg _))
        rw [ENNReal.ofReal_sum_of_nonneg (fun σ _ ↦ hp σ)] at hh
        simp_rw [←mul_assoc,ENNReal.ofReal_mul (mul_nonneg hc (hn _ X))] at hh
        simp_rw [hX,norm_mul,mul_pow,ENNReal.ofReal_mul (sq_nonneg _),←mul_assoc,←Finset.sum_mul]
        exact mul_le_mul_of_nonneg_right hh zero_le
      _ = ∑ σ : Fin n → Bool, ∫⁻ X, ENNReal.ofReal (c*∑ v : CubeCell K, q (fun i ↦ σ i=true) v X)*ENNReal.ofReal (‖(w σ).onScalar u.1 X‖^2) := by
        rw [lintegral_finsetSum _ (fun σ _ ↦ hm σ)]
      _ ≤ ∑ σ : Fin n → Bool, ENNReal.ofReal (selectedEnergy (fun i ↦ σ i=true) ((w σ).onJet u)) := by
        apply Finset.sum_le_sum
        intro σ _
        have hh := dirichlet_physical_cell_energy hL (fun i ↦ σ i=true) hr ((w σ).onJet u) ((w σ).onJet_mem_domain hu)
        refine (le_of_eq ?_).trans hh
        apply lintegral_congr
        intro X
        congr 2
        dsimp [c,q,unitPairCount]
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro v _
        ring
      _ = _ := by rw [spatialPartitionEnergy,ENNReal.ofReal_sum_of_nonneg (fun σ _ ↦ selectedEnergy_nonneg _ _)]
  apply le_trans _ havg
  apply le_of_eq
  have hp (X : Configuration n L) :
      ENNReal.ofReal (c*(∑ v : CubeCell K, if spatialSiteDistance L A (unitCenter L v)+1≤H then q (fun _ ↦ True) v X else 0))*ENNReal.ofReal (‖u.1 X‖^2)=
      ∑ v : CubeCell K, ENNReal.ofReal (c*(if spatialSiteDistance L A (unitCenter L v)+1≤H then q (fun _ ↦ True) v X else 0))*ENNReal.ofReal (‖u.1 X‖^2) := by
    have hpv (v : CubeCell K) : 0≤c*(if spatialSiteDistance L A (unitCenter L v)+1≤H then q (fun _ ↦ True) v X else 0) := by
      apply mul_nonneg hc
      split_ifs
      · exact unitPairCount_nonneg hL _ v X
      · exact le_refl _
    rw [Finset.mul_sum,ENNReal.ofReal_sum_of_nonneg (fun v _ ↦ hpv v),Finset.sum_mul]
  simp_rw [hp]
  rw [lintegral_finsetSum]
  · apply Finset.sum_congr rfl
    intro v _
    by_cases hv : spatialSiteDistance L A (unitCenter L v)+1≤H
    · rw [indicator_of_mem (show H∈Ici (spatialSiteDistance L A (unitCenter L v)+1) from hv)]
      simp only [ite_eq_left hv,ENNReal.ofReal_mul hc,mul_assoc]
      rw [lintegral_const_mul' _ _ (ENNReal.ofReal_ne_top)]
    · rw [indicator_of_notMem (show H∉Ici (spatialSiteDistance L A (unitCenter L v)+1) from hv)]
      simp only [ite_eq_right hv,mul_zero,ENNReal.ofReal_zero,zero_mul,lintegral_zero]
  · intro v _
    by_cases hv : spatialSiteDistance L A (unitCenter L v)+1≤H
    · simp only [ite_eq_left hv]
      exact (((unitPairCount_measurable hL _ v).const_mul c).ennreal_ofReal.mul
        ((Lp.stronglyMeasurable u.1).measurable.norm.pow_const 2).ennreal_ofReal)
    · simp only [ite_eq_right hv,mul_zero,ENNReal.ofReal_zero,zero_mul]
      exact measurable_const

theorem spatial_cell_average {n K : ℕ} {L : Length} (hL : L.val=(K:ℝ))
    (A : Finset (Torus L)) {r : ℝ} (hr : 0<r) (u : Jet n L) (hu : u∈dirichletDomain n L r) :
    (∑ v : CubeCell K, ENNReal.ofReal (Real.exp (-(spatialSiteDistance L A (unitCenter L v)+1)))*
      (ENNReal.ofReal (1/(64*Real.sqrt 3)*r)*
        (∫⁻ X, ENNReal.ofReal (unitPairCount hL (fun _ ↦ True) v X)*ENNReal.ofReal (‖u.1 X‖^2))))≤
      ∫⁻ H, ENNReal.ofReal (spatialPartitionEnergy L A H u) ∂radiusLaw := by
  have hb := lintegral_mono (μ:=radiusLaw) (fun H ↦ spatialPartition_cell_integral hL A H hr u hu)
  rw [lintegral_finsetSum] at hb
  · apply le_trans _ hb
    apply Finset.sum_le_sum
    intro v _
    rw [lintegral_indicator_const measurableSet_Ici]
    have hd : 0≤ spatialSiteDistance L A (unitCenter L v)+1 := by
      have := spatialSiteDistance_nonneg L A (unitCenter L v)
      linarith
    have ht : radiusLaw (Ici (spatialSiteDistance L A (unitCenter L v)+1))=
        ENNReal.ofReal (Real.exp (-(spatialSiteDistance L A (unitCenter L v)+1))) := by
      rw [←radiusLaw_tail_eq hd]
      exact (ENNReal.ofReal_toReal (measure_ne_top radiusLaw _)).symm
    rw [ht,mul_comm]
  · intro v _
    exact measurable_const.indicator measurableSet_Ici

end HardSphere

end

end OAI
