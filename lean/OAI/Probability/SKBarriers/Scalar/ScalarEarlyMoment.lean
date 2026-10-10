import Mathlib
import OAI.Probability.SKBarriers.Scalar.ScalarMomentLevel
import OAI.Probability.SKBarriers.Scalar.ScalarResponse

namespace OAI

section

noncomputable section
open scoped BigOperators NNReal Topology
open MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic
attribute [local instance 2000] parameterNormedGroup parameterNormedSpace

def scalarPrefixVector (n : ℕ) (v : Fin n → ℝ) (j : Fin (n+1)) (i : Fin n) : ℝ :=
  if i.val < j.val then v i else 0

def scalarPrefixVariance (n : ℕ) (v : Fin n → ℝ) (j : Fin (n+1)) : ℝ :=
  ∑ i, (scalarPrefixVector n v j i)^2

theorem coordinateLinear_prefix_split (a b : ℕ) (v : Fin (a+b) → ℝ)
    (z : ParameterSpace (a+b)) :
    coordinateLinear (a+b) (scalarPrefixVector (a+b) v ⟨a,by omega⟩) z=
      ∑ i : Fin a, v (i.castAdd b)*coordinateProjection (a+b) (i.castAdd b) z := by
  rw [coordinateLinear_apply,Fin.sum_univ_add]
  simp only [scalarPrefixVector,Fin.val_castAdd,Fin.val_natAdd]
  simp only [show ∀ i : Fin a, i.val < a from Fin.isLt,ite_true]
  have he (i : Fin b) : ¬ a+i.val < a := by omega
  simp only [he,ite_false,zero_mul,Finset.sum_const_zero,add_zero]

theorem hierarchyMomentLevel_spin_abs_le_prefix (n : ℕ) (m v : Fin n → ℝ)
    (hm : ∀ i, m i∈Icc (0:ℝ) 1) (j : Fin (n+1)) (z : ParameterSpace n) :
    |hierarchyMomentLevel n m
      (affineLogPartition (fun _ : Bool => 0) (fun b => spin b • scalarSpinField n v))
      (affineMoment (fun _ : Bool => 0) (fun b => spin b • scalarSpinField n v) spin) j z| ≤
      |parameter n z+coordinateLinear n (scalarPrefixVector n v j) z| := by
  rw [scalarSpin_affineMoment,scalarSpinRoot_gradient,← scalarSpinParameter_eq]
  rcases j with ⟨a,ha⟩
  obtain ⟨b,hb⟩ := Nat.exists_eq_add_of_le (Nat.le_of_lt_succ ha)
  subst n
  rw [hierarchyMomentLevel_scalar_split,coordinateLinear_prefix_split]
  simp only [zero_add]
  rw [scalarHierarchyAverage_translate]
  exact scalarHierarchyAverage_spin_abs_le_field b _ _ (fun i => hm _) _

theorem parameter_ae_hierarchyPathLaw (n : ℕ) (m : Fin n → ℝ)
    (f : ParameterSpace n → ℝ) (x : ℝ) :
    ∀ᵐ z ∂hierarchyPathLaw n m f x, parameter n z=x := by
  exact (withDensity_absolutelyContinuous _ _).ae_le (parameter_ae_fiberGaussian n x)

theorem parameter_coordinateAxis (n : ℕ) (i : Fin n) : parameter n (coordinateAxis n i)=0 := by
  induction n with
  | zero => exact Fin.elim0 i
  | succ n ih =>
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp [coordinateAxis_last,parameter]
    · simpa only [coordinateAxis_castSucc,parameter,ContinuousLinearMap.comp_apply,
        ContinuousLinearMap.coe_fst'] using ih j

theorem scalarPrefix_square_bound (n : ℕ) (m v : Fin n → ℝ)
    (hm : ∀ i, m i∈Icc (0:ℝ) 1) (hmono : Monotone m) (j : Fin (n+1)) (x : ℝ) :
    (∫ z, (coordinateLinear n (scalarPrefixVector n v j) z)^2
      ∂hierarchyPathLaw n m (affineLogPartition (fun _ : Bool => 0)
        (fun b => spin b • scalarSpinField n v)) x) ≤
      2*scalarPrefixVariance n v j+4*(scalarPrefixVariance n v j)^2 := by
  have H := affineHierarchy_square_bound n m hm hmono (fun _ : Bool => 0)
    (fun b => spin b • scalarSpinField n v) (fun i => |v i|) (fun i => abs_nonneg _)
    (fun b i => by
      cases b <;> simp [spin,scalarSpinField,parameter_coordinateAxis,coordinateLinear_coordinateAxis]) x
    (scalarPrefixVector n v j)
  have he : (∑ i, |scalarPrefixVector n v j i| * |v i|)=scalarPrefixVariance n v j := by
    apply Finset.sum_congr rfl
    intro i _
    unfold scalarPrefixVector
    split_ifs
    · rw [← sq_abs]; ring
    · simp
  rw [he] at H
  change _ ≤ 2*scalarPrefixVariance n v j+(2*scalarPrefixVariance n v j)^2 at H
  nlinarith

theorem scalarMomentSquare_origin_le_prefix (n : ℕ) (m v : Fin n → ℝ)
    (hm : ∀ i, m i∈Icc (0:ℝ) 1) (hmono : Monotone m) (j : Fin (n+1)) :
    scalarMomentSquare n m v scalarSpinTerminal scalarMagnetization j 0 ≤
      2*scalarPrefixVariance n v j+4*(scalarPrefixVariance n v j)^2 := by
  let f := affineLogPartition (fun _ : Bool => (0:ℝ)) (fun b => spin b • scalarSpinField n v)
  let G := affineMoment (fun _ : Bool => (0:ℝ)) (fun b => spin b • scalarSpinField n v) spin
  let μ := hierarchyPathLaw n m f 0
  let L := coordinateLinear n (scalarPrefixVector n v j)
  have hf : BoundedDerivs f := affineLogPartition_boundedDerivs _ _
  have hG := affineMoment_continuous (fun _ : Bool => (0:ℝ)) (fun b => spin b • scalarSpinField n v) spin
  have hbG (z) : ‖G z‖ ≤ 1 := affineMoment_norm_le _ _ _ (by intro b; cases b <;> norm_num [spin]) z
  have hM := hierarchyMomentLevel_bounded_continuous n m f G hf hG zero_le_one hbG j
  have hiM : Integrable (fun z => (hierarchyMomentLevel n m f G j z)^2) μ :=
    hierarchyPathLaw_integrable n m f _ hf (hM.1.pow 2) (C:=1) (fun z => by
      simp only [Pi.pow_apply,norm_pow]; simpa using pow_le_pow_left₀ (norm_nonneg _) (hM.2 z) 2) 0
  have hiL : Integrable (fun z => (L z)^2) μ :=
    ((HasExpGrowth.linear L).pow 2).integrable_hierarchyPathLaw n m hf (L.continuous.pow 2) 0
  rw [← scalarMomentSquare_eq_path_integral]
  apply (integral_mono_ae hiM hiL ?_).trans (scalarPrefix_square_bound n m v hm hmono j 0)
  filter_upwards [parameter_ae_hierarchyPathLaw n m f 0] with z hz
  have H := hierarchyMomentLevel_spin_abs_le_prefix n m v hm j z
  rw [hz,zero_add] at H
  simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) (abs_nonneg _)).mpr H

end SK.Analytic

end
end

end OAI
