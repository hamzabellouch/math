import Mathlib
import OAI.Probability.SKBarriers.Parisi.QuantileVariation
import OAI.Probability.SKBarriers.Scalar.ScalarCDFLimit
import OAI.Probability.SKBarriers.Scalar.ScalarMomentSquare
import OAI.Probability.SKBarriers.Scalar.OneSiteScalar

namespace OAI

section

noncomputable section
open scoped NNReal Topology BigOperators
open MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic
attribute [local instance 2000] parameterNormedGroup parameterNormedSpace

theorem hierarchyMeanOverlap_oneSite (n : ℕ) (m v : Fin n → ℝ) (j : Fin (n+1)) :
    hierarchyMeanOverlap n m (fun s : Config 1 => spin (s 0) • coordinateLinear n v)
      (fun i s => spin (s i)) j=scalarMomentSquare n m v scalarSpinTerminal scalarMagnetization j 0 := by
  have heF : affineLogPartition (fun _ : Config 1 => 0) (fun s => spin (s 0) • coordinateLinear n v)=
      scalarParameterTerminal n v (fun _ => scalarSpinTerminal) 0 := by
    funext z
    simpa only [scalarParameterTerminal,zero_add] using affineLogPartition_oneConfig (coordinateLinear n v) z
  have heG : affineMoment (fun _ : Config 1 => 0) (fun s => spin (s 0) • coordinateLinear n v) (fun s => spin (s 0))=
      scalarParameterTerminal n v (fun _ => scalarMagnetization) 0 := by
    funext z
    simpa only [scalarParameterTerminal,zero_add] using affineMoment_oneConfig (coordinateLinear n v) z
  rw [hierarchyMeanOverlap_eq_mean_integrals]
  · simp only [Fin.sum_univ_one,Nat.cast_one,div_one,hierarchySpinMean,
      heF,heG]
    let f := scalarParameterTerminal n v (fun _ => scalarSpinTerminal) 0
    have hf : BoundedDerivs f := scalarParameterTerminal_const_regular n v scalarSpinTerminal_regular 0
    have hg := hierarchySpinMean_regular n m
      (fun s : Config 1 => spin (s 0) • coordinateLinear n v) (fun s => spin (s 0))
      (by norm_num : (0:ℝ) ≤ 1) (fun s => by cases s 0 <;> norm_num [spin]) j
    simp only [hierarchySpinMean,heF,heG] at hg
    rw [scalarMomentSquare_eq_hierarchyAverage _ _ _ scalarSpinTerminal_regular _ _ _ 0]
    symm
    apply hierarchyAverage_eq_integral _ _ f hf _ (C:=1)
    · exact (continuous_pow 2).comp hg.1
    · norm_num
    · intro z
      simpa only [f,scalarParameterTerminal,zero_add,norm_pow,one_pow] using
        pow_le_one₀ (norm_nonneg _) (hg.2 z) (n:=2)
  · intro i s
    cases s i <;> norm_num [spin]

theorem blockExponent_singleSite {D k : ℕ} (I : Fin D → Finset (Fin 1)) (v : Fin (k+1) → ℝ) :
    blockExponent I (fun _ => 0) v=fun s : Config 1 =>
      spin (s 0) • coordinateLinear (blockDimension D 1 k) (siteScalarCoefficients (D:=D) v 0) := by
  funext s
  ext z
  rw [blockExponent_expansion]
  simp only [zero_mul,Finset.sum_const_zero,zero_add,Fin.sum_univ_one,
    smul_apply,smul_eq_mul]
  rw [coordinateLinear_apply,siteScalarCoefficients_field]
  simp only [siteField,sum_apply,smul_apply,smul_eq_mul,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro b _
  ring

theorem quantileOverlapMean_eq_scalar_block (k : ℕ) (β : ℝ) (Q : Fin (k+1) → ℝ) (j : Fin (k+1)) :
    quantileOverlapMean k β Q j=
      scalarMomentSquare (blockDimension 0 1 k) (blockMass 0 1 k)
        (siteScalarCoefficients (D:=0) (fun i => β*Real.sqrt (cumulativeGapMap k Q i)) 0)
        scalarSpinTerminal scalarMagnetization (blockLevel 0 1 k j) 0 := by
  unfold quantileOverlapMean
  rw [blockExponent_singleSite,hierarchyMeanOverlap_oneSite,card_edge_one]

theorem blockDimension_oneSite (k : ℕ) : blockDimension 0 1 k=k+1 := by simp [blockDimension]

theorem scalarMomentSquare_cast {n l : ℕ} (hn : n=l) (m v : Fin l → ℝ)
    (f g : ℝ → ℝ) (j : Fin (l+1)) (x : ℝ) :
    scalarMomentSquare n (fun i => m (Fin.cast hn i)) (fun i => v (Fin.cast hn i)) f g
      (Fin.cast (congrArg (·+1) hn.symm) j) x=scalarMomentSquare l m v f g j x := by
  subst l
  rfl

theorem blockMass_oneSite_cast (k : ℕ) :
    blockMass 0 1 k=fun i => quantileMass k (Fin.cast (blockDimension_oneSite k) i) := by
  funext i
  let b := Fin.cast (blockDimension_oneSite k) i
  have he : fieldIndex 0 1 k b 0=i := by ext; simp [b]
  rw [← he,blockMass_at_field]
  simp only [quantileMass,Fin.val_cast,fieldIndex_val,Nat.mul_one,Nat.zero_add,Fin.val_zero,Nat.add_zero]

theorem siteScalarCoefficients_oneSite_cast (k : ℕ) (v : Fin (k+1) → ℝ) :
    siteScalarCoefficients (D:=0) v (0:Fin 1)=fun i => v (Fin.cast (blockDimension_oneSite k) i) := by
  funext i
  let b := Fin.cast (blockDimension_oneSite k) i
  have he : fieldIndex 0 1 k b 0=i := by ext; simp [b]
  have H := siteScalarCoefficients_at (D:=0) v (0:Fin 1) b
  simpa only [he] using H

theorem quantileOverlapMean_eq_scalar (k : ℕ) (β : ℝ) (Q : Fin (k+1) → ℝ) (j : Fin (k+1)) :
    quantileOverlapMean k β Q j=
      scalarMomentSquare (k+1) (quantileMass k)
        (fun i => β*Real.sqrt (cumulativeGapMap k Q i)) scalarSpinTerminal scalarMagnetization j.succ 0 := by
  rw [quantileOverlapMean_eq_scalar_block,blockMass_oneSite_cast,siteScalarCoefficients_oneSite_cast]
  have hj : blockLevel 0 1 k j=Fin.cast (congrArg (·+1) (blockDimension_oneSite k).symm) j.succ := by
    ext
    simp
  rw [hj]
  exact scalarMomentSquare_cast (blockDimension_oneSite k) (quantileMass k)
    (fun i => β*Real.sqrt (cumulativeGapMap k Q i)) scalarSpinTerminal scalarMagnetization j.succ 0

end SK.Analytic

end
end

end OAI
