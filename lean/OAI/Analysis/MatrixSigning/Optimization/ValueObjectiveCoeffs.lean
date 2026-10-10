import Mathlib
import OAI.Analysis.MatrixSigning.Optimization.ObjectiveCLM
import OAI.Analysis.MatrixSigning.Optimization.ValueOuterRadius

namespace OAI

open Matrix

namespace CurrentKS.RationalSDP
noncomputable section
open CurrentKS.Hermitian CurrentKS.HermitianCoordinates CurrentKS.Variational Matrix Set
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.Frobenius

variable {d N : ℕ}

def valueObjectiveCoeffs (d : ℕ) (ε : ℚ) : Fin (valueDimension d) → ℚ :=
  Pi.single (valueIndex d (.inl 0)) 1 + ε •
    ∑ i : Fin d, (Pi.single (valueIndex d (.inr (.inl (i,i)))) 1 +
      Pi.single (valueIndex d (.inr (.inr (i,i)))) 1)

def valueLipschitz (d : ℕ) (ε : ℚ) : ℚ := ((valueDimension d:ℚ)+1)*(1+2*ε*d)

lemma valueObjectiveCoeffs_dot (ε : ℚ) (v : Fin (valueDimension d) → ℚ) :
    valueObjectiveCoeffs d ε ⬝ᵥ v = valueObjective d ε v := by
  rw [valueObjective_apply]
  simp [valueObjectiveCoeffs,add_dotProduct,smul_dotProduct,sum_dotProduct,
    single_dotProduct,timeCoordinate,matrixCoordinate,smul_eq_mul]

lemma valueObjectiveCoeffs_real (ε : ℚ) (v : Fin (valueDimension d) → ℝ) :
    (fun i => (valueObjectiveCoeffs d ε i:ℝ)) ⬝ᵥ v =
      timeCoordinate d v+(ε:ℝ)*∑ i : Fin d,
        (matrixCoordinate d false v (i,i)+matrixCoordinate d true v (i,i)) := by
  have he : (fun i => (valueObjectiveCoeffs d ε i:ℝ)) =
      Pi.single (valueIndex d (.inl 0)) 1 + (ε:ℝ) •
      ∑ i : Fin d,(Pi.single (valueIndex d (.inr (.inl (i,i)))) 1+
        Pi.single (valueIndex d (.inr (.inr (i,i)))) 1) := by
    have hs (j k : Fin (valueDimension d)) :
        ((Pi.single j (1:ℚ) : Fin (valueDimension d) → ℚ) k : ℝ) =
          (Pi.single j (1:ℝ) : Fin (valueDimension d) → ℝ) k := by
      by_cases h : j=k
      · subst k; simp
      · simp [h]
    ext k
    simp only [valueObjectiveCoeffs,Pi.add_apply,Pi.smul_apply,Finset.sum_apply,
      smul_eq_mul,Rat.cast_add,Rat.cast_mul,Rat.cast_sum,hs]
  rw [he]
  simp [add_dotProduct,smul_dotProduct,sum_dotProduct,
    single_dotProduct,timeCoordinate,matrixCoordinate,smul_eq_mul]

lemma objectiveCLM_value (ε : ℚ) (v : EuclideanSpace ℝ (Fin (valueDimension d))) :
    objectiveCLM (valueObjectiveCoeffs d ε) v = objective (ε:ℝ) (unpackValue v) := by
  rw [objectiveCLM_apply,valueObjectiveCoeffs_real]
  simp only [objective,unpackValue,realTrace_add]
  congr 1
  simp only [assemble,Hermitian.realTrace,trace_decode,← Finset.sum_add_distrib]

lemma valueObjectiveCoeffs_bound {ε : ℚ} (hε : 0 ≤ ε) (k : Fin (valueDimension d)) :
    |valueObjectiveCoeffs d ε k| ≤ 1+2*ε*d := by
  have hp (j : Fin (valueDimension d)) :
      0 ≤ (Pi.single j (1:ℚ) : Fin (valueDimension d) → ℚ) k ∧
      (Pi.single j (1:ℚ) : Fin (valueDimension d) → ℚ) k ≤ 1 := by
    simp only [Pi.single_apply]
    split_ifs <;> norm_num
  have hs : (∑ i : Fin d,
      ((Pi.single (valueIndex d (.inr (.inl (i,i)))) (1:ℚ) : Fin (valueDimension d) → ℚ) k+
      (Pi.single (valueIndex d (.inr (.inr (i,i)))) (1:ℚ) : Fin (valueDimension d) → ℚ) k)) ≤ 2*d := by
    calc
      _ ≤ ∑ _ : Fin d,(2:ℚ) := Finset.sum_le_sum fun i _ => by
        have h₁ := (hp (valueIndex d (.inr (.inl (i,i))))).2
        have h₂ := (hp (valueIndex d (.inr (.inr (i,i))))).2
        linarith
      _ = _ := by simp; ring
  have hn : 0 ≤ valueObjectiveCoeffs d ε k := by
    simp only [valueObjectiveCoeffs,Pi.add_apply,Pi.smul_apply,Finset.sum_apply,smul_eq_mul]
    exact add_nonneg (hp _).1 (mul_nonneg hε (Finset.sum_nonneg fun i _ =>
      add_nonneg (hp _).1 (hp _).1))
  rw [abs_of_nonneg hn]
  simp only [valueObjectiveCoeffs,Pi.add_apply,Pi.smul_apply,Finset.sum_apply,smul_eq_mul]
  have ht := (hp (valueIndex d (.inl 0))).2
  have hm := mul_le_mul_of_nonneg_left hs hε
  nlinarith

lemma valueLipschitz_pos {ε : ℚ} (hε : 0 ≤ ε) : 0 < valueLipschitz d ε := by
  unfold valueLipschitz
  positivity

lemma objectiveCLM_value_norm {ε : ℚ} (hε : 0 ≤ ε) :
    ‖objectiveCLM (valueObjectiveCoeffs d ε)‖ ≤ (valueLipschitz d ε:ℝ) := by
  have hb : ‖realVector (valueObjectiveCoeffs d ε)‖ ≤
      ((valueDimension d:ℝ)+1)*(1+2*(ε:ℝ)*d) := by
    apply euclidean_norm_le_card _ (by exact_mod_cast (show (0:ℚ)≤1+2*ε*d by positivity))
    intro k
    change ‖(valueObjectiveCoeffs d ε k:ℝ)‖ ≤ _
    rw [Real.norm_eq_abs]
    exact_mod_cast valueObjectiveCoeffs_bound hε k
  change ‖innerSL ℝ (realVector (valueObjectiveCoeffs d ε))‖ ≤ _
  rw [innerSL_apply_norm]
  simpa only [valueLipschitz,Rat.cast_mul,Rat.cast_add,Rat.cast_one,Rat.cast_ofNat,Rat.cast_natCast] using hb

end
end CurrentKS.RationalSDP

end OAI
