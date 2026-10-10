import OAI.Combinatorics.Progressions.Estimates.CoefficientSliceEmbedding

namespace OAI

section

namespace Erdos3

open scoped BigOperators NNReal Classical

structure RetainedCoefficientSlice (M : ℕ) (B T η : ℝ≥0) where
  length : ℕ
  modulus : ℕ
  residue : ZMod modulus
  modulus_pos : 0 < modulus
  modulus_le : modulus ≤ M
  weight : (Option Empty → ℝ) → ℝ
  weight_range : ∀ x, 0 ≤ weight x ∧ weight x ≤ B
  weight_lipschitz : LipschitzWith T weight
  mean_lower : (η : ℝ) ≤ 𝔼 x : ↥(coefficientResidueSet length modulus residue),
    weight (fun _ => (x.val : ℝ) / length)

namespace RetainedCoefficientSlice

variable {M : ℕ} {B T η : ℝ≥0} (s : RetainedCoefficientSlice M B T η)

abbrev Domain := ↥(coefficientResidueSet s.length s.modulus s.residue)

noncomputable def sliceWeight (x : s.Domain) : ℝ := s.weight (fun _ => (x.val : ℝ) / s.length)

theorem sliceWeight_nonneg (x : s.Domain) : 0 ≤ s.sliceWeight x := (s.weight_range _).1

theorem total_pos (hη : 0 < η) : 0 < ∑ x, s.sliceWeight x :=
  FiniteProbabilityWeights.sum_pos_of_expect_pos _ ((show (0 : ℝ) < η from hη).trans_le s.mean_lower)

noncomputable def law (hη : 0 < η) : FiniteProbabilityWeights s.Domain :=
  FiniteProbabilityWeights.ofPositiveWeights s.sliceWeight s.sliceWeight_nonneg (s.total_pos hη)

def finiteSlice (offset stride : ℤ) : FiniteCoefficientSlice where
  length := s.length
  offset := offset
  stride := stride
  modulus := s.modulus
  residue := s.residue

theorem length_pos_of_size (hsize : M ≤ s.length) : 0 < s.length :=
  s.modulus_pos.trans_le (s.modulus_le.trans hsize)

noncomputable def normalizer (hsize : M ≤ s.length) : ℝ :=
  (scalarCubeResidueWeights Empty s.length M (s.length_pos_of_size hsize)
    (fun _ => s.modulus) (fun _ => s.residue) (fun _ => s.modulus_pos) (fun _ => s.modulus_le)
    (by simpa only [Fintype.card_empty, zero_add, one_mul] using hsize)).mean
    (fun z => s.weight (fun i => (z i : ℝ) / s.length))

theorem normalizer_eq_mean (hsize : M ≤ s.length) :
    s.normalizer hsize = 𝔼 x : s.Domain, s.sliceWeight x := by
  unfold normalizer
  rw [scalarCubeResidueWeights_mean]
  apply Fintype.expect_equiv (emptyScalarCubeResidueEquiv s.length (fun _ => s.modulus) (fun _ => s.residue))
  intro x
  unfold sliceWeight
  congr 1
  funext i
  cases i with
  | none => rfl
  | some a => exact a.elim

theorem normalizer_lower (hsize : M ≤ s.length) : (η : ℝ) ≤ s.normalizer hsize := by
  rw [s.normalizer_eq_mean]
  exact s.mean_lower

noncomputable def normalized (hB : 0 < B) (hη : 0 < η) (hsize : M ≤ s.length) :
    NormalizedScalarCubeSource Empty :=
  normalizedScalarCubeSourceOfMeanLower Empty s.length M (s.length_pos_of_size hsize)
    (fun _ => s.modulus) (fun _ => s.residue) (fun _ => s.modulus_pos) (fun _ => s.modulus_le)
    (by simpa only [Fintype.card_empty, zero_add, one_mul] using hsize)
    s.weight B T η hB hη s.weight_range s.weight_lipschitz (s.normalizer_lower hsize)

theorem normalized_coefficientDensity (hB : 0 < B) (hη : 0 < η) (hsize : M ≤ s.length)
    (x : s.Domain) :
    (s.normalized hB hη hsize).coefficientDensity x = s.sliceWeight x / s.normalizer hsize := rfl

theorem normalized_coefficientWeights (hB : 0 < B) (hη : 0 < η) (hsize : M ≤ s.length) :
    (s.normalized hB hη hsize).coefficientWeights = s.law hη := by
  have hZ : 0 < s.normalizer hsize := (show (0 : ℝ) < η from hη).trans_le (s.normalizer_lower hsize)
  exact FiniteProbabilityWeights.ofDensity_div_eq_ofPositiveWeights s.sliceWeight s.sliceWeight_nonneg
    (s.total_pos hη) hZ (s.normalized hB hη hsize).coefficientDensity_mean_one

theorem affine_abs_le (offset : ℤ) (stride : ℕ) (x : s.Domain) :
    |((offset + (stride : ℤ) * x.val : ℤ) : ℝ)| ≤ |(offset : ℝ)| + (stride : ℝ) * s.length := by
  have hb := (s.finiteSlice offset stride).value_abs_le x
  have hb' : |(((s.finiteSlice offset stride).value x : ℤ) : ℝ)| ≤
      ((s.finiteSlice offset stride).radius : ℝ) := by exact_mod_cast hb
  simpa only [finiteSlice, FiniteCoefficientSlice.value, FiniteCoefficientSlice.radius,
    Nat.cast_add, Nat.cast_mul, Nat.cast_natAbs, Int.cast_abs, Int.cast_natCast,
    abs_of_nonneg (Nat.cast_nonneg stride : (0 : ℝ) ≤ _)] using hb'

end RetainedCoefficientSlice

end Erdos3

end

end OAI
