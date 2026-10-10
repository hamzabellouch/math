import Mathlib
import OAI.Probability.SKBarriers.SpinGlass.SpinCoefficientVariation

namespace OAI

section

section
noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Filter
namespace SK.Analytic
attribute [local instance 2000] parameterNormedGroup parameterNormedSpace

theorem hierarchyMeanOverlap_eq_mean_integrals {S : Type} [Fintype S] [Nonempty S]
    {N : ℕ} (n : ℕ) (m : Fin n → ℝ) (U : S → ParameterSpace n →L[ℝ] ℝ)
    (c : Fin N → S → ℝ) (hc : ∀ i s, ‖c i s‖ ≤ 1) (j : Fin (n+1)) :
    hierarchyMeanOverlap n m U c j =
      (∑ i, ∫ z, (hierarchySpinMean n m U (c i) j z)^2
        ∂hierarchyPathLaw n m (affineLogPartition (fun _ => 0) U) 0) / (N:ℝ) := by
  unfold hierarchyMeanOverlap hierarchyMeanSquare normalizedSquare
  rw [integral_div,integral_finsetSum]
  intro i _
  have hr := hierarchySpinMean_regular n m U (c i) (by norm_num : (0:ℝ) ≤ 1) (hc i) j
  apply hierarchyPathLaw_integrable n m _ _ (affineLogPartition_boundedDerivs (fun _ => 0) U)
    (hr.1.pow 2) (C := 1) _ 0
  intro z
  dsimp only [Pi.pow_apply]
  rw [norm_pow]
  exact pow_le_one₀ (norm_nonneg _) (hr.2 z)

theorem blockAtom_sum_mul (D N k : ℕ) (f : Fin (blockDimension D N k+1) → ℝ) :
    (∑ j, hierarchyAtom (blockDimension D N k) (blockMass D N k) 1 j*f j) =
      ∑ b : Fin (k+1), ((k+1 : ℕ) : ℝ)⁻¹*f (blockLevel D N k b) := by
  simp only [hierarchyAtom_blockMass,blockAtom,Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b _
  simp only [ite_mul,zero_mul,Finset.sum_ite_eq,Finset.mem_univ,ite_true]

theorem fieldIndex_lt_blockLevel_iff (D N k : ℕ) (b l : Fin (k+1)) (i : Fin N) :
    (fieldIndex D N k b i).val < (blockLevel D N k l).val ↔ b ≤ l := by
  simp only [fieldIndex_val,blockLevel_val,Fin.le_def]
  constructor
  · intro h
    by_contra hn
    have hbl : l.val+1 ≤ b.val := by omega
    have hmul := Nat.mul_le_mul_right N hbl
    omega
  · intro h
    have hmul := Nat.mul_le_mul_right N h
    nlinarith [i.isLt]

theorem blockPressure_coordinate_variation {D N k : ℕ} (I : Fin D → Finset (Fin N))
    (a : Fin D → ℝ) (v : Fin (k+1) → ℝ) (b : Fin (k+1)) (i : Fin N) :
    fderiv ℝ (fun c : Fin (blockDimension D N k) → ℝ =>
      hierarchyPressure (blockDimension D N k) (blockMass D N k)
        (affineLogPartition (fun _ => 0) (spinExponent (blockDimension D N k) c (blockInteraction I))) 0)
      (blockCoefficients a v) (Pi.single (fieldIndex D N k b i) 1) =
      v b * (1-∑ l : Fin (k+1), if b ≤ l then ((k+1:ℕ):ℝ)⁻¹ *
        (∫ z, (hierarchySpinMean (blockDimension D N k) (blockMass D N k) (blockExponent I a v)
          (fun s => spin (s i)) (blockLevel D N k l) z)^2
          ∂hierarchyPathLaw (blockDimension D N k) (blockMass D N k)
            (affineLogPartition (fun _ => 0) (blockExponent I a v)) 0) else 0) := by
  rw [spinPressure_coefficient_variation,blockCoefficients_field,blockInteraction_field]
  simp only [spinMonomial,Finset.prod_singleton]
  congr 2
  have he (j : Fin (blockDimension D N k+1)) (c : ℝ) :
      (if (fieldIndex D N k b i).val < j.val then
        hierarchyAtom (blockDimension D N k) (blockMass D N k) 1 j*c else 0) =
      hierarchyAtom (blockDimension D N k) (blockMass D N k) 1 j *
        (if (fieldIndex D N k b i).val < j.val then c else 0) := by split_ifs <;> simp
  simp_rw [he]
  rw [blockAtom_sum_mul]
  simp only [fieldIndex_lt_blockLevel_iff,mul_ite,mul_zero]
  rfl
end SK.Analytic

end
end

end

end OAI
