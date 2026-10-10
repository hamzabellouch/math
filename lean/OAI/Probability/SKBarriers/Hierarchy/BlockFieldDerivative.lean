import Mathlib
import OAI.Probability.SKBarriers.Hierarchy.BlockDerivativeSum

namespace OAI

section

section
noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Filter
namespace SK.Analytic
attribute [local instance 2000] parameterNormedGroup parameterNormedSpace

theorem linearMap_blockCoefficients {D N k : ℕ}
    (L : (Fin (blockDimension D N k) → ℝ) →L[ℝ] ℝ) (a : Fin D → ℝ) (v : Fin (k+1) → ℝ) :
    L (blockCoefficients (N := N) a v) =
      (∑ i : Fin D, a i*L (Pi.single (Fin.castAdd ((k+1)*N) i) 1))+
      ∑ b : Fin (k+1), ∑ i : Fin N, v b*L (Pi.single (fieldIndex D N k b i) 1) := by
  conv_lhs => rw [pi_eq_sum_univ' (blockCoefficients (N := N) a v)]
  rw [map_sum,Fin.sum_univ_add]
  simp only [map_smul,smul_eq_mul,blockCoefficients,Fin.addCases_left,Fin.addCases_right]
  congr 1
  rw [← finProdFinEquiv.sum_comp (fun t => v (finProdFinEquiv.symm t).1*L (Pi.single (Fin.natAdd D t) 1))]
  simp only [Equiv.symm_apply_apply,Fintype.sum_prod_type,fieldIndex_eq_natAdd]

theorem field_derivative_sum {N k : ℕ} (hN : 0 < N) (E : Fin N → Fin (k+1) → ℝ)
    (v w : Fin (k+1) → ℝ) :
    (∑ b, ∑ i : Fin N, w b*(v b*(1-∑ l : Fin (k+1), if b ≤ l then ((k+1:ℕ):ℝ)⁻¹*E i l else 0))) =
    (N:ℝ)*∑ b, w b*v b*(1-∑ l : Fin (k+1), if b ≤ l then ((k+1:ℕ):ℝ)⁻¹*((∑ i, E i l)/(N:ℝ)) else 0) := by
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro b _
  simp only [mul_sub,mul_one,Finset.sum_sub_distrib,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,
    Finset.mul_sum]
  rw [Finset.sum_comm]
  have hn : (N:ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  congr 1
  apply Finset.sum_congr rfl
  intro l _
  by_cases h : b ≤ l
  · simp only [h,ite_true]
    simp only [← Finset.mul_sum]
    field_simp
  · simp only [h,ite_false,mul_zero,Finset.sum_const_zero]

theorem blockPressure_field_differential {D N k : ℕ} (hN : 0 < N)
    (I : Fin D → Finset (Fin N)) (a : Fin D → ℝ) (v w : Fin (k+1) → ℝ) :
    fderiv ℝ (fun c : Fin (blockDimension D N k) → ℝ =>
      hierarchyPressure (blockDimension D N k) (blockMass D N k)
        (affineLogPartition (fun _ => 0) (spinExponent (blockDimension D N k) c (blockInteraction I))) 0)
      (blockCoefficients a v) (blockCoefficients (N := N) (fun _ => 0) w) =
    (N:ℝ)*∑ b, w b*v b*(1-∑ l : Fin (k+1), if b ≤ l then ((k+1:ℕ):ℝ)⁻¹*
      hierarchyMeanOverlap (blockDimension D N k) (blockMass D N k) (blockExponent I a v)
        (fun i s => spin (s i)) (blockLevel D N k l) else 0) := by
  rw [linearMap_blockCoefficients]
  simp only [zero_mul,Finset.sum_const_zero,zero_add,blockPressure_coordinate_variation]
  simp only [hierarchyMeanOverlap_eq_mean_integrals (blockDimension D N k) (blockMass D N k) (blockExponent I a v) (fun i s => spin (s i)) (fun i s => by cases s i <;> norm_num [spin])]
  exact field_derivative_sum hN _ v w

theorem blockCoefficients_hasDerivAt {D N k : ℕ} {a : ℝ → Fin D → ℝ}
    {v : ℝ → Fin (k+1) → ℝ} {a' : Fin D → ℝ} {v' : Fin (k+1) → ℝ} {t : ℝ}
    (ha : HasDerivAt a a' t) (hv : HasDerivAt v v' t) :
    HasDerivAt (fun u => blockCoefficients (N := N) (a u) (v u)) (blockCoefficients a' v') t := by
  apply hasDerivAt_pi.mpr
  intro i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · simpa only [blockCoefficients,Fin.addCases_left] using hasDerivAt_pi.mp ha j
  · simpa only [blockCoefficients,Fin.addCases_right] using hasDerivAt_pi.mp hv (finProdFinEquiv.symm j).1
end SK.Analytic

end
end

end

end OAI
