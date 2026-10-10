import Mathlib
import OAI.Probability.SKBarriers.Parisi.CDFOverlap
import OAI.Probability.SKBarriers.Scalar.ScalarSpatialAverage
import OAI.Probability.SKBarriers.Scalar.ScalarEarlyMoment

namespace OAI

section

noncomputable section
open scoped BigOperators NNReal Topology
open MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic
attribute [local instance 2000] parameterNormedGroup parameterNormedSpace

theorem scalarPrefixVariance_nonneg (n : ℕ) (v : Fin n → ℝ) (j : Fin (n+1)) :
    0 ≤ scalarPrefixVariance n v j := Finset.sum_nonneg (fun _ _ => sq_nonneg _)

theorem scalarPrefixVariance_monotone (n : ℕ) (v : Fin n → ℝ) :
    Monotone (scalarPrefixVariance n v) := by
  intro i j hij
  apply Finset.sum_le_sum
  intro k _
  unfold scalarPrefixVector
  by_cases h : k.val < i.val
  · rw [ite_eq_left h,ite_eq_left (lt_of_lt_of_le h hij)]
  · rw [ite_eq_right h,zero_pow (by norm_num : 2≠0)]
    exact sq_nonneg _

theorem scalarFiniteResponse_origin_le (n : ℕ) (m v : Fin n → ℝ)
    (hm : ∀ i, m i∈Icc (0:ℝ) 1) (hmono : Monotone m) (i : Fin n) :
    scalarFiniteResponse n m v i 0 ≤
      rootHessian 0 (scalarHierarchy n m v scalarSpinTerminal) 0+
        (2*scalarPrefixVariance n v i.castSucc+4*(scalarPrefixVariance n v i.castSucc)^2) := by
  rw [scalarFiniteResponse_eq_hessian_prefix n m v hm hmono]
  apply add_le_add_right
  let C := 2*scalarPrefixVariance n v i.castSucc+4*(scalarPrefixVariance n v i.castSucc)^2
  have hC : 0 ≤ C := by
    have hV := scalarPrefixVariance_nonneg n v i.castSucc
    dsimp [C]; positivity
  calc
    _ ≤ ∑ j : Fin (n+1), hierarchyAtom n m 1 j*C := by
      apply Finset.sum_le_sum
      intro j _
      have ha := hierarchyAtom_nonneg n m zero_le_one (fun i => (hm i).1) (fun i => (hm i).2) hmono j
      split_ifs with hj
      · apply mul_le_mul_of_nonneg_left _ ha
        have hV := scalarPrefixVariance_monotone n v (show j ≤ i.castSucc from hj)
        have hsq := (sq_le_sq₀ (scalarPrefixVariance_nonneg n v j)
          (scalarPrefixVariance_nonneg n v i.castSucc)).mpr hV
        exact (scalarMomentSquare_origin_le_prefix n m v hm hmono j).trans (by
          dsimp [C]; nlinarith)
      · exact mul_nonneg ha hC
    _ = C := by rw [← Finset.sum_mul,hierarchyAtom_sum,one_mul]

theorem scalarHierarchyAverage_spin_square_lipschitz (n : ℕ) (m v : Fin n → ℝ)
    (hm : ∀ i, m i∈Icc (0:ℝ) 1) :
    LipschitzWith 2 (fun x => (scalarHierarchyAverage n m v scalarSpinTerminal scalarMagnetization x)^2) := by
  have he : scalarHierarchyAverage n m v scalarSpinTerminal scalarMagnetization=
      rootGradient 0 (scalarHierarchy n m v scalarSpinTerminal) := by
    funext x
    exact (scalarHierarchy_gradient_average n m v scalarSpinTerminal_regular scalarSpinTerminal_hasDerivAt x).symm
  have hB (x) : |scalarHierarchyAverage n m v scalarSpinTerminal scalarMagnetization x| ≤ 1 :=
    scalarHierarchyAverage_abs_le scalarSpinTerminal_regular scalarMagnetization_abs_le_one n m v x
  apply LipschitzWith.of_dist_le_mul
  intro x y
  simp only [Real.dist_eq,NNReal.coe_ofNat]
  apply (abs_sq_sub_sq_le_two (hB x) (hB y)).trans
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  rw [he]
  simpa only [Real.norm_eq_abs,NNReal.coe_one,one_mul] using
    (scalarHierarchy_spin_gradient_lipschitz n m v hm).norm_sub_le x y

theorem scalarMomentSquare_spin_spatial_bound (n : ℕ) (m v : Fin n → ℝ)
    (hm : ∀ i, m i∈Icc (0:ℝ) 1) (hmono : Monotone m)
    (j : Fin (n+1)) (x y : ℝ) :
    |scalarMomentSquare n m v scalarSpinTerminal scalarMagnetization j x-
      scalarMomentSquare n m v scalarSpinTerminal scalarMagnetization j y| ≤
      (2+2*Real.exp 2)*|x-y| := by
  rcases j with ⟨a,ha⟩
  obtain ⟨b,hb⟩ := Nat.exists_eq_add_of_le (Nat.le_of_lt_succ ha)
  subst n
  rw [scalarMomentSquare_split]
  have hmb : ∀ i : Fin b, m (i.natAdd a)∈Icc (0:ℝ) 1 := fun i => hm _
  have H := scalarHierarchyAverage_spatial_bound a (fun i => m (i.castAdd b)) (fun i => v (i.castAdd b))
    (fun i => hm _) (fun i j hij => hmono hij)
    (scalarHierarchy_regular b _ (fun i => v (i.natAdd a)) scalarSpinTerminal_regular)
    (scalarHierarchy_lipschitz b _ (fun i => v (i.natAdd a)) (fun i => (hmb i).1) scalarSpinTerminal_regular scalarSpinTerminal_lipschitz)
    (scalarHierarchyAverage_spin_square_lipschitz b _ _ hmb)
    (C:=1) (fun z => by
      have H := scalarHierarchyAverage_abs_le scalarSpinTerminal_regular scalarMagnetization_abs_le_one
        b (fun i => m (i.natAdd a)) (fun i => v (i.natAdd a)) z
      rw [abs_of_nonneg (sq_nonneg _)]
      simpa only [NNReal.coe_one,one_pow,sq_abs] using pow_le_pow_left₀ (abs_nonneg _) H 2) x y
  simpa only [NNReal.coe_one,NNReal.coe_ofNat,mul_one, add_zero] using H

theorem scalarFiniteResponse_spatial_bound (n : ℕ) (m v : Fin n → ℝ)
    (hm : ∀ i, m i∈Icc (0:ℝ) 1) (hmono : Monotone m) (i : Fin n) (x y : ℝ) :
    |scalarFiniteResponse n m v i x-scalarFiniteResponse n m v i y| ≤
      (2+2*Real.exp 2)*|x-y| := by
  let C := (2+2*Real.exp 2)*|x-y|
  have hC : 0≤C := by dsimp [C]; positivity
  have he : scalarFiniteResponse n m v i x-scalarFiniteResponse n m v i y =
      ∑ j : Fin (n+1), if i.val < j.val then hierarchyAtom n m 1 j*
        (scalarMomentSquare n m v scalarSpinTerminal scalarMagnetization j y-
          scalarMomentSquare n m v scalarSpinTerminal scalarMagnetization j x) else 0 := by
    unfold scalarFiniteResponse
    rw [show (1-(∑ j : Fin (n+1), if i.val < j.val then hierarchyAtom n m 1 j*
      scalarMomentSquare n m v scalarSpinTerminal scalarMagnetization j x else 0))-
      (1-(∑ j : Fin (n+1), if i.val < j.val then hierarchyAtom n m 1 j*
      scalarMomentSquare n m v scalarSpinTerminal scalarMagnetization j y else 0)) =
      ∑ j : Fin (n+1), ((if i.val < j.val then hierarchyAtom n m 1 j*
      scalarMomentSquare n m v scalarSpinTerminal scalarMagnetization j y else 0)-
      (if i.val < j.val then hierarchyAtom n m 1 j*
      scalarMomentSquare n m v scalarSpinTerminal scalarMagnetization j x else 0)) by
      rw [Finset.sum_sub_distrib]; ring]
    apply Finset.sum_congr rfl
    intro j _
    split_ifs <;> ring
  rw [he]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  calc
    _ ≤ ∑ j : Fin (n+1), hierarchyAtom n m 1 j*C := by
      apply Finset.sum_le_sum
      intro j _
      have ha := hierarchyAtom_nonneg n m zero_le_one (fun i => (hm i).1) (fun i => (hm i).2) hmono j
      split_ifs
      · rw [abs_mul,abs_of_nonneg ha,abs_sub_comm]
        exact mul_le_mul_of_nonneg_left (scalarMomentSquare_spin_spatial_bound n m v hm hmono j x y) ha
      · simpa only [abs_zero] using mul_nonneg ha hC
    _ = C := by rw [← Finset.sum_mul,hierarchyAtom_sum,one_mul]

end SK.Analytic

end
end

end OAI
