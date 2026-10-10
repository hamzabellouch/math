import Mathlib
import OAI.Probability.SKBarriers.Scalar.ScalarAtomic
import OAI.Probability.SKBarriers.Parisi.QuantileLipschitz
import OAI.Probability.SKBarriers.Parisi.QuantileMinimizer

namespace OAI

section

section
noncomputable section
open scoped BigOperators Topology
open MeasureTheory ProbabilityTheory Filter
namespace SK.Analytic

def unitCDF (q x : ℝ) : ℝ := if q ≤ x then 1 else 0

theorem unitCDF_indicator (q : ℝ) : unitCDF q = (Set.Ici q).indicator (fun _ => (1:ℝ)) := by
  funext x
  simp only [unitCDF,Set.indicator_apply,Set.mem_Ici]

theorem unitCDF_integrable (q : ℝ) : IntegrableOn (unitCDF q) (Set.Icc (0:ℝ) 1) := by
  rw [unitCDF_indicator]
  exact (integrable_const (1:ℝ)).indicator measurableSet_Ici

theorem unitCDF_integral (q : ℝ) (hq : q ∈ Set.Icc 0 1) :
    (∫ x in Set.Icc (0:ℝ) 1, unitCDF q x) = 1-q := by
  rw [unitCDF_indicator,setIntegral_indicator measurableSet_Ici]
  have he : Set.Icc (0:ℝ) 1 ∩ Set.Ici q = Set.Icc q 1 := by
    ext x
    simp only [Set.mem_inter_iff,Set.mem_Icc,Set.mem_Ici]
    constructor
    · intro H; exact ⟨H.2,H.1.2⟩
    · intro H; exact ⟨⟨hq.1.trans H.1,H.2⟩,H.1⟩
  rw [he,integral_Icc_eq_integral_Ioc,← intervalIntegral.integral_of_le hq.2]
  simp only [intervalIntegral.integral_const,smul_eq_mul,mul_one]

theorem unitCDF_distance_integral (a b : ℝ) (ha : a ∈ Set.Icc 0 1) (hb : b ∈ Set.Icc 0 1) :
    (∫ x in Set.Icc (0:ℝ) 1, |unitCDF a x-unitCDF b x|) = |a-b| := by
  have ordered (a b : ℝ) (ha : a ∈ Set.Icc 0 1) (hb : b ∈ Set.Icc 0 1) (hab : a ≤ b) :
      (∫ x in Set.Icc (0:ℝ) 1, |unitCDF a x-unitCDF b x|) = b-a := by
    have hn (x : ℝ) : 0 ≤ unitCDF a x-unitCDF b x := by
      simp only [unitCDF]
      split_ifs <;> try norm_num
      linarith
    simp_rw [abs_of_nonneg (hn _)]
    rw [integral_sub (unitCDF_integrable a) (unitCDF_integrable b),
      unitCDF_integral a ha,unitCDF_integral b hb]
    ring
  rcases le_total a b with hab | hba
  · rw [ordered a b ha hb hab,abs_of_nonpos (sub_nonpos.mpr hab)]
    ring
  · simp_rw [abs_sub_comm (unitCDF a _) (unitCDF b _)]
    rw [ordered b a hb ha hba,abs_of_nonneg (sub_nonneg.mpr hba)]

theorem unitCDF_sum_abs {k : ℕ} (A B : Fin (k+1) → ℝ)
    (hA : Monotone A) (hB : Monotone B) (x : ℝ) :
    |∑ j : Fin (k+1), (unitCDF (A j) x-unitCDF (B j) x)| =
      ∑ j : Fin (k+1), |unitCDF (A j) x-unitCDF (B j) x| := by
  have hs : (∀ j, 0 ≤ unitCDF (A j) x-unitCDF (B j) x) ∨
      (∀ j, unitCDF (A j) x-unitCDF (B j) x ≤ 0) := by
    by_cases H : ∃ i, A i ≤ x ∧ x < B i
    · obtain ⟨i,hiA,hiB⟩ := H
      left
      intro j
      rcases le_total j i with hji | hij
      · have ha : A j ≤ x := (hA hji).trans hiA
        simp only [unitCDF,ite_eq_left ha]
        split_ifs <;> norm_num
      · have hb : ¬B j ≤ x := not_le.mpr (hiB.trans_le (hB hij))
        simp only [unitCDF,ite_eq_right hb]
        split_ifs <;> norm_num
    · right
      intro j
      have h : A j ≤ x → B j ≤ x := by
        intro ha
        by_contra hb
        exact H ⟨j,ha,not_le.mp hb⟩
      by_cases ha : A j ≤ x
      · simp only [unitCDF,ite_eq_left ha,ite_eq_left (h ha),sub_self,le_refl]
      · simp only [unitCDF,ite_eq_right ha]
        split_ifs <;> norm_num
  rcases hs with hp | hn
  · rw [abs_of_nonneg (Finset.sum_nonneg (fun j _ => hp j))]
    simp_rw [abs_of_nonneg (hp _)]
  · rw [abs_of_nonpos (Finset.sum_nonpos (fun j _ => hn j))]
    simp_rw [abs_of_nonpos (hn _),Finset.sum_neg_distrib]

theorem quantileCDF_eq_unitCDF_sum (k : ℕ) (Q : Fin (k+1) → ℝ) (x : ℝ) :
    quantileCDF k Q x = ((k+1:ℕ):ℝ)⁻¹*∑ j : Fin (k+1), unitCDF (Q j) x := by
  rw [quantileCDF_formula,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  simp only [unitCDF]
  split_ifs <;> simp

theorem quantileCDF_L1_eq {k : ℕ} (A B : Fin (k+1) → ℝ)
    (hA : A ∈ admissibleQuantiles k) (hB : B ∈ admissibleQuantiles k) :
    (∫ x in Set.Icc (0:ℝ) 1, |quantileCDF k A x-quantileCDF k B x|) =
      ∑ j : Fin (k+1), ((k+1:ℕ):ℝ)⁻¹*|A j-B j| := by
  have he (x : ℝ) : |quantileCDF k A x-quantileCDF k B x| =
      ((k+1:ℕ):ℝ)⁻¹*∑ j : Fin (k+1), |unitCDF (A j) x-unitCDF (B j) x| := by
    rw [quantileCDF_eq_unitCDF_sum,quantileCDF_eq_unitCDF_sum,← mul_sub,← Finset.sum_sub_distrib,
      abs_mul,abs_of_nonneg (show 0 ≤ ((k+1:ℕ):ℝ)⁻¹ by positivity),unitCDF_sum_abs A B hA.1 hB.1]
  simp_rw [he]
  have hi (j : Fin (k+1)) : IntegrableOn (fun x => |unitCDF (A j) x-unitCDF (B j) x|) (Set.Icc (0:ℝ) 1) :=
    ((unitCDF_integrable (A j)).sub (unitCDF_integrable (B j))).abs
  rw [integral_const_mul,integral_finsetSum _ (fun j _ => hi j),Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [unitCDF_distance_integral (A j) (B j) (hA.2 j) (hB.2 j)]

theorem atomicParisi_lipschitz_cdf {k : ℕ} (β : ℝ) (A B : Fin (k+1) → ℝ)
    (hA : A ∈ admissibleQuantiles k) (hB : B ∈ admissibleQuantiles k) :
    |atomicParisi k β B-atomicParisi k β A| ≤
      (β^2/2)*(∫ x in Set.Icc (0:ℝ) 1, |quantileCDF k A x-quantileCDF k B x|) := by
  rw [atomicParisi_eq_extended _ _ _ hB.2,atomicParisi_eq_extended _ _ _ hA.2,quantileCDF_L1_eq A B hA hB]
  simpa only [abs_sub_comm] using extendedQuantileParisi_lipschitz β A B hA.2 hB.2
    hA.1 hB.1

end SK.Analytic

end
end

end

end OAI
