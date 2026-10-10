import Mathlib
import OAI.Probability.SKBarriers.Scalar.ScalarEndpoint
import OAI.Probability.SKBarriers.Interpolation.FieldVarianceMonotone

namespace OAI

section

section
noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic

theorem cumulativeGapMap_nonneg_iff (k : ℕ) (Q : Fin (k+1) → ℝ) :
    (∀ j, 0 ≤ cumulativeGapMap k Q j) ↔ 0 ≤ Q 0 ∧ Monotone Q := by
  constructor
  · intro h
    refine ⟨h 0,Fin.monotone_iff_le_succ.mpr (fun j => ?_)⟩
    exact sub_nonneg.mp (h j.succ)
  · rintro ⟨h0,hm⟩ j
    refine Fin.cases h0 (fun i => ?_) j
    exact sub_nonneg.mpr (hm (Fin.castSucc_le_succ i))

def clampQuantile {k : ℕ} (Q : Fin (k+1) → ℝ) (j : Fin (k+1)) : ℝ := min (Q j) 1

theorem clampQuantile_gap {k : ℕ} (Q : Fin (k+1) → ℝ)
    (hQ : ∀ j, 0 ≤ cumulativeGapMap k Q j) (j : Fin (k+1)) :
    0 ≤ cumulativeGapMap k (clampQuantile Q) j ∧
      cumulativeGapMap k (clampQuantile Q) j ≤ cumulativeGapMap k Q j := by
  obtain ⟨h0,hm⟩ := (cumulativeGapMap_nonneg_iff k Q).mp hQ
  refine Fin.cases ?_ (fun i => ?_) j
  · exact ⟨le_min h0 zero_le_one,min_le_left _ _⟩
  · simp only [cumulativeGapMap_succ,clampQuantile]
    have hi := hm (Fin.castSucc_le_succ i)
    by_cases hb : Q i.succ ≤ 1
    · rw [min_eq_left hb,min_eq_left (hi.trans hb)]
      exact ⟨sub_nonneg.mpr hi,le_rfl⟩
    · rw [min_eq_right (le_of_not_ge hb)]
      by_cases ha : Q i.castSucc ≤ 1
      · rw [min_eq_left ha]
        constructor <;> linarith
      · rw [min_eq_right (le_of_not_ge ha),sub_self]
        exact ⟨le_rfl,sub_nonneg.mpr hi⟩

theorem clampQuantile_admissible {k : ℕ} (Q : Fin (k+1) → ℝ)
    (hQ : ∀ j, 0 ≤ cumulativeGapMap k Q j) :
    Monotone (clampQuantile Q) ∧ ∀ j, clampQuantile Q j ∈ Set.Icc 0 1 := by
  have H := (cumulativeGapMap_nonneg_iff k (clampQuantile Q)).mp (fun j => (clampQuantile_gap Q hQ j).1)
  refine ⟨H.2,fun j => ⟨H.1.trans (H.2 (Fin.zero_le j)),min_le_right _ _⟩⟩

theorem extendedQuantileParisi_clamp_le {k : ℕ} (β : ℝ) (Q : Fin (k+1) → ℝ)
    (hQ : ∀ j, 0 < cumulativeGapMap k Q j) {δ : ℝ} (hδ : 0 ≤ δ)
    (hupper : ∀ j, Q j ≤ 1+δ) :
    extendedQuantileParisi k β (clampQuantile Q) ≤ extendedQuantileParisi k β Q+(β^2/4)*(2*δ) := by
  have hg := clampQuantile_gap Q (fun j => (hQ j).le)
  have H := skBlock_field_variance_mono (N := 1) (k := k) (by norm_num) 0 β
    (cumulativeGapMap k (clampQuantile Q)) (cumulativeGapMap k Q)
    (fun j => (hg j).1) hQ (fun j => (hg j).2)
  simp only [skBlockRoot_zero_disorder_scalar (by norm_num : 0 < 1),Nat.cast_one,one_mul,div_one] at H
  have hqn := (cumulativeGapMap_nonneg_iff k Q).mp (fun j => (hQ j).le)
  have hnonneg (j : Fin (k+1)) : 0 ≤ Q j := hqn.1.trans (hqn.2 (Fin.zero_le j))
  have hsq : (∑ j : Fin (k+1), ((k+1:ℕ):ℝ)⁻¹*(clampQuantile Q j)^2) ≤
      ∑ j : Fin (k+1), ((k+1:ℕ):ℝ)⁻¹*(Q j)^2 := by
    apply Finset.sum_le_sum
    intro j _
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    exact sq_le_sq₀ (le_min (hnonneg j) zero_le_one) (hnonneg j) |>.mpr (min_le_left _ _)
  have hlast : Q (Fin.last k)-clampQuantile Q (Fin.last k) ≤ δ := by
    dsimp only [clampQuantile]
    by_cases h : Q (Fin.last k) ≤ 1
    · rw [min_eq_left h,sub_self]
      exact hδ
    · rw [min_eq_right (le_of_not_ge h)]
      linarith [hupper (Fin.last k)]
  unfold extendedQuantileParisi
  have hc : 0 ≤ β^2/4 := by positivity
  have hcineq := mul_le_mul_of_nonneg_left (show
      1-2*clampQuantile Q (Fin.last k)+∑ j : Fin (k+1), ((k+1:ℕ):ℝ)⁻¹*(clampQuantile Q j)^2 ≤
      1-2*Q (Fin.last k)+∑ j : Fin (k+1), ((k+1:ℕ):ℝ)⁻¹*(Q j)^2+2*δ by linarith) hc
  nlinarith

theorem exists_admissible_scalar_lower_bound {N k : ℕ} (hN : 0 < N) (hk : 0 < k)
    {β η : ℝ} (hβ : 0 < β) (hη : 0 < η)
    (hsmall : (k:ℝ)/Real.sqrt ((N:ℝ)*(β^2*η)) ≤ 1) :
    ∃ Q : Fin (k+1) → ℝ,
      Monotone Q ∧ (∀ j, Q j ∈ Set.Icc 0 1) ∧
      extendedQuantileParisi k β Q-
        (β^2/4)*(20*((k:ℝ)/Real.sqrt ((N:ℝ)*(β^2*η))+1/Real.sqrt (k:ℝ))+
          2*(((k+1:ℕ):ℝ)*η)*(1+((k+1:ℕ):ℝ)*η)+4*(((k+1:ℕ):ℝ)*η)) ≤
        (∫ J, logPartition β J ∂disorderLaw N)/(N:ℝ) := by
  obtain ⟨Q,hgap,hupper,H⟩ := exists_quenched_scalar_lower_bound hN hk hβ hη hsmall
  have hpos (j : Fin (k+1)) : 0 < cumulativeGapMap k Q j := hη.trans_le (hgap j)
  have ha := clampQuantile_admissible Q (fun j => (hpos j).le)
  refine ⟨clampQuantile Q,ha.1,ha.2,?_⟩
  have HC := extendedQuantileParisi_clamp_le β Q hpos (by positivity) hupper
  linarith
end SK.Analytic

end
end

end

end OAI
