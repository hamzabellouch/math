import OAI.Analysis.MarkovType.JConvexitySquareAverage
import Mathlib.Analysis.Normed.Lp.lpSpace
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.Algebra.InfiniteSum.Ring

namespace OAI

namespace MarkovSuperreflexivity

open scoped BigOperators ENNReal

universe u

variable (X : Type u) [NormedAddCommGroup X] [sectionNormedSpaceℝX : NormedSpace ℝ X]

instance sequenceL2ExponentAtLeastOne : Fact (1 ≤ (2 : ℝ≥0∞)) := ⟨by norm_num⟩

abbrev SequenceL2 := lp (fun _ : ℕ => X) (2 : ℝ≥0∞)

variable {X}

omit sectionNormedSpaceℝX in
theorem sequenceL2_completeSpace [NormedSpace ℝ X] [CompleteSpace X] : CompleteSpace (SequenceL2 X) :=
  inferInstance

omit sectionNormedSpaceℝX in
theorem sequenceL2_norm_sq [NormedSpace ℝ X] (f : SequenceL2 X) :
    ‖f‖ ^ 2 = ∑' k : ℕ, ‖f k‖ ^ 2 := by
  simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using
    lp.norm_rpow_eq_tsum (p := (2 : ℝ≥0∞)) (by norm_num) f

omit sectionNormedSpaceℝX in
theorem sequenceL2_hasSum_norm_sq [NormedSpace ℝ X] (f : SequenceL2 X) :
    HasSum (fun k : ℕ => ‖f k‖ ^ 2) (‖f‖ ^ 2) := by
  simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using
    lp.hasSum_norm (p := (2 : ℝ≥0∞)) (by norm_num) f

@[simp] theorem sequenceL2_cutSum_apply {n : ℕ} (f : Fin n → SequenceL2 X)
    (r : Fin n) (k : ℕ) :
    (cutSum f r) k = cutSum (fun j => f j k) r := by
  let ev : SequenceL2 X →+ X :=
    { toFun := fun x => x k
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  change ev (∑ j : Fin n, cutSign r j • f j) =
    ∑ j : Fin n, cutSign r j • f j k
  exact (map_sum ev (fun j : Fin n => cutSign r j • f j) Finset.univ).trans
    (Finset.sum_congr rfl (fun _ _ => rfl))

theorem squareAverage_sequenceL2 {n : ℕ} {α : ℝ}
    (h : ∀ x : Fin n → X,
      (n : ℝ)⁻¹ * (∑ r, ‖cutSum x r‖ ^ 2)
        ≤ α ^ 2 * (n : ℝ) * ∑ j, ‖x j‖ ^ 2)
    (f : Fin n → SequenceL2 X) :
    (n : ℝ)⁻¹ * (∑ r, ‖cutSum f r‖ ^ 2)
      ≤ α ^ 2 * (n : ℝ) * ∑ j, ‖f j‖ ^ 2 := by
  have hleft : HasSum
      (fun k : ℕ => (n : ℝ)⁻¹ * ∑ r, ‖(cutSum f r) k‖ ^ 2)
      ((n : ℝ)⁻¹ * ∑ r, ‖cutSum f r‖ ^ 2) :=
    (hasSum_sum (s := Finset.univ)
      (fun r _ => sequenceL2_hasSum_norm_sq (cutSum f r))).mul_left (n : ℝ)⁻¹
  have hright : HasSum
      (fun k : ℕ => (α ^ 2 * (n : ℝ)) * ∑ j, ‖f j k‖ ^ 2)
      ((α ^ 2 * (n : ℝ)) * ∑ j, ‖f j‖ ^ 2) :=
    (hasSum_sum (s := Finset.univ)
      (fun j _ => sequenceL2_hasSum_norm_sq (f j))).mul_left (α ^ 2 * (n : ℝ))
  apply hasSum_le _ hleft hright
  intro k
  simpa only [sequenceL2_cutSum_apply] using h (fun j => f j k)

theorem AmbientJConvex.sequenceL2 (h : AmbientJConvex X) :
    AmbientJConvex (SequenceL2 X) := by
  obtain ⟨n, hn, α, hα0, hα1, haverage⟩ :=
    JConvex.squareAverage (p := normSeminorm ℝ X) h
  have hnpos : 0 < n := lt_of_lt_of_le (by decide : 0 < 2) hn
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hnpos
  have hbase : ∀ x : Fin n → X,
      (n : ℝ)⁻¹ * (∑ r, ‖cutSum x r‖ ^ 2)
        ≤ α ^ 2 * (n : ℝ) * ∑ j, ‖x j‖ ^ 2 := haverage
  let ρ : ℝ := (1 + α) / 2
  have hρ0 : 0 < ρ := by dsimp [ρ]; linarith
  have hρ1 : ρ < 1 := by dsimp [ρ]; linarith
  have hαρ : α ≤ ρ := by dsimp [ρ]; linarith
  have hsqαρ : α ^ 2 ≤ ρ ^ 2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hαρ) (add_nonneg hρ0.le hα0)]
  refine ⟨n, hn, 1 - ρ, by linarith, by linarith, ?_⟩
  intro f hf
  change ∃ r : Fin n, ‖cutSum f r‖ ≤ (n : ℝ) * (1 - (1 - ρ))
  have hnorm : ∀ j, ‖f j‖ ≤ 1 := hf
  have hQ : (∑ j, ‖f j‖ ^ 2) ≤ (n : ℝ) := by
    have heach : ∀ j, ‖f j‖ ^ 2 ≤ (1 : ℝ) := by
      intro j
      nlinarith [mul_nonneg (sub_nonneg.mpr (hnorm j))
        (add_nonneg (by norm_num : (0 : ℝ) ≤ 1) (norm_nonneg (f j)))]
    simpa using Finset.sum_le_sum (fun j (_ : j ∈ Finset.univ) => heach j)
  have havg := squareAverage_sequenceL2 hbase f
  have havgρ : (n : ℝ)⁻¹ * (∑ r, ‖cutSum f r‖ ^ 2) ≤ (ρ * (n : ℝ)) ^ 2 := by
    calc
      (n : ℝ)⁻¹ * (∑ r, ‖cutSum f r‖ ^ 2)
          ≤ α ^ 2 * (n : ℝ) * ∑ j, ‖f j‖ ^ 2 := havg
      _ ≤ α ^ 2 * (n : ℝ) * (n : ℝ) :=
        mul_le_mul_of_nonneg_left hQ (mul_nonneg (sq_nonneg α) hnR.le)
      _ = α ^ 2 * (n : ℝ) ^ 2 := by ring
      _ ≤ ρ ^ 2 * (n : ℝ) ^ 2 := mul_le_mul_of_nonneg_right hsqαρ (sq_nonneg _)
      _ = (ρ * (n : ℝ)) ^ 2 := by ring
  have hupper : (∑ r, ‖cutSum f r‖ ^ 2) ≤ (n : ℝ) * (ρ * (n : ℝ)) ^ 2 := by
    calc
      (∑ r, ‖cutSum f r‖ ^ 2)
          = (n : ℝ) * ((n : ℝ)⁻¹ * ∑ r, ‖cutSum f r‖ ^ 2) := by
        rw [← mul_assoc, mul_inv_cancel₀ (ne_of_gt hnR), one_mul]
      _ ≤ (n : ℝ) * (ρ * (n : ℝ)) ^ 2 := mul_le_mul_of_nonneg_left havgρ hnR.le
  by_contra hnone
  have hbad : ∀ r : Fin n, ρ * (n : ℝ) < ‖cutSum f r‖ := by
    intro r
    apply lt_of_not_ge
    intro hr
    apply hnone
    refine ⟨r, ?_⟩
    nlinarith only [hr]
  have hbadSq : ∀ r : Fin n, (ρ * (n : ℝ)) ^ 2 < ‖cutSum f r‖ ^ 2 := by
    intro r
    have hp : 0 < ‖cutSum f r‖ + ρ * (n : ℝ) :=
      add_pos_of_nonneg_of_pos (norm_nonneg _) (mul_pos hρ0 hnR)
    nlinarith [mul_pos (sub_pos.mpr (hbad r)) hp]
  have hstrict : (n : ℝ) * (ρ * (n : ℝ)) ^ 2 < ∑ r, ‖cutSum f r‖ ^ 2 := by
    calc
      (n : ℝ) * (ρ * (n : ℝ)) ^ 2 = ∑ _r : Fin n, (ρ * (n : ℝ)) ^ 2 := by simp
      _ < ∑ r, ‖cutSum f r‖ ^ 2 :=
        Finset.sum_lt_sum (fun r _ => (hbadSq r).le)
          ⟨⟨0, hnpos⟩, Finset.mem_univ _, hbadSq _⟩
  exact (not_lt_of_ge hupper) hstrict

end MarkovSuperreflexivity

end OAI
