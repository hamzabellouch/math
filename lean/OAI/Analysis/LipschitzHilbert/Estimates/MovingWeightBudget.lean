import OAI.Analysis.LipschitzHilbert.Estimates.MovingExponentialWeights
import OAI.Analysis.LipschitzHilbert.Estimates.SegmentWeights

namespace OAI

/-! Finite endpoint transport from the actual logarithmic loss budget.
Small relative errors are summed against losses, without charging a fixed
error for every hierarchy level. -/

noncomputable section
open scoped BigOperators
namespace LipschitzHilbert

theorem exponential_weight_motion_from_increments (L M : ℕ → ℂ) (cost : ℕ → ℝ)
    (N : ℕ) (C D ε V : ℝ) (hD : 0 ≤ D) (hε : 0 ≤ ε) (hV : 0 ≤ V)
    (hL : ∀ j ≤ N, (L j).re ≤ C) (hM : ∀ j ≤ N, (M j).re ≤ C)
    (hzero : ‖M 0-L 0‖ ≤ D)
    (hcost : ∀ j < N, 0 ≤ cost j)
    (hincr : ∀ j < N, ‖L (j+1)-L j‖ ≤ cost j)
    (hmove : ∀ j < N, ‖(M (j+1)-M j)-(L (j+1)-L j)‖ ≤ ε*cost j)
    (hbudget : (∑ j ∈ Finset.range N, cost j) ≤ V) :
    ‖Complex.exp (M N)-Complex.exp (L N)‖ +
      (∑ j ∈ Finset.range N,
        ‖(Complex.exp (M (j+1))-Complex.exp (L (j+1)))-
          (Complex.exp (M j)-Complex.exp (L j))‖) ≤
      Real.exp C*((D+ε*V)+ε*V+(D+ε*V)*V) := by
  have hpartial (k : ℕ) (hk : k ≤ N) :
      ‖M k-L k‖ ≤ D+ε*(∑ j ∈ Finset.range k, cost j) := by
    induction k with
    | zero => simpa using hzero
    | succ k ih =>
      have hkN : k < N := by omega
      have heq : M (k+1)-L (k+1) = (M k-L k)+((M (k+1)-M k)-(L (k+1)-L k)) := by ring
      rw [heq, Finset.sum_range_succ]
      calc
        _ ≤ ‖M k-L k‖+‖(M (k+1)-M k)-(L (k+1)-L k)‖ := norm_add_le _ _
        _ ≤ (D+ε*(∑ j ∈ Finset.range k, cost j))+ε*cost k :=
          add_le_add (ih (by omega)) (hmove k hkN)
        _ = _ := by ring
  have hdiff (k : ℕ) (hk : k ≤ N) : ‖M k-L k‖ ≤ D+ε*V := by
    apply (hpartial k hk).trans
    apply add_le_add le_rfl
    apply mul_le_mul_of_nonneg_left _ hε
    exact (Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hk)
      (fun j hj _ => hcost j (Finset.mem_range.mp hj))).trans hbudget
  apply exponential_sequence_difference_variation L M N C (D+ε*V) V (ε*V)
    (by positivity) hL hM hdiff
  · exact (Finset.sum_le_sum (fun j hj => hincr j (Finset.mem_range.mp hj))).trans hbudget
  · calc
      _ ≤ ∑ j ∈ Finset.range N, ε*cost j :=
        Finset.sum_le_sum (fun j hj => hmove j (Finset.mem_range.mp hj))
      _ = ε*(∑ j ∈ Finset.range N, cost j) := (Finset.mul_sum _ _ _).symm
      _ ≤ ε*V := mul_le_mul_of_nonneg_left hbudget hε

/-- The same transport bound on any interval of later endpoints. -/
theorem exponential_weight_motion_on_interval (L M : ℕ → ℂ) (cost : ℕ → ℝ)
    (start N : ℕ) (hstart : start ≤ N) (C D ε V : ℝ)
    (hD : 0 ≤ D) (hε : 0 ≤ ε) (hV : 0 ≤ V)
    (hL : ∀ j, start ≤ j → j ≤ N → (L j).re ≤ C)
    (hM : ∀ j, start ≤ j → j ≤ N → (M j).re ≤ C)
    (hzero : ‖M start-L start‖ ≤ D)
    (hcost : ∀ j ∈ Finset.Ico start N, 0 ≤ cost j)
    (hincr : ∀ j ∈ Finset.Ico start N, ‖L (j+1)-L j‖ ≤ cost j)
    (hmove : ∀ j ∈ Finset.Ico start N,
      ‖(M (j+1)-M j)-(L (j+1)-L j)‖ ≤ ε*cost j)
    (hbudget : (∑ j ∈ Finset.Ico start N, cost j) ≤ V) :
    ‖Complex.exp (M N)-Complex.exp (L N)‖ +
      (∑ j ∈ Finset.Ico start N,
        ‖(Complex.exp (M (j+1))-Complex.exp (L (j+1)))-
          (Complex.exp (M j)-Complex.exp (L j))‖) ≤
      Real.exp C*((D+ε*V)+ε*V+(D+ε*V)*V) := by
  have hshift (j : ℕ) (hj : j < N-start) : start+j ∈ Finset.Ico start N :=
    Finset.mem_Ico.mpr ⟨by omega, by omega⟩
  have hb : (∑ j ∈ Finset.range (N-start), cost (start+j)) ≤ V := by
    simpa only [Finset.sum_Ico_eq_sum_range] using hbudget
  have h := exponential_weight_motion_from_increments
    (fun j => L (start+j)) (fun j => M (start+j)) (fun j => cost (start+j))
    (N-start) C D ε V hD hε hV
    (fun j hj => hL _ (by omega) (by omega))
    (fun j hj => hM _ (by omega) (by omega)) (by simpa using hzero)
    (fun j hj => hcost _ (hshift j hj))
    (fun j hj => by simpa only [Nat.add_assoc] using hincr _ (hshift j hj))
    (fun j hj => by simpa only [Nat.add_assoc] using hmove _ (hshift j hj)) hb
  have hend : start+(N-start)=N := by omega
  simpa only [Finset.sum_Ico_eq_sum_range, hend, Nat.add_assoc] using h

/-- A moving endpoint increment is controlled by relative errors in the
parent loss and boundary loss, with exactly the original weighted cost. -/
theorem segmentLog_increment_motion (n n' R R' : ℕ → ℝ) (phase : ℕ → ℂ)
    (a ε Z : ℝ) (start j : ℕ) (hs : start ≤ j)
    (ha : 0 ≤ a) (hZ : 0 ≤ Z)
    (hn : 0 < n j) (hn1 : 0 < n (j+1))
    (hn' : 0 < n' j) (hn1' : 0 < n' (j+1))
    (hP : |Real.log (n' j/n' (j+1))-Real.log (n j/n (j+1))| ≤
      ε*Real.log (n j/n (j+1)))
    (hR : |R' j-R j| ≤ ε*R j) (hz : ‖phase j‖ ≤ Z) :
    ‖(segmentLog n' R' phase a start (j+1)-segmentLog n' R' phase a start j)-
      (segmentLog n R phase a start (j+1)-segmentLog n R phase a start j)‖ ≤
      ε*(a*Real.log (n j/n (j+1))+Z*R j) := by
  rw [segmentLog_increment n' R' phase a start j hs hn' hn1',
    segmentLog_increment n R phase a start j hs hn hn1]
  have heq : (((a*Real.log (n' j/n' (j+1)):ℝ):ℂ)-phase j*(R' j:ℂ))-
      (((a*Real.log (n j/n (j+1)):ℝ):ℂ)-phase j*(R j:ℂ)) =
      (a:ℂ)*((Real.log (n' j/n' (j+1))-Real.log (n j/n (j+1)):ℝ):ℂ)-
        phase j*((R' j-R j:ℝ):ℂ) := by push_cast; ring
  rw [heq]
  calc
    _ ≤ ‖(a:ℂ)*((Real.log (n' j/n' (j+1))-Real.log (n j/n (j+1)):ℝ):ℂ)‖+
        ‖phase j*((R' j-R j:ℝ):ℂ)‖ := norm_sub_le _ _
    _ = a*|Real.log (n' j/n' (j+1))-Real.log (n j/n (j+1))|+
        ‖phase j‖*|R' j-R j| := by
      rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Complex.norm_real,
        Real.norm_eq_abs, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg ha]
    _ ≤ a*(ε*Real.log (n j/n (j+1)))+Z*(ε*R j) := add_le_add
      (mul_le_mul_of_nonneg_left hP ha)
      (mul_le_mul hz hR (abs_nonneg _) hZ)
    _ = _ := by ring

end LipschitzHilbert

end

end OAI
