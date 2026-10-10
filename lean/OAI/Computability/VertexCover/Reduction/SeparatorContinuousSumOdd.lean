import Mathlib
import OAI.Computability.VertexCover.Reduction.HighVectorsSeparated

namespace OAI

section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
namespace VertexCover.LabelCover

theorem norm_sum_le (Φ : LabelCover) {d : ℕ} {ι : Type*}
    (T : Finset ι) (f : ι → Φ.Coordinate d → ℝ) :
    Φ.compatibilityNorm (∑ i ∈ T, f i) ≤ ∑ i ∈ T, Φ.compatibilityNorm (f i) := by
  classical
  induction T using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    exact (Φ.norm_zero d).le
  | @insert i T hi ih =>
    simp only [Finset.sum_insert hi]
    exact (Φ.norm_add_le _ _).trans (add_le_add_right ih _)

theorem increment_sub (Φ : LabelCover) {d : ℕ} (i : Φ.Query d)
    (s t : Fin (Φ.WeightDimension d) → ℝ) :
    Φ.increment i (s-t) = Φ.increment i s - Φ.increment i t := by
  have hn : Φ.increment i (-t) = -Φ.increment i t := by
    ext p
    change Φ.increment i (fun k => -t k) p = -Φ.increment i t p
    have h := congrFun (Φ.increment_mul i (-1) t) p
    simpa only [neg_one_mul] using h
  rw [sub_eq_add_neg, Φ.increment_add, hn, sub_eq_add_neg]

noncomputable def continuousSum (Φ : LabelCover) {d : ℕ} (seed : Φ.Seeds d)
    (s : Fin d → Fin (Φ.WeightDimension d) → ℝ) : Φ.Coordinate d → ℝ :=
  ∑ j, Φ.increment (Φ.query seed j) (s j)

theorem sumVector_eq_continuousSum (Φ : LabelCover) {d : ℕ} (v : Φ.Vertex d) :
    Φ.sumVector v = Φ.continuousSum v.1 (fun j k => (gridRational d (v.2 j k) : ℝ)) := rfl

theorem continuousSum_neg (Φ : LabelCover) {d : ℕ} (seed : Φ.Seeds d)
    (s : Fin d → Fin (Φ.WeightDimension d) → ℝ) :
    Φ.continuousSum seed (-s) = -Φ.continuousSum seed s := by
  unfold continuousSum
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro j _
  ext p
  change Φ.increment (Φ.query seed j) (fun k => -s j k) p =
    -Φ.increment (Φ.query seed j) (s j) p
  have h := congrFun (Φ.increment_mul (Φ.query seed j) (-1) (s j)) p
  simpa only [neg_one_mul] using h

theorem continuousSum_sub_same_seed (Φ : LabelCover) {d : ℕ} (seed : Φ.Seeds d)
    (s t : Fin d → Fin (Φ.WeightDimension d) → ℝ) :
    Φ.continuousSum seed s - Φ.continuousSum seed t = Φ.continuousSum seed (s-t) := by
  simp only [continuousSum, ← Finset.sum_sub_distrib, Pi.sub_apply, increment_sub]

theorem continuousSum_close (Φ : LabelCover) {d : ℕ} (seed : Φ.Seeds d)
    (s t : Fin d → Fin (Φ.WeightDimension d) → ℝ) {b : ℝ} (hb : 0 ≤ b)
    (hclose : ∀ j k, |s j k - t j k| ≤ b) :
    Φ.compatibilityNorm (Φ.continuousSum seed s - Φ.continuousSum seed t) ≤ d*b := by
  rw [Φ.continuousSum_sub_same_seed]
  apply (Φ.norm_sum_le _ _).trans
  calc
    (∑ j, Φ.compatibilityNorm (Φ.increment (Φ.query seed j) ((s-t) j))) ≤
        ∑ _j : Fin d, b := by
      apply Finset.sum_le_sum
      intro j _
      exact Φ.increment_norm_le _ _ hb (hclose j)
    _ = d*b := by simp

def InWeightCube (Φ : LabelCover) {d : ℕ}
    (s : Fin d → Fin (Φ.WeightDimension d) → ℝ) : Prop :=
  ∀ j k, |s j k| ≤ 1

theorem continuousSum_change_blocks (Φ : LabelCover) {d : ℕ}
    (seed seed' : Φ.Seeds d) (s t : Fin d → Fin (Φ.WeightDimension d) → ℝ)
    (hs : Φ.InWeightCube s) (ht : Φ.InWeightCube t) (B : Finset (Fin d))
    (heq : ∀ j ∉ B, Φ.query seed j = Φ.query seed' j ∧ s j = t j) :
    Φ.compatibilityNorm (Φ.continuousSum seed s - Φ.continuousSum seed' t) ≤ 2*B.card := by
  classical
  unfold continuousSum
  rw [← Finset.sum_sub_distrib]
  apply (Φ.norm_sum_le _ _).trans
  calc
    (∑ j, Φ.compatibilityNorm
        (Φ.increment (Φ.query seed j) (s j) - Φ.increment (Φ.query seed' j) (t j))) ≤
        ∑ j : Fin d, if j ∈ B then (2 : ℝ) else 0 := by
      apply Finset.sum_le_sum
      intro j _
      by_cases hj : j ∈ B
      · rw [ite_eq_left hj]
        have hb := Φ.norm_sub_triangle (Φ.increment (Φ.query seed j) (s j)) 0
          (Φ.increment (Φ.query seed' j) (t j))
        have hh1 := Φ.increment_norm_le (Φ.query seed j) (s j) (by norm_num : (0:ℝ) ≤ 1) (hs j)
        have hh2 := Φ.increment_norm_le (Φ.query seed' j) (t j) (by norm_num : (0:ℝ) ≤ 1) (ht j)
        simp only [sub_zero, zero_sub, Φ.norm_neg] at hb
        linarith
      · obtain ⟨hq, hw⟩ := heq j hj
        rw [hq, hw, sub_self, ite_eq_right hj]
        exact (Φ.norm_zero d).le
    _ = 2*B.card := by simp [Finset.sum_ite_mem, mul_comm]

theorem separator_continuousSum_odd (Φ : LabelCover) {d : ℕ}
    (A : Finset (Φ.Coordinate d → ℝ)) (hA : A.Nonempty) (seed : Φ.Seeds d)
    (s : Fin d → Fin (Φ.WeightDimension d) → ℝ) :
    Φ.separator A hA (Φ.continuousSum seed (-s)) =
      -Φ.separator A hA (Φ.continuousSum seed s) := by
  rw [Φ.continuousSum_neg, Φ.separator_odd]

end VertexCover.LabelCover

end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
