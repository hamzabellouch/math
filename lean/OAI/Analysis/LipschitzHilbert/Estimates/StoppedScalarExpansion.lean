import OAI.Analysis.LipschitzHilbert.Trees.PathExpansion

namespace OAI

/-! Finite scalar algebra for a stopped path. The terminal coefficient is
retained, so a small positive terminal mass is never replaced by zero. -/

noncomputable section
open scoped BigOperators
namespace LipschitzHilbert
attribute [local instance] Classical.propDecidable

def stoppedScalarExpansion (active : ℕ → Prop) (beta terminal : ℕ → ℝ) : ℕ → ℕ → ℝ
  | 0,j => terminal j
  | n+1,j => if active j then beta j*stoppedScalarExpansion active beta terminal n (j+1)
      else terminal j

/-- Unroll up to the first inactive index, keeping its exact terminal value. -/
theorem stoppedScalarExpansion_eq (active : ℕ → Prop) (beta terminal : ℕ → ℝ)
    (count stop j : ℕ) (hstop : stop ≤ count)
    (ha : ∀ i < stop, active (j+i)) (hz : ¬active (j+stop)) :
    stoppedScalarExpansion active beta terminal count j =
      terminal (j+stop)*∏ i ∈ Finset.range stop, beta (j+i) := by
  induction stop generalizing count j with
  | zero =>
    have hz' : ¬active j := by simpa only [Nat.add_zero] using hz
    cases count <;> simp [stoppedScalarExpansion,hz']
  | succ stop ih =>
    cases count with
    | zero => omega
    | succ count =>
      have hactive : active j := by simpa using ha 0 (by omega)
      rw [stoppedScalarExpansion,ite_eq_left hactive]
      have ha' : ∀ i < stop, active ((j+1)+i) := by
        intro i hi
        simpa only [Nat.add_assoc,Nat.add_comm 1 i] using ha (i+1) (by omega)
      have hz' : ¬active ((j+1)+stop) := by
        simpa only [Nat.add_assoc,Nat.add_comm 1 stop] using hz
      rw [ih count (j+1) (by omega) ha' hz',Finset.prod_range_succ']
      have heq : (∏ i ∈ Finset.range stop, beta (j+(i+1))) =
          ∏ i ∈ Finset.range stop, beta (j+1+i) := by
        apply Finset.prod_congr rfl
        intro i _
        congr 1
        omega
      rw [heq]
      have hj : j+(stop+1) = j+1+stop := by omega
      rw [hj]
      simp only [Nat.add_zero]
      ring

/-- A normalized path reaches its final parent with probability at most
one. This is the scalar form of the subunit child transition bound. -/
theorem normalized_path_parent_bound (V D : ℕ → ℝ) (N : ℕ)
    (hV : ∀ j ≤ N, 0 < V j) (hD : ∀ j ≤ N, 0 < D j)
    (hchild : ∀ j < N, V (j+1) ≤ D j) :
    (∏ j ∈ Finset.range (N+1), V j/D j) ≤ V 0/D N := by
  induction N with
  | zero => simp
  | succ N ih =>
    have hprev := ih (fun j hj => hV j (by omega))
      (fun j hj => hD j (by omega)) (fun j hj => hchild j (by omega))
    rw [Finset.prod_range_succ]
    calc
      _ ≤ (V 0/D N)*(V (N+1)/D (N+1)) :=
        mul_le_mul_of_nonneg_right hprev (div_nonneg (hV (N+1) (by omega)).le (hD (N+1) le_rfl).le)
      _ = (V 0/D (N+1))*(V (N+1)/D N) := by ring
      _ ≤ V 0/D (N+1) := mul_le_of_le_one_right
        (div_nonneg (hV 0 (by omega)).le (hD (N+1) le_rfl).le)
        ((div_le_one (hD N (by omega))).mpr (hchild N (by omega)))

/-- An arbitrary terminal coefficient with a weight bound gives the
required per-top probability bound, with no depth factor. -/
theorem normalized_terminal_weight_bound (V D : ℕ → ℝ) (N : ℕ)
    (e C w : ℝ) (hV : ∀ j ≤ N, 0 < V j) (hD : ∀ j ≤ N, 0 < D j)
    (hchild : ∀ j < N, V (j+1) ≤ D j) (he : 0 ≤ e) (hCw : e ≤ C*w)
    (hfinal : 1 ≤ D N) :
    e*(∏ j ∈ Finset.range (N+1), V j/D j)/V 0 ≤ C*w := by
  have hp := normalized_path_parent_bound V D N hV hD hchild
  calc
    _ ≤ e*(V 0/D N)/V 0 :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hp he) (hV 0 (by omega)).le
    _ = e/D N := by field_simp [(hV 0 (by omega)).ne']
    _ ≤ e := div_le_self he hfinal
    _ ≤ C*w := hCw

end LipschitzHilbert

end

end OAI
