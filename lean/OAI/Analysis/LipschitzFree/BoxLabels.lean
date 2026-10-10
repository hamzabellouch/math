import Mathlib

namespace OAI

/-!
# Finite box labels with the supremum metric
-/

noncomputable section
open scoped BigOperators ENNReal

noncomputable section
namespace DiscreteFree
open scoped Classical

def BoxLabel (C : Type*) (cap : ℕ) := C → Fin (cap+1)

instance (C : Type*) [Fintype C] (cap : ℕ) : Fintype (BoxLabel C cap) :=
  inferInstanceAs (Fintype (C → Fin (cap+1)))

namespace BoxLabel
variable {C : Type*} [Fintype C] {cap : ℕ}

def distance (a b : BoxLabel C cap) : ℕ := Finset.univ.sup (fun i => Nat.dist (a i).val (b i).val)

theorem coord_le (a b : BoxLabel C cap) (i : C) :
    Nat.dist (a i).val (b i).val ≤ distance a b := Finset.le_sup (f := fun i => Nat.dist (a i).val (b i).val) (Finset.mem_univ i)

theorem distance_le_iff {a b : BoxLabel C cap} {n : ℕ} :
    distance a b ≤ n ↔ ∀ i, Nat.dist (a i).val (b i).val ≤ n := by
  simp [distance, Finset.sup_le_iff]

@[simp] theorem distance_self (a : BoxLabel C cap) : distance a a = 0 := by
  simp [distance]

theorem distance_comm (a b : BoxLabel C cap) : distance a b = distance b a := by
  simp only [distance, Nat.dist_comm]

theorem distance_triangle (a b c : BoxLabel C cap) :
    distance a c ≤ distance a b + distance b c := by
  rw [distance_le_iff]
  intro i
  exact (Nat.dist.triangle_inequality _ _ _).trans (Nat.add_le_add (coord_le a b i) (coord_le b c i))

theorem eq_of_distance_zero {a b : BoxLabel C cap} (h : distance a b = 0) : a = b := by
  funext i
  apply Fin.ext
  exact Nat.eq_of_dist_eq_zero (Nat.eq_zero_of_le_zero ((coord_le a b i).trans_eq h))

theorem distance_bound (a b : BoxLabel C cap) : distance a b ≤ cap := by
  rw [distance_le_iff]
  intro i
  have ha := (a i).isLt
  have hb := (b i).isLt
  unfold Nat.dist
  omega

instance : MetricSpace (BoxLabel C cap) where
  dist a b := distance a b
  dist_self a := by simp
  dist_comm a b := by rw [distance_comm]
  dist_triangle a b c := by exact_mod_cast distance_triangle a b c
  eq_of_dist_eq_zero h := eq_of_distance_zero (by exact_mod_cast h)

@[simp] theorem dist_eq (a b : BoxLabel C cap) : dist a b = (distance a b : ℝ) := rfl

theorem cast_nat_dist (m n : ℕ) : (Nat.dist m n : ℝ) = |(m : ℝ) - n| := by
  unfold Nat.dist
  rcases le_total m n with h | h
  · have h' : (m : ℝ) ≤ n := by exact_mod_cast h
    rw [Nat.sub_eq_zero_of_le h, zero_add, Nat.cast_sub h, abs_of_nonpos (sub_nonpos.mpr h')]
    ring
  · have h' : (n : ℝ) ≤ m := by exact_mod_cast h
    rw [Nat.sub_eq_zero_of_le h, add_zero, Nat.cast_sub h, abs_of_nonneg (sub_nonneg.mpr h')]

theorem real_coord_le (a b : BoxLabel C cap) (i : C) :
    |((a i).val : ℝ) - (b i).val| ≤ dist a b := by
  rw [← cast_nat_dist, dist_eq]
  exact_mod_cast coord_le a b i

theorem dist_eq_real_sup (a b : BoxLabel C cap) :
    dist a b = dist (fun i => ((a i).val : ℝ)) (fun i => ((b i).val : ℝ)) := by
  apply le_antisymm
  · have hn : ∀ i, (Nat.dist (a i).val (b i).val : ℝ) ≤
        dist (fun i => ((a i).val : ℝ)) (fun i => ((b i).val : ℝ)) := by
      intro i
      have h := dist_le_pi_dist (fun i => ((a i).val : ℝ)) (fun i => ((b i).val : ℝ)) i
      simpa only [Real.dist_eq, cast_nat_dist] using h
    change ((Finset.univ.sup (fun i => Nat.dist (a i).val (b i).val) : ℕ) : ℝ) ≤ _
    apply Finset.sup_induction (p := fun n : ℕ => (n : ℝ) ≤
      dist (fun i => ((a i).val : ℝ)) (fun i => ((b i).val : ℝ)))
    · simpa only [Nat.bot_eq_zero, Nat.cast_zero] using (dist_nonneg :
        0 ≤ dist (fun i => ((a i).val : ℝ)) (fun i => ((b i).val : ℝ)))
    · intro m hm n hn
      change ((max m n : ℕ) : ℝ) ≤ _
      rw [Nat.cast_max]
      exact max_le hm hn
    · intro i _
      exact hn i
  · exact (dist_pi_le_iff dist_nonneg).mpr (fun i => by
      simpa only [Real.dist_eq] using real_coord_le a b i)

end BoxLabel
end DiscreteFree
end

end

end OAI
