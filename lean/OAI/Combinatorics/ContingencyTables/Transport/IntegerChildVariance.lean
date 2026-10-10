import OAI.Combinatorics.ContingencyTables.Transport.IntegerChildLogConcavity

namespace OAI

/-! # Between-child variance from raw integer transport

The no-valley bound for child masses turns adjacent transport into a
bound on every pair of child means. Finite Cauchy--Schwarz and the exact
weighted pair formula then bound the between-child variance.
-/

namespace ContingencyTables.IntegerWeightedTransport

open scoped BigOperators Classical
open CommonBasesFPRAS

lemma range_difference_sum (H : ℕ → ℝ) (a n : ℕ) :
    (∑ j ∈ Finset.range n, (H (a+j)-H (a+j+1)))=H a-H (a+n) := by
  induction n with
  | zero => simp
  | succ n ih => rw [Finset.sum_range_succ,ih]; simp only [Nat.add_succ]; ring

lemma path_square (H : ℕ → ℝ) (a n : ℕ) :
    (H a-H (a+n))^2 ≤ (n:ℝ)*∑ j ∈ Finset.range n, (H (a+j)-H (a+j+1))^2 := by
  have h := Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul (Finset.range n)
    (r := fun j => H (a+j)-H (a+j+1)) (f := fun _ => (1:ℝ))
    (g := fun j => (H (a+j)-H (a+j+1))^2)
    (fun _ _ => zero_le_one) (fun _ _ => sq_nonneg _) (fun _ _ => by simp)
  simpa only [range_difference_sum,Finset.sum_const,Finset.card_range,nsmul_eq_mul,mul_one] using h

lemma minimum_pair_coefficient (x y Z : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y)
    (hZ : 0 < Z) (hxZ : x ≤ Z) (hyZ : y ≤ Z) : x*y/Z ≤ min x y := by
  apply le_min
  · apply (div_le_iff₀ hZ).mpr
    exact mul_le_mul_of_nonneg_left hyZ hx
  · apply (div_le_iff₀ hZ).mpr
    simpa only [mul_comm] using mul_le_mul_of_nonneg_left hxZ hy

lemma child_pair_path_bound (z H : ℕ → ℝ) (U a b : ℕ) (Z A E : ℝ)
    (hz : ∀ j ≤ U, 0 ≤ z j) (hZ : 0 < Z) (hzZ : ∀ j ≤ U, z j ≤ Z)
    (hA : 0 ≤ A) (hE : 0 ≤ E)
    (hminimum : ∀ a j b, a ≤ j → j ≤ b → b ≤ U → min (z a) (z b) ≤ z j)
    (hadj : ∀ j, j < U → min (z j) (z (j+1))*(H j-H (j+1))^2 ≤ A*E)
    (ha : a ≤ U) (hb : b ≤ U) :
    z a*z b/Z*(H a-H b)^2 ≤ (U:ℝ)^2*A*E := by
  wlog hab : a ≤ b generalizing a b
  · have h := this b a hb ha (by omega)
    have hsq : (H b-H a)^2=(H a-H b)^2 := by ring
    simpa only [mul_comm (z b) (z a),hsq] using h
  have hmin : 0 ≤ min (z a) (z b) := le_min (hz a ha) (hz b hb)
  have hn : b-a ≤ U := by omega
  have hpath := path_square H a (b-a)
  rw [Nat.add_sub_of_le hab] at hpath
  have hcoef := minimum_pair_coefficient (z a) (z b) Z (hz a ha) (hz b hb)
    hZ (hzZ a ha) (hzZ b hb)
  have hsteps : ∑ j ∈ Finset.range (b-a),
      min (z a) (z b)*(H (a+j)-H (a+j+1))^2 ≤ (b-a:ℕ)* (A*E) := by
    calc
      _ ≤ ∑ _j ∈ Finset.range (b-a), A*E := by
        apply Finset.sum_le_sum
        intro j hj
        have hjn := Finset.mem_range.mp hj
        have hjU : a+j < U := by omega
        have hm : min (z a) (z b) ≤ min (z (a+j)) (z (a+j+1)) := by
          apply le_min
          · exact hminimum a (a+j) b (by omega) (by omega) hb
          · exact hminimum a (a+j+1) b (by omega) (by omega) hb
        exact (mul_le_mul_of_nonneg_right hm (sq_nonneg _)).trans (hadj (a+j) hjU)
      _ = _ := by simp
  have hnreal : (b-a:ℕ) ≤ (U:ℝ) := by exact_mod_cast hn
  have hAE : 0 ≤ A*E := mul_nonneg hA hE
  calc
    _ ≤ min (z a) (z b)*(H a-H b)^2 := mul_le_mul_of_nonneg_right hcoef (sq_nonneg _)
    _ ≤ min (z a) (z b)*((b-a:ℕ)*
        ∑ j ∈ Finset.range (b-a), (H (a+j)-H (a+j+1))^2) :=
      mul_le_mul_of_nonneg_left hpath hmin
    _ = (b-a:ℕ)*(∑ j ∈ Finset.range (b-a),
        min (z a) (z b)*(H (a+j)-H (a+j+1))^2) := by rw [←Finset.mul_sum]; ring
    _ ≤ (b-a:ℕ)*((b-a:ℕ)*(A*E)) :=
      mul_le_mul_of_nonneg_left hsteps (Nat.cast_nonneg _)
    _ ≤ (U:ℝ)*((U:ℝ)*(A*E)) := by
      gcongr
    _ = _ := by ring

lemma finite_pair_square {X : Type*} [Fintype X] (w H : X → ℝ) :
    (∑ x, ∑ y, w x*w y*(H x-H y)^2)=
      2*(∑ x, w x)*(∑ x, w x*(H x)^2)-2*(∑ x, w x*H x)^2 := by
  have he (x y : X) : w x*w y*(H x-H y)^2=
      (w x*(H x)^2)*w y+w x*(w y*(H y)^2)-2*((w x*H x)*(w y*H y)) := by ring
  have hinner (x : X) : (∑ y, w x*w y*(H x-H y)^2)=
      (w x*(H x)^2)*(∑ y, w y)+w x*(∑ y, w y*(H y)^2)-
        2*((w x*H x)*(∑ y, w y*H y)) := by
    simp_rw [he,Finset.sum_sub_distrib,Finset.sum_add_distrib,←Finset.mul_sum]
  simp_rw [hinner,Finset.sum_sub_distrib,Finset.sum_add_distrib,←Finset.mul_sum,←Finset.sum_mul]
  ring

/-- Exact unnormalized weighted variance pair formula. -/
lemma finite_weighted_variance_pair {X : Type*} [Fintype X] (w H : X → ℝ)
    (hZ : 0 < ∑ x, w x) :
    (∑ x, w x*(H x-(∑ y, w y*H y)/(∑ y, w y))^2)=
      (∑ x, ∑ y, w x*w y/(∑ k, w k)*(H x-H y)^2)/2 := by
  have hc := finite_center_at_mean Finset.univ w H (ne_of_gt hZ)
  rw [hc]
  have he : (∑ x, ∑ y, w x*w y/(∑ k, w k)*(H x-H y)^2)=
      (∑ x, ∑ y, w x*w y*(H x-H y)^2)/(∑ k, w k) := by
    simp_rw [div_mul_eq_mul_div,←Finset.sum_div]
  rw [he,finite_pair_square]
  field_simp

/-- The paper's between-child estimate, including zero-mass children. -/
theorem child_variance_bound (z H : ℕ → ℝ) (U : ℕ) (A E : ℝ)
    (hz : ∀ j ≤ U, 0 ≤ z j) (hZ : 0 < ∑ j : Fin (U+1), z j.val)
    (hA : 0 ≤ A) (hE : 0 ≤ E)
    (hminimum : ∀ a j b, a ≤ j → j ≤ b → b ≤ U → min (z a) (z b) ≤ z j)
    (hadj : ∀ j, j < U → min (z j) (z (j+1))*(H j-H (j+1))^2 ≤ A*E) :
    (∑ j : Fin (U+1), z j.val*(H j.val-
      (∑ k : Fin (U+1), z k.val*H k.val)/(∑ k : Fin (U+1), z k.val))^2) ≤
      ((U:ℝ)+1)^4*A*E := by
  have hzZ (j : ℕ) (hj : j ≤ U) : z j ≤ ∑ k : Fin (U+1), z k.val := by
    exact Finset.single_le_sum (fun k _ => hz k.val (by omega))
      (Finset.mem_univ (⟨j,by omega⟩ : Fin (U+1)))
  rw [finite_weighted_variance_pair _ _ hZ]
  have hp (a b : Fin (U+1)) := child_pair_path_bound z H U a.val b.val _ A E hz hZ hzZ
    hA hE hminimum hadj (by omega) (by omega)
  have hsum := Finset.sum_le_sum (s := Finset.univ) (fun a _ =>
    Finset.sum_le_sum (s := Finset.univ) (fun b _ => hp a b))
  have hsum' : (∑ a : Fin (U+1), ∑ b : Fin (U+1),
      z a.val*z b.val/(∑ k : Fin (U+1), z k.val)*(H a.val-H b.val)^2) ≤
      ((U:ℝ)+1)^2*(U:ℝ)^2*A*E := by
    simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,
      Nat.cast_add,Nat.cast_one] at hsum
    convert hsum using 1; ring
  have hAE : 0 ≤ A*E := mul_nonneg hA hE
  have hU : 0 ≤ (U:ℝ) := Nat.cast_nonneg _
  have hpow : ((U:ℝ)+1)^2*(U:ℝ)^2 ≤ ((U:ℝ)+1)^4 := by
    have hsq : (U:ℝ)^2 ≤ ((U:ℝ)+1)^2 := by nlinarith
    convert mul_le_mul_of_nonneg_left hsq (sq_nonneg ((U:ℝ)+1)) using 1; ring
  have hb := mul_le_mul_of_nonneg_right hpow hAE
  nlinarith

end ContingencyTables.IntegerWeightedTransport

end OAI
