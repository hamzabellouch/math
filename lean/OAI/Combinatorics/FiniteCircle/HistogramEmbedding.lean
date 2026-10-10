import OAI.Combinatorics.FiniteCircle.Separation

namespace OAI

namespace FiniteCircle

open scoped BigOperators List
open scoped ComplexConjugate
open RCLike Module
open Classical

theorem histogram_embedding_step {α : Type*} [Fintype α] (a : α) {m M : ℕ}
    (hm : 0 < m) (b : ℕ) (F : List.Vector α m → Fin M → ℝ) (Λ : ℝ) (hΛ : 0 ≤ Λ)
    (hFlo : ∀ u v, (deficit u.val v.val : ℝ) ≤ coordDist F u v)
    (hFhi : ∀ u v, coordDist F u v ≤ Λ * deficit u.val v.val) :
    ∃ M' : ℕ, ∃ F' : List.Vector α (b*m) → Fin M' → ℝ,
      ∀ x y, (deficit x.val y.val : ℝ) ≤ coordDist F' x y ∧
        coordDist F' x y ≤ (16 * (Nat.log 2 m + 1) *
          (b + 16 * Real.log ((m:ℝ)+1) * Λ)) * deficit x.val y.val := by
  classical
  let X := List.Vector α m
  let : DecidableEq X := Classical.decEq X
  let Ω := PartitionSpace X
  let K := Nat.log 2 m + 1
  have hav (k : Fin K) : 1 ≤ 2^k.val ∧ 2^k.val ≤ m := by
    refine ⟨?_, Nat.pow_le_of_le_log hm.ne' (by have := k.isLt; dsimp [K] at *; omega)⟩
    have hp : 0 < 2^k.val := pow_pos (by norm_num) _
    omega
  have hp (k : Fin K) := finite_partition (finite_l1_cuts F) (partitionRate (2^k.val))
    (partitionRate_nonneg (2^k.val))
  choose μ label he using hp
  let I := (Fin b × Fin K) × (Ω × Ω)
  let Φ : List α → I → ℝ := fun x i =>
    4 * histMap (μ i.1.2) (label i.1.2) (windowWords a x (i.1.1*m) m (2^i.1.2.val)) i.2
  have hΦ (x y : List α) : coordDist Φ x y =
      4 * ∑ j : Fin b, ∑ k : Fin K, (μ k).expect (fun ω => histDist (label k ω)
        (windowWords a x (j*m) m (2^k.val)) (windowWords a y (j*m) m (2^k.val))) := by
    unfold coordDist
    rw [Fintype.sum_prod_type]
    simp only [Φ, ← mul_sub, abs_mul, show |(4:ℝ)| = 4 by norm_num]
    simp_rw [← Finset.mul_sum, histMap_distance]
    rw [Fintype.sum_prod_type]
  have hnonneg (x y : List α) (j : Fin b) (k : Fin K) :
      0 ≤ (μ k).expect (fun ω => histDist (label k ω)
        (windowWords a x (j*m) m (2^k.val)) (windowWords a y (j*m) m (2^k.val))) :=
    (μ k).expect_nonneg (fun _ => histDist_nonneg _ _ _)
  have hlo (x y : List.Vector α (b*m)) : (deficit x.val y.val : ℝ) ≤ coordDist Φ x.val y.val := by
    have hx (j : Fin b) : (segment x.val (j*m) m).length = m := by
      apply length_segment
      rw [x.property]
      have h := Nat.mul_le_mul_right m (Nat.succ_le_of_lt j.isLt)
      simpa only [Nat.succ_mul] using h
    have hy (j : Fin b) : (segment y.val (j*m) m).length = m := by
      apply length_segment
      rw [y.property]
      have h := Nat.mul_le_mul_right m (Nat.succ_le_of_lt j.isLt)
      simpa only [Nat.succ_mul] using h
    have hblock (j : Fin b) : (deficit (segment x.val (j*m) m) (segment y.val (j*m) m) : ℝ) ≤
        4 * ∑ k : Fin K, (μ k).expect (fun ω => histDist (label k ω)
          (windowWords a x.val (j*m) m (2^k.val)) (windowWords a y.val (j*m) m (2^k.val))) := by
      let q := deficit (segment x.val (j*m) m) (segment y.val (j*m) m)
      by_cases hq : q = 0
      · change (q:ℝ) ≤ _
        rw [hq, Nat.cast_zero]
        exact mul_nonneg (by norm_num) (Finset.sum_nonneg (fun k _ => hnonneg x.val y.val j k))
      · have hqm : q ≤ m := by dsimp [q, deficit]; rw [hx]; omega
        obtain ⟨k, hs, hsm, hqs, hsq⟩ := exists_separating_scale (Nat.pos_of_ne_zero hq) hqm
        have hsep := block_histogram_lower a F hFlo (μ k) (label k) (he k)
          (hx j) (hy j) hs hsm hsq
        rw [windowWords_segment a x.val hs hsm, windowWords_segment a y.val hs hsm] at hsep
        calc
          _ = (q:ℝ) := rfl
          _ ≤ 4 * (2^k.val : ℕ) := by exact_mod_cast hqs
          _ ≤ 4 * (μ k).expect (fun ω => histDist (label k ω)
              (windowWords a x.val (j*m) m (2^k.val)) (windowWords a y.val (j*m) m (2^k.val))) := by linarith
          _ ≤ _ := mul_le_mul_of_nonneg_left
            (Finset.single_le_sum (fun k _ => hnonneg x.val y.val j k) (Finset.mem_univ _)) (by norm_num)
    calc
      _ ≤ ∑ j : Fin b, (deficit (segment x.val (j*m) m) (segment y.val (j*m) m) : ℝ) := by
        exact_mod_cast deficit_le_sum_blocks x.property y.property
      _ ≤ ∑ j : Fin b, 4 * ∑ k : Fin K, (μ k).expect (fun ω => histDist (label k ω)
          (windowWords a x.val (j*m) m (2^k.val)) (windowWords a y.val (j*m) m (2^k.val))) :=
        Finset.sum_le_sum (fun j _ => hblock j)
      _ = _ := by rw [hΦ, Finset.mul_sum]
  have hmove (x y : List α) (hxy : Slide x y) : coordDist Φ x y ≤
      4*K * (2*b + 32 * Real.log ((m:ℝ)+1) * Λ) := by
    rw [hΦ, Finset.sum_comm]
    calc
      _ ≤ 4 * ∑ k : Fin K, (2*b + 32 * Real.log ((m:ℝ)+1) * Λ) := by
        apply mul_le_mul_of_nonneg_left _ (by norm_num)
        apply Finset.sum_le_sum
        intro k _
        refine (histogram_slide_bound a F Λ hΛ hFhi (μ k) (label k) (he k) hxy b
          (hav k).1 (hav k).2).trans ?_
        have hlog : Real.log (((2^k.val : ℕ):ℝ)+1) ≤ Real.log ((m:ℝ)+1) :=
          Real.log_le_log (by positivity) (by exact_mod_cast Nat.add_le_add_right (hav k).2 1)
        gcongr
      _ = _ := by simp; ring
  let e := Fintype.equivFin I
  let F' : List.Vector α (b*m) → Fin (Fintype.card I) → ℝ := fun x i => Φ x.val (e.symm i)
  have hdist (x y : List.Vector α (b*m)) : coordDist F' x y = coordDist Φ x.val y.val :=
    e.symm.sum_comp (fun i => |Φ x.val i - Φ y.val i|)
  refine ⟨Fintype.card I, F', fun x y => ⟨?_, ?_⟩⟩
  · rw [hdist]
    exact hlo x y
  · rw [hdist]
    have hp := (exists_slidePath a (x.property.trans y.property.symm)).coordDist_le Φ
      (4*K * (2*b + 32 * Real.log ((m:ℝ)+1) * Λ)) hmove
    refine hp.trans_eq ?_
    push_cast
    dsimp [K]
    push_cast
    ring

end FiniteCircle

end OAI
