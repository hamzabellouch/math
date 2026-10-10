import OAI.Combinatorics.BalancedRyser.Selection.PlaneSelectionOccupancy
import OAI.Combinatorics.BalancedRyser.Selection.SelectionProcessLaw

namespace OAI

open scoped BigOperators

namespace Balanced.Selection.Process

noncomputable section
attribute [local instance] Classical.propDecidable

variable {I V : Type*} [Fintype I] [Fintype V]

theorem noise_mean_eq_draw_mean (p : Parameters) (q : ℕ) (G : Input I V)
    (S : State I V) (f : I → V → ℝ) :
    (∑ r : Noise I V, noiseWeight p q G S r * f r.1 r.2.1) =
      ∑ i : I, ∑ v : V, drawWeight G S i v * f i v := by
  simp only [Noise, Fintype.sum_prod_type, noiseWeight]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro v hv
  calc
    (∑ flags, drawWeight G S i v * flagsWeight p q G S flags * f i v) =
        ∑ flags, (drawWeight G S i v * f i v) * flagsWeight p q G S flags := by
      apply Finset.sum_congr rfl
      intro flags hflags
      ring
    _ = _ := by rw [← Finset.mul_sum, sum_flagsWeight, mul_one]

theorem draw_mean_eq_average (G : Input I V) (S : State I V) (f : I → V → ℝ) :
    (∑ i : I, ∑ v : V, drawWeight G S i v * f i v) =
      SelectionOccupancy.average S.remaining (domain G S) f := by
  classical
  have hi : ∀ i : I, (∑ v : V, drawWeight G S i v * f i v) =
      if i ∈ S.remaining then
        ((∑ v ∈ domain G S i, f i v) / (domain G S i).card) / S.remaining.card
      else 0 := by
    intro i
    by_cases him : i ∈ S.remaining
    · simp only [drawWeight, him, true_and, ite_true, ite_mul, zero_mul]
      rw [← Finset.sum_filter]
      simp only [Finset.filter_mem_eq_inter, Finset.univ_inter]
      rw [← Finset.mul_sum]
      simp only [div_eq_mul_inv, mul_inv_rev]
      ring
    · simp [drawWeight, him]
  simp_rw [hi]
  rw [← Finset.sum_filter]
  simp only [Finset.filter_mem_eq_inter, Finset.univ_inter]
  exact (Finset.sum_div _ _ _).symm

theorem noise_mean_eq_average (p : Parameters) (q : ℕ) (G : Input I V)
    (S : State I V) (f : I → V → ℝ) :
    (∑ r : Noise I V, noiseWeight p q G S r * f r.1 r.2.1) =
      SelectionOccupancy.average S.remaining (domain G S) f := by
  rw [noise_mean_eq_draw_mean, draw_mean_eq_average]

theorem performed_occupancy_ge {P D L : Type*}
    [Fintype P] [Fintype D] [Fintype L]
    (p : Parameters) (q t : ℕ) (G : Input I V) (S : State I V)
    (hp : Precheck p q t G S) (A : FiniteAffine.Plane q P D L)
    (index : I ≃ D × Bool) (line : V → L)
    (hline : Selection.LineAssignment G A index line)
    (l : L) (T : Finset P) (hT : ∀ x ∈ T, A.incident x l)
    (B : ℝ) (hq : 0 < q) (hB : 0 < B)
    (hsize : ∀ i ∈ S.remaining, (q : ℝ) / B ≤ ((domain G S i).card : ℝ)) :
    (1 - B / q) * (T.card : ℝ) ≤
      ∑ r : Noise I V, noiseWeight p q G S r *
        ((SelectionOccupancy.afterPlaneLine A T l (line r.2.1)).card : ℝ) := by
  classical
  rw [noise_mean_eq_average p q G S
    (fun _ v => ((SelectionOccupancy.afterPlaneLine A T l (line v)).card : ℝ))]
  apply SelectionOccupancy.selection_plane_occupancy_drift G A index line hline
    S.remaining hp.1 (domain G S) _ l T hT B hq hB hsize
  intro i hi v hv
  exact (Finset.mem_filter.mp hv).2

omit [Fintype I] in
theorem domain_size_ge_q_div_Bstar (p : Parameters) (q t : ℕ) (G : Input I V)
    (S : State I V) (hp : Precheck p q t G S) (hc : 0 < p.c)
    (hscale : p.smin ≤ p.sizeScale q t) (i : I) (hi : i ∈ S.remaining) :
    (q : ℝ) / p.Bstar ≤ ((domain G S i).card : ℝ) := by
  have heq : (q : ℝ) / p.Bstar = p.smin * p.c * q / 2 := by
    unfold Parameters.Bstar
    rw [div_div_eq_mul_div]
    ring
  rw [heq]
  apply le_trans _ (hp.2.2.2.1 i hi).2
  apply div_le_div_of_nonneg_right _ (by norm_num)
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right hscale hc.le) (Nat.cast_nonneg q)

theorem performed_occupancy_ge_Bstar {P D L : Type*}
    [Fintype P] [Fintype D] [Fintype L]
    (p : Parameters) (q t : ℕ) (G : Input I V) (S : State I V)
    (hp : Precheck p q t G S) (hc : 0 < p.c) (hq : 0 < q)
    (hscale : p.smin ≤ p.sizeScale q t)
    (A : FiniteAffine.Plane q P D L) (index : I ≃ D × Bool) (line : V → L)
    (hline : Selection.LineAssignment G A index line)
    (l : L) (T : Finset P) (hT : ∀ x ∈ T, A.incident x l) :
    (1 - p.Bstar / q) * (T.card : ℝ) ≤
      ∑ r : Noise I V, noiseWeight p q G S r *
        ((SelectionOccupancy.afterPlaneLine A T l (line r.2.1)).card : ℝ) := by
  have hB : 0 < p.Bstar := by
    unfold Parameters.Bstar Parameters.smin
    positivity
  exact performed_occupancy_ge p q t G S hp A index line hline l T hT p.Bstar hq hB
    (fun i hi => domain_size_ge_q_div_Bstar p q t G S hp hc hscale i hi)

theorem performed_rescaled_occupancy_ge {P D L : Type*}
    [Fintype P] [Fintype D] [Fintype L]
    (p : Parameters) (q t : ℕ) (G : Input I V) (S : State I V)
    (hp : Precheck p q t G S) (hc : 0 < p.c) (hq : 0 < q)
    (hscale : p.smin ≤ p.sizeScale q t)
    (hfactor : 0 < 1 - p.Bstar / q)
    (A : FiniteAffine.Plane q P D L) (index : I ≃ D × Bool) (line : V → L)
    (hline : Selection.LineAssignment G A index line)
    (l : L) (T : Finset P) (hT : ∀ x ∈ T, A.incident x l) :
    (T.card : ℝ) / (1 - p.Bstar / q) ^ t ≤
      ∑ r : Noise I V, noiseWeight p q G S r *
        (((SelectionOccupancy.afterPlaneLine A T l (line r.2.1)).card : ℝ) /
          (1 - p.Bstar / q) ^ (t + 1)) := by
  simp_rw [← mul_div_assoc]
  rw [← Finset.sum_div]
  apply (le_div_iff₀ (pow_pos hfactor _)).2
  have heq : (T.card : ℝ) / (1 - p.Bstar / q) ^ t *
      (1 - p.Bstar / q) ^ (t + 1) = (1 - p.Bstar / q) * T.card := by
    rw [pow_succ, ← mul_assoc, div_mul_cancel₀ _ (pow_pos hfactor t).ne', mul_comm]
  rw [heq]
  exact performed_occupancy_ge_Bstar p q t G S hp hc hq hscale A index line hline l T hT

theorem tracked_card_le_order {P D L : Type*}
    [Fintype P] [Fintype D] [Fintype L]
    (q : ℕ) (A : FiniteAffine.Plane q P D L) (l : L) (T : Finset P)
    (hT : ∀ x ∈ T, A.incident x l) : T.card ≤ q := by
  classical
  have hs : T ⊆ A.linePoints l := by
    intro x hx
    simp [FiniteAffine.Plane.linePoints, hT x hx]
  exact (Finset.card_le_card hs).trans_eq (A.card_points_line l)

omit [Fintype I] [Fintype V] in
theorem performed_rescaled_occupancy_jump {P D L : Type*}
    [Fintype P] [Fintype D] [Fintype L]
    (p : Parameters) (q t : ℕ) (hc : 0 < p.c) (hq : 0 < q)
    (hfactor : 0 < 1 - p.Bstar / q)
    (A : FiniteAffine.Plane q P D L) (line : V → L)
    (l : L) (T : Finset P) (hT : ∀ x ∈ T, A.incident x l)
    (d : ℝ) (hd : 0 < d) (hdenom : d ≤ (1 - p.Bstar / q) ^ (t + 1))
    (r : Noise I V) :
    |((SelectionOccupancy.afterPlaneLine A T l (line r.2.1)).card : ℝ) /
        (1 - p.Bstar / q) ^ (t + 1) -
      (T.card : ℝ) / (1 - p.Bstar / q) ^ t| ≤ (1 + p.Bstar) / d := by
  classical
  have hB : 0 < p.Bstar := by
    unfold Parameters.Bstar Parameters.smin
    positivity
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hfactor1 : 1 - p.Bstar / q ≤ 1 := by
    linarith [div_nonneg hB.le hqR.le]
  have hcard : (T.card : ℝ) ≤ q := by
    exact_mod_cast tracked_card_le_order q A l T hT
  have h := SelectionOccupancy.rescaled_increment_abs_le hfactor hfactor1
    (pow_pos hfactor t) (show (1 - p.Bstar / q) ^ (t + 1) =
      (1 - p.Bstar / q) * (1 - p.Bstar / q) ^ t by rw [pow_succ]; ring)
    hd hdenom (Nat.cast_nonneg T.card) hcard (show (0 : ℝ) ≤ 1 by norm_num)
    (SelectionOccupancy.plane_step_abs_le_one A T l (line r.2.1) hT)
  have heq : (1 : ℝ) + (1 - (1 - p.Bstar / q)) * q = 1 + p.Bstar := by
    field_simp
    ring
  simpa only [heq] using h

end
end Balanced.Selection.Process

end OAI
