import Mathlib.Tactic
import OAI.Combinatorics.BalancedRyser.Selection.SelectionProcessLaw

namespace OAI

namespace Balanced.Selection.Process

noncomputable section
attribute [local instance] Classical.propDecidable
open scoped BigOperators

variable {I V : Type*} [Fintype I] [Fintype V]

omit [Fintype V] in

theorem sum_drawWeight_over_slots (G : Input I V) (S : State I V) (w : V) :
    (∑ i : I, drawWeight G S i w) =
      if w ∈ currentVertices G S then
        ((S.remaining.card : ℝ) * (domain G S (G.slot w)).card)⁻¹ else 0 := by
  rw [Finset.sum_eq_single (G.slot w)]
  · simp only [drawWeight, domain, currentVertices, Finset.mem_filter]
    by_cases ha : w ∈ S.alive <;> by_cases hr : G.slot w ∈ S.remaining <;>
      simp [ha, hr]
  · intro i _ hi
    have hslot : G.slot w ≠ i := Ne.symm hi
    simp [drawWeight, domain, hslot]
  · simp

omit [Fintype V] in

theorem sum_drawWeight_over_slots_le (G : Input I V) (S : State I V)
    (L : ℝ) (hL : 0 < L) (hS : S.remaining.Nonempty)
    (hdom : ∀ i ∈ S.remaining, L ≤ ((domain G S i).card : ℝ)) (w : V) :
    (∑ i : I, drawWeight G S i w) ≤ 1 / ((S.remaining.card : ℝ) * L) := by
  have hcard : (0 : ℝ) < S.remaining.card := by
    exact_mod_cast Finset.card_pos.mpr hS
  rw [sum_drawWeight_over_slots]
  split_ifs with hw
  · have hslot : G.slot w ∈ S.remaining := (Finset.mem_filter.mp hw).2
    rw [inv_eq_one_div]
    exact one_div_le_one_div_of_le (mul_pos hcard hL)
      (mul_le_mul_of_nonneg_left (hdom _ hslot) hcard.le)
  · positivity

theorem drawWeight_event_le_card_div (G : Input I V) (S : State I V)
    (A : Finset V) (L : ℝ) (hL : 0 < L) (hS : S.remaining.Nonempty)
    (hdom : ∀ i ∈ S.remaining, L ≤ ((domain G S i).card : ℝ)) :
    (∑ i : I, ∑ w : V, if w ∈ A then drawWeight G S i w else 0) ≤
      (A.card : ℝ) / ((S.remaining.card : ℝ) * L) := by
  rw [Finset.sum_comm]
  have hswap (w : V) :
      (∑ i : I, if w ∈ A then drawWeight G S i w else 0) =
        if w ∈ A then ∑ i : I, drawWeight G S i w else 0 := by
    by_cases hw : w ∈ A <;> simp [hw]
  simp_rw [hswap]
  rw [← Finset.sum_filter]
  simp only [Finset.filter_mem_eq_inter, Finset.univ_inter]
  calc
    (∑ w ∈ A, ∑ i : I, drawWeight G S i w) ≤
        ∑ _w ∈ A, 1 / ((S.remaining.card : ℝ) * L) := by
      exact Finset.sum_le_sum fun w _ =>
        sum_drawWeight_over_slots_le G S L hL hS hdom w
    _ = (A.card : ℝ) / ((S.remaining.card : ℝ) * L) := by
      simp [div_eq_mul_inv]

theorem noiseWeight_vertex_event_eq_drawWeight (p : Parameters) (q : ℕ)
    (G : Input I V) (S : State I V) (A : Finset V) :
    (∑ r : Noise I V, if r.2.1 ∈ A then noiseWeight p q G S r else 0) =
      ∑ i : I, ∑ w : V, if w ∈ A then drawWeight G S i w else 0 := by
  simp only [Noise, Fintype.sum_prod_type, noiseWeight]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro w _
  by_cases hw : w ∈ A
  · simp only [hw, ite_true, ← Finset.mul_sum, sum_flagsWeight, mul_one]
  · simp [hw]

theorem exceptional_noise_mass_le
    {G : Input I V} {q : ℕ} {c C : ℝ} (hG : GraphBounds G q c C)
    (p : Parameters) (S : State I V) (v : V)
    (L : ℝ) (hL : 0 < L) (hS : S.remaining.Nonempty)
    (hdom : ∀ i ∈ S.remaining, L ≤ ((domain G S i).card : ℝ)) :
    (∑ r : Noise I V, if r.2.1 ∈ G.exceptional v then noiseWeight p q G S r else 0) ≤
      (q : ℝ) ^ (1 / 8 : ℝ) / ((S.remaining.card : ℝ) * L) := by
  rw [noiseWeight_vertex_event_eq_drawWeight]
  exact (drawWeight_event_le_card_div G S (G.exceptional v) L hL hS hdom).trans
    (div_le_div_of_nonneg_right (hG.2.2.2.2.2.1 v)
      (mul_nonneg (Nat.cast_nonneg _) hL.le))

theorem exceptional_noise_mass_le_source_bound
    {G : Input I V} {q t : ℕ} (p : Parameters) (hp : p.Admissible)
    (hq : 0 < q) (hG : GraphBounds G q p.c p.C)
    (S : State I V) (v : V) (hpre : Precheck p q t G S)
    (hscale : p.smin ≤ p.sizeScale q t)
    (hremaining : p.a * (q : ℝ) ≤ (S.remaining.card : ℝ)) :
    (∑ r : Noise I V, if r.2.1 ∈ G.exceptional v then noiseWeight p q G S r else 0) ≤
      2 * (q : ℝ) ^ (1 / 8 : ℝ) / (p.a * p.smin * p.c * (q : ℝ) ^ 2) := by
  have hc : 0 < p.c := hp.1
  have ha : 0 < p.a := hp.2.2.2.2.1
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hsmin : 0 < p.smin := Real.exp_pos _
  let L : ℝ := p.smin * p.c * q / 2
  have hL : 0 < L := by dsimp [L]; positivity
  have hdom : ∀ i ∈ S.remaining, L ≤ ((domain G S i).card : ℝ) := by
    intro i hi
    apply le_trans _ (hpre.2.2.2.1 i hi).2
    dsimp [L]
    gcongr
  have hprob := exceptional_noise_mass_le hG p S v L hL hpre.1 hdom
  calc
    (∑ r : Noise I V, if r.2.1 ∈ G.exceptional v then noiseWeight p q G S r else 0) ≤
        (q : ℝ) ^ (1 / 8 : ℝ) / ((S.remaining.card : ℝ) * L) := hprob
    _ ≤ (q : ℝ) ^ (1 / 8 : ℝ) / ((p.a * q) * L) :=
      div_le_div_of_nonneg_left (Real.rpow_nonneg (Nat.cast_nonneg _) _)
        (mul_pos (mul_pos ha hqR) hL)
        (mul_le_mul_of_nonneg_right hremaining hL.le)
    _ = 2 * (q : ℝ) ^ (1 / 8 : ℝ) / (p.a * p.smin * p.c * (q : ℝ) ^ 2) := by
      dsimp [L]
      field_simp

end
end Balanced.Selection.Process

end OAI
