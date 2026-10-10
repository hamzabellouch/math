import Mathlib
import OAI.Combinatorics.KMedian.Amplification.AmplifierSize
import OAI.Combinatorics.KMedian.Machines.Box

namespace OAI

section Inline_PCPIteration

namespace MetricKMedian.PCP
open Finset
open scoped BigOperators Classical

namespace Amplifier

namespace Box
variable (C : Box)
noncomputable def next : Box := ofCSP (result C.csp)
lemma next_complete (h : C.Perfect) : C.next.Perfect := by
  obtain ⟨a,ha⟩ := h
  exact ofCSP_complete (result C.csp) (complete C.csp a ha)
lemma next_sound {δ : ℝ} (h : C.Rejects δ) : C.next.Rejects (min (2*δ) (1/(capLoss:ℝ))) := by
  apply ofCSP_sound (result C.csp)
  intro a
  exact (min_le_min_right _ (mul_le_mul_of_nonneg_left (h _) (by norm_num))).trans (sound C.csp a)
lemma next_edges : C.next.edges ≤ edgeCoefficient*C.edges := by
  change (ofCSP (result C.csp)).edges ≤ _
  rw [ofCSP_edges]
  simpa only [Nat.card_fin] using edge_card_bound C.csp
lemma next_size : C.next.nodes+C.next.edges ≤ sizeCoefficient*C.edges := by
  change (ofCSP (result C.csp)).nodes+(ofCSP (result C.csp)).edges ≤ _
  rw [ofCSP_nodes,ofCSP_edges]
  simpa only [Nat.card_fin] using size_bound C.csp

noncomputable def iterate (C : Box) : ℕ → Box
  | 0 => C
  | n+1 => (iterate C n).next
lemma iterate_complete (h : C.Perfect) (n : ℕ) : (C.iterate n).Perfect := by
  induction n with
  | zero => exact h
  | succ n ih => simpa only [iterate] using (C.iterate n).next_complete ih
lemma iterate_sound {δ : ℝ} (h : C.Rejects δ) (n : ℕ) :
    (C.iterate n).Rejects (min (2^n*δ) (1/(capLoss:ℝ))) := by
  have hc : 0≤1/(capLoss:ℝ) := one_div_nonneg.mpr (Nat.cast_nonneg capLoss)
  induction n with
  | zero =>
    intro a
    change min (2^0*δ) (1/(capLoss:ℝ)) ≤ C.csp.rejection a
    rw [pow_zero,one_mul]
    exact (min_le_left _ _).trans (h a)
  | succ n ih =>
    rw [iterate]
    intro a
    have hn := (C.iterate n).next_sound ih a
    apply le_trans _ hn
    rw [pow_succ]
    simp only [min_def]
    split_ifs <;> nlinarith
lemma iterate_edges (n : ℕ) : (C.iterate n).edges ≤ edgeCoefficient^n*C.edges := by
  induction n with
  | zero => simp [iterate]
  | succ n ih =>
    rw [iterate]
    calc
      _ ≤ edgeCoefficient*(C.iterate n).edges := (C.iterate n).next_edges
      _ ≤ edgeCoefficient*(edgeCoefficient^n*C.edges) := Nat.mul_le_mul_left _ ih
      _ = _ := by rw [pow_succ']; exact (Nat.mul_assoc _ _ _).symm
lemma iterate_size (n : ℕ) :
    (C.iterate (n+1)).nodes+(C.iterate (n+1)).edges ≤ sizeCoefficient*edgeCoefficient^n*C.edges := by
  rw [iterate]
  calc
    _ ≤ sizeCoefficient*(C.iterate n).edges := (C.iterate n).next_size
    _ ≤ sizeCoefficient*(edgeCoefficient^n*C.edges) := Nat.mul_le_mul_left _ (C.iterate_edges n)
    _ = _ := (Nat.mul_assoc _ _ _).symm

lemma inverse_edge_gap (h : ¬ C.Perfect) : C.Rejects (1/(C.edges:ℝ)) := by
  intro a
  have he : ∃ e, (a (C.csp.left e),a (C.csp.right e)) ∉ C.csp.allowed e := by
    by_contra hh
    push Not at hh
    exact h ⟨a,hh⟩
  obtain ⟨e,he⟩ := he
  simpa only [BinaryCSP.rejection,Fintype.card_fin] using
    testRate_ge_atom (fun e => (a (C.csp.left e),a (C.csp.right e)) ∉ C.csp.allowed e) e he

def count : ℕ := Nat.log 2 C.edges+1
noncomputable def amplified : Box := C.iterate C.count
lemma amplified_complete (h : C.Perfect) : C.amplified.Perfect := C.iterate_complete h _
lemma amplified_sound (h : ¬ C.Perfect) : C.amplified.Rejects (1/(capLoss:ℝ)) := by
  have hn : C.edges ≤ 2^C.count := Nat.le_of_lt (Nat.lt_pow_succ_log_self (by omega : 1<2) _)
  have hn' : (C.edges:ℝ)≤2^C.count := by exact_mod_cast hn
  have he : 0<(C.edges:ℝ) := Nat.cast_pos.mpr C.edges_pos
  have hc : (1:ℝ)≤capLoss := by norm_num [capLoss]
  have hh : 1/(capLoss:ℝ)≤2^C.count*(1/(C.edges:ℝ)) := by
    have h1 : (1:ℝ)≤2^C.count/(C.edges:ℝ) := (le_div_iff₀ he).mpr (by simpa using hn')
    have h2 : (1:ℝ)/(capLoss:ℝ)≤1 := (div_le_one (Nat.cast_pos.mpr capLoss_pos)).mpr hc
    simpa only [mul_one_div] using h2.trans h1
  simpa only [amplified,min_eq_right hh] using C.iterate_sound (C.inverse_edge_gap h) C.count
end Box
end Amplifier
end MetricKMedian.PCP

end Inline_PCPIteration

end OAI
