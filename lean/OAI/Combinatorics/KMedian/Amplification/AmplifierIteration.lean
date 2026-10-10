import Mathlib
import OAI.Combinatorics.KMedian.Amplification.AmplifierTableSize
import OAI.Combinatorics.KMedian.Machines.CSPTableBounds

namespace OAI

section Inline_PCPAmplifierIteration
namespace MetricKMedian.PCP.Compiler.AmplifierProgram
open Amplifier Binary Binary.Automatic
open scoped Classical

noncomputable def fallback : CSPTable Label := ([()],[(0,0,Finset.univ)])
lemma fallback_valid : fallback.WellFormed := by
  constructor
  · exact Nat.zero_lt_one
  · intro r hr
    have hr' : r=(0,0,Finset.univ) := by simpa only [fallback,List.mem_singleton] using hr
    subst r
    exact ⟨Nat.zero_lt_one,Nat.zero_lt_one⟩
noncomputable def normalize (s : CSPTable Label) : CSPTable Label := if s.check then s else fallback
lemma normalize_valid (s : CSPTable Label) : (normalize s).WellFormed := by
  unfold normalize
  split_ifs with h
  · exact (CSPTable.check_iff s).mp h
  · exact fallback_valid
lemma normalize_eq {s : CSPTable Label} (h : s.WellFormed) : normalize s=s :=
  ite_eq_left ((CSPTable.check_iff s).mpr h)
lemma poly_normalize : Poly normalize := by
  unfold normalize
  exact Poly.ite CSPTable.poly_check Poly.identity (Automatic.Poly.const _)
noncomputable def iterate : ℕ → CSPTable Label → CSPTable Label
  | 0, s => s
  | n+1, s => next (iterate n s)
lemma iterate_valid {s : CSPTable Label} (h : s.WellFormed) (n : ℕ) : (iterate n s).WellFormed := by
  induction n with
  | zero => exact h
  | succ n ih =>
    let : Nonempty (Fin (iterate n s).2.length) := Fin.pos_iff_nonempty.mp ih.1
    exact next_wellFormed (iterate n s) ih
lemma iterate_count {s : CSPTable Label} (h : s.WellFormed) (n : ℕ) :
    (iterate n s).1.length+(iterate n s).2.length≤co^n*(s.1.length+s.2.length) := by
  induction n with
  | zero => simp only [iterate,pow_zero,one_mul,le_refl]
  | succ n ih =>
    have hh := iterate_valid h n
    let : Nonempty (Fin (iterate n s).2.length) := Fin.pos_iff_nonempty.mp hh.1
    have hi : (iterate n s).2.length≤co^n*(s.1.length+s.2.length) := (Nat.le_add_left _ _).trans ih
    calc
      _ ≤ co*(iterate n s).2.length := next_count _ hh
      _ ≤ co*(co^n*(s.1.length+s.2.length)) := Nat.mul_le_mul_left _ hi
      _ = _ := by rw [pow_succ']; exact (Nat.mul_assoc _ _ _).symm
lemma iterate_complete {s : CSPTable Label} (h : s.WellFormed)
    (hc : ∃ a, (s.csp h).Satisfies a) (n : ℕ) :
    ∃ a, ((iterate n s).csp (iterate_valid h n)).Satisfies a := by
  induction n with
  | zero => exact hc
  | succ n ih =>
    have hh := iterate_valid h n
    let : Nonempty (Fin (iterate n s).2.length) := Fin.pos_iff_nonempty.mp hh.1
    exact complete (iterate n s) hh ih
lemma iterate_gap {s : CSPTable Label} (h : s.WellFormed) (δ : ℝ)
    (hg : ∀ a, δ≤(s.csp h).rejection a) (n : ℕ) :
    ∀ a, min (2^n*δ) (1/(capLoss:ℝ))≤((iterate n s).csp (iterate_valid h n)).rejection a := by
  have hc : 0≤1/(capLoss:ℝ) := by positivity
  induction n with
  | zero =>
    intro a
    change min (2^0*δ) (1/(capLoss:ℝ)) ≤ (s.csp h).rejection a
    rw [pow_zero,one_mul]
    exact (min_le_left _ _).trans (hg a)
  | succ n ih =>
    have hh := iterate_valid h n
    let : Nonempty (Fin (iterate n s).2.length) := Fin.pos_iff_nonempty.mp hh.1
    intro a
    have hn := gap (iterate n s) hh _ ih a
    apply le_trans _ hn
    rw [pow_succ]
    simp only [min_def]
    split_ifs <;> nlinarith
end MetricKMedian.PCP.Compiler.AmplifierProgram

end Inline_PCPAmplifierIteration

end OAI
