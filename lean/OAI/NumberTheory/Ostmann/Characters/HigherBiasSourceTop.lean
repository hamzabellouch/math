import OAI.NumberTheory.Ostmann.Characters.HigherBiasSourceScale
import OAI.NumberTheory.Ostmann.Characters.RichShellSelection

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.Characters
open Construction

lemma harmonicIntervalMass_pos_witness {E : Finset ℕ} {a b : ℝ}
    (h : 0 < harmonicIntervalMass E a b) :
    ∃ p∈E,a < Real.log (Real.log p) ∧ Real.log (Real.log p) ≤ b := by
  classical
  have hn : (E.filter (fun p : ℕ => a < Real.log (Real.log (p:ℝ)) ∧ Real.log (Real.log (p:ℝ)) ≤ b)).Nonempty := by
    by_contra hh
    have he := Finset.not_nonempty_iff_eq_empty.mp hh
    unfold harmonicIntervalMass at h
    rw [he] at h
    simp only [harmonicPrimeMass,Finset.sum_empty,lt_self_iff_false] at h
  obtain ⟨p,hp⟩ := hn
  exact ⟨p,(Finset.mem_filter.mp hp).1,(Finset.mem_filter.mp hp).2⟩

theorem exists_higherSource_top_shell {E : Finset ℕ} {α β L U ε c₀ : ℝ} {k : ℕ}
    (_hε : 0 < ε) (hεu : ε ≤ 5) (hc₀ : 0 < c₀)
    (hband : ∀ p∈E,α*L ≤ Real.log (Real.log p))
    (hend : U+5*(k:ℝ) ≤ β*L)
    (hrich : ∀ v : ℝ,U ≤ v → v+ε*(k:ℝ) ≤ U+5*(k:ℝ) →
      ∃ i : ℕ,v ≤ U+(i:ℝ) ∧ U+(i:ℝ)+1 ≤ v+ε*(k:ℝ) ∧
        c₀ ≤ harmonicIntervalMass E (U+(i:ℝ)) (U+(i:ℝ)+1)) :
    ∃ i : ℕ,let u := U+(i:ℝ);
      U ≤ u ∧ u+1 ≤ U+ε*(k:ℝ) ∧ α*L-1 ≤ u ∧ u ≤ β*L ∧
      c₀ ≤ harmonicIntervalMass E u (u+1) := by
  obtain ⟨i,hi,hie,him⟩ := hrich U le_rfl (by nlinarith [Nat.cast_nonneg (α:=ℝ) k])
  obtain ⟨p,hp,hpl,hpu⟩ := harmonicIntervalMass_pos_witness (hc₀.trans_le him)
  refine ⟨i,hi,hie,?_,?_,him⟩
  · linarith [hband p hp]
  · have hh : U+ε*(k:ℝ) ≤ U+5*(k:ℝ) := by nlinarith [Nat.cast_nonneg (α:=ℝ) k]
    linarith

theorem higherSource_lower_shell_gaps {A B D w s U u γ L : ℝ}
    (hγ : γ*L ≤ w) (hAB : A+2*w ≤ B) (hBD : B+2*w ≤ D)
    (hs : s+1 ≤ A+w) (hDU : D ≤ U) (hUu : U ≤ u) :
    B+w ≤ u-γ*L ∧ s+1 ≤ u-3*(γ*L) := by
  constructor <;> linarith

theorem higherSource_top_prime_log {p : ℕ} (hp : p.Prime) {u : ℝ}
    (h : Real.log (Real.log p) ≤ u+1) : Real.log p ≤ Real.exp 1*Real.exp u := by
  have hl : 0 < Real.log (p:ℝ) := Real.log_pos (by exact_mod_cast hp.one_lt)
  have hh := Real.exp_le_exp.mpr h
  simpa only [Real.exp_log hl,Real.exp_add,mul_comm] using hh

end Ostmann.Characters

end

end OAI
