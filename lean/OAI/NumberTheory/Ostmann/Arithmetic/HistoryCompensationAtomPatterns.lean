import OAI.NumberTheory.Ostmann.Arithmetic.HistoryCompensationAtomSelected
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryCompensationPatternBudget

namespace OAI

open Erdos970

noncomputable section
open scoped BigOperators
namespace Ostmann.Arithmetic.HistoryCompensationAtom
open Construction CompensationEqualityPatterns HistoryCompensationMoment Filter
attribute [local instance] Classical.propDecidable
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {d : Decomposition} {Bs BD Bz L : ℝ} {k : ℕ} {E : Finset ℕ}

omit [DecidableEq ι] in

theorem selectedBlockWeight_fiber_eq (C : InitialSourceChoice d Bs BD Bz k L E)
    (origin : ι → ℕ) {τ : ι → ℕ} (p : Pattern τ) (q : Block p)
    (v : CommonSample C.sources origin) :
    selectedBlockWeight C origin (fun i : Fiber p q => i.val) v =
      CompensationEqualityPatterns.blockWeight p (sourceWeight C.sources origin) q v *
        (v.val : ℝ) ^ multiplicity p q / (v.val : ℝ) := by
  simp only [selectedBlockWeight, HistoryCompensationAtom.blockWeight,
    CompensationEqualityPatterns.blockWeight, CompensationEqualityPatterns.multiplicity,
    Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, div_eq_mul_inv]
  ring

omit [DecidableEq ι] in

theorem selectedBlockWeight_fiber_sum_eq (C : InitialSourceChoice d Bs BD Bz k L E)
    (origin : ι → ℕ) {τ : ι → ℕ} (p : Pattern τ) (q : Block p) :
    (∑ v : CommonSample C.sources origin,
      selectedBlockWeight C origin (fun i : Fiber p q => i.val) v) =
      HistoryCompensationPatternBudget.blockMoment p (sourceWeight C.sources origin)
        (fun v => (v.val : ℝ)) q := rfl

omit [DecidableEq ι] in
theorem selectedBlockWeight_fiber_nonneg [DecidableEq ι]
    (C : InitialSourceChoice d Bs BD Bz k L E)
    (origin : ι → ℕ) {τ : ι → ℕ} (p : Pattern τ) (q : Block p)
    (v : CommonSample C.sources origin) :
    0 ≤ selectedBlockWeight C origin (fun i : Fiber p q => i.val) v :=
  selectedBlockWeight_nonneg C origin _ v

theorem selected_pattern_bounds_eventually (d : Decomposition) (Bs BD Bz : ℝ)
    {k : ℕ} (hk : 0 < k) :
    ∀ᶠ L : ℝ in atTop, ∀ (E : Finset ℕ) (C : InitialSourceChoice d Bs BD Bz k L E),
      Real.exp ((1/20 : ℝ)*L) ≤ C.blockBase →
      C.blockBase+favorableBlockWidth L ≤ Real.exp ((9/10 : ℝ)*L) →
      C.blockBase-2 < (C.giantCenter : ℝ) →
      (C.giantCenter : ℝ) < C.blockBase+favorableBlockWidth L+2 →
      |(C.bulkBin : ℝ)| ≤ favorableBlockWidth L/16 →
      |(C.spectatorBin : ℝ)| ≤ favorableBlockWidth L/16 →
      ∀ (origin τ : ι → ℕ) (p : Pattern τ) (q : Block p),
      (∑ v : CommonSample C.sources origin,
        selectedBlockWeight C origin (fun i : Fiber p q => i.val) v) ≤
        Real.exp ((Fintype.card ι : ℝ)*L) ∧
      ∀ v : CommonSample C.sources origin,
        selectedBlockWeight C origin (fun i : Fiber p q => i.val) v ≤
          Real.exp ((Fintype.card ι : ℝ)*L-Real.exp ((39/10000 : ℝ)*L)) := by
  filter_upwards [HistorySelectedSourceAtomBounds.selected_source_atom_bounds_eventually
    d Bs BD Bz hk, eventually_ge_atTop (0 : ℝ)] with L hs hL
  intro E C hG hGu hcl hcu hb hd origin τ p q
  have hc := hs E C hG hGu hcl hcu hb hd
  let j : Fiber p q := Classical.choice (fiber_nonempty p q)
  have h := selectedBlockWeight_uniform_bounds C origin (fun i : Fiber p q => i.val) j
    (Real.one_le_exp hL) (fun i => hc.1 _) (hc.2.1 (origin j.val))
  have hcard : Fintype.card (Fiber p q) ≤ Fintype.card ι :=
    Fintype.card_le_of_injective (fun i : Fiber p q => i.val) Subtype.val_injective
  have hbudget : (Fintype.card (Fiber p q) : ℝ)*L ≤ (Fintype.card ι : ℝ)*L :=
    mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) hL
  have he : (Real.exp L)^Fintype.card (Fiber p q) =
      Real.exp ((Fintype.card (Fiber p q) : ℝ)*L) := by rw [← Real.exp_nat_mul]
  constructor
  · rw [he] at h
    exact h.1.trans (Real.exp_le_exp.mpr hbudget)
  · intro v
    have hv := h.2 v
    rw [he, ← Real.exp_add] at hv
    exact hv.trans (Real.exp_le_exp.mpr (by linarith))

theorem selected_pattern_literal_bounds_eventually (d : Decomposition) (Bs BD Bz : ℝ)
    {k : ℕ} (hk : 0 < k) :
    ∀ᶠ L : ℝ in atTop, ∀ (E : Finset ℕ) (C : InitialSourceChoice d Bs BD Bz k L E),
      Real.exp ((1/20 : ℝ)*L) ≤ C.blockBase →
      C.blockBase+favorableBlockWidth L ≤ Real.exp ((9/10 : ℝ)*L) →
      C.blockBase-2 < (C.giantCenter : ℝ) →
      (C.giantCenter : ℝ) < C.blockBase+favorableBlockWidth L+2 →
      |(C.bulkBin : ℝ)| ≤ favorableBlockWidth L/16 →
      |(C.spectatorBin : ℝ)| ≤ favorableBlockWidth L/16 →
      ∀ (origin τ : ι → ℕ) (p : Pattern τ) (q : Block p),
      let weight := fun v : CommonSample C.sources origin =>
        CompensationEqualityPatterns.blockWeight p (sourceWeight C.sources origin) q v *
          (v.val : ℝ)^multiplicity p q / (v.val : ℝ)
      (∀ v, 0 ≤ weight v) ∧
      (∑ v, weight v) ≤ Real.exp ((Fintype.card ι : ℝ)*L) ∧
      ∀ v, weight v ≤ Real.exp ((Fintype.card ι : ℝ)*L-Real.exp ((39/10000 : ℝ)*L)) := by
  filter_upwards [selected_pattern_bounds_eventually (ι := ι) d Bs BD Bz hk] with L hL
  intro E C hG hGu hcl hcu hb hd origin τ p q
  dsimp only
  simp_rw [← selectedBlockWeight_fiber_eq]
  exact ⟨selectedBlockWeight_fiber_nonneg C origin p q,
    hL E C hG hGu hcl hcu hb hd origin τ p q⟩

end Ostmann.Arithmetic.HistoryCompensationAtom

end

end OAI
