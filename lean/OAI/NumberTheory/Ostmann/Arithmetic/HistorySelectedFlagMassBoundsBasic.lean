import OAI.NumberTheory.Ostmann.Arithmetic.HistoryCompensationAtomPatterns

namespace OAI

open Erdos970

noncomputable section
open scoped BigOperators
namespace Ostmann.Arithmetic.HistorySelectedFlagMassBounds
open Construction CompensationEqualityPatterns HistoryCompensationMoment HistoryCompensationAtom
attribute [local instance] Classical.propDecidable

def occurrenceCap (k : ℕ) : ℕ := max 1 (4*k*2^k)

def massCap (k : ℕ) (L : ℝ) : ℝ := Real.exp ((occurrenceCap k : ℝ)*L)

def atomCap (k : ℕ) (L : ℝ) : ℝ :=
  Real.exp ((occurrenceCap k : ℝ)*L-Real.exp ((39/10000 : ℝ)*L))

structure Bounds {κ : Type*} [Fintype κ] (k : ℕ) (L : ℝ) (w : κ → ℝ) : Prop where
  nonneg : ∀ v, 0 ≤ w v
  mass : (∑ v, w v) ≤ massCap k L
  atom : ∀ v, w v ≤ atomCap k L

lemma one_le_occurrenceCap (k : ℕ) : 1 ≤ occurrenceCap k := Nat.le_max_left _ _

lemma le_cap_mul {L : ℝ} (k : ℕ) (hL : 0 ≤ L) : L ≤ (occurrenceCap k : ℝ)*L := by
  have h : (1 : ℝ) ≤ occurrenceCap k := by exact_mod_cast one_le_occurrenceCap k
  simpa only [one_mul] using mul_le_mul_of_nonneg_right h hL

lemma one_le_massCap {L : ℝ} (k : ℕ) (hL : 0 ≤ L) : 1 ≤ massCap k L :=
  Real.one_le_exp (mul_nonneg (Nat.cast_nonneg _) hL)

lemma source_atom_le_cap {L : ℝ} (k : ℕ) (hL : 0 ≤ L) :
    Real.exp (L-Real.exp ((39/10000 : ℝ)*L)) ≤ atomCap k L :=
  Real.exp_le_exp.mpr (sub_le_sub_right (le_cap_mul k hL) _)

theorem prior_bounds {κ : Type*} [Fintype κ] (P : FinitePrior κ) (k : ℕ) {L : ℝ}
    (hL : 0 ≤ L)
    (ha : ∀ v, P.mass v ≤ Real.exp (L-Real.exp ((39/10000 : ℝ)*L))) :
    Bounds k L P.mass where
  nonneg := P.mass_nonneg
  mass := by rw [P.mass_total]; exact one_le_massCap k hL
  atom v := (ha v).trans (source_atom_le_cap k hL)

theorem sourceWeight_bounds {ι : Type*} [Fintype ι] [DecidableEq ι]
    (sources : SourceFamily) (origin : ι → ℕ) (i : ι) (k : ℕ) {L : ℝ}
    (hL : 0 ≤ L)
    (ha : ∀ v : (sources (origin i)).Sample,
      (sources (origin i)).law.mass v ≤ Real.exp (L-Real.exp ((39/10000 : ℝ)*L))) :
    Bounds k L (sourceWeight sources origin i) where
  nonneg := sourceWeight_nonneg sources origin i
  mass := by rw [sourceWeight_sum]; exact one_le_massCap k hL
  atom v := by
    unfold sourceWeight
    split_ifs with hv
    · exact (ha ⟨v.val,hv⟩).trans (source_atom_le_cap k hL)
    · exact (Real.exp_pos _).le

theorem literal_block_bounds {ι : Type*} [Fintype ι] [DecidableEq ι]
    {d : Decomposition} {Bs BD Bz L : ℝ} {k : ℕ} {E : Finset ℕ}
    (C : InitialSourceChoice d Bs BD Bz k L E)
    (origin : ι → ℕ) {τ : ι → ℕ} (p : Pattern τ) (q : Block p)
    (hL : 0 ≤ L) (hn : Fintype.card ι ≤ occurrenceCap k)
    (hcap : ∀ i, C.sourceNormalization (origin i) ≤ Real.exp L)
    (hsource : ∀ i, ∀ v : (C.sources (origin i)).Sample,
      (C.sources (origin i)).law.mass v ≠ 0 →
        Real.exp ((39/10000 : ℝ)*L) ≤ Real.log (v.val : ℝ)) :
    Bounds k L (fun v : CommonSample C.sources origin =>
      CompensationEqualityPatterns.blockWeight p (sourceWeight C.sources origin) q v *
        (v.val : ℝ)^multiplicity p q / (v.val : ℝ)) := by
  simp_rw [← selectedBlockWeight_fiber_eq]
  let j : Fiber p q := Classical.choice (fiber_nonempty p q)
  have h := selectedBlockWeight_uniform_bounds C origin (fun i : Fiber p q => i.val) j
    (Real.one_le_exp hL) (fun i => hcap i.val) (hsource j.val)
  have hcard : Fintype.card (Fiber p q) ≤ occurrenceCap k :=
    (Fintype.card_le_of_injective (fun i : Fiber p q => i.val) Subtype.val_injective).trans hn
  have hbudget : (Fintype.card (Fiber p q) : ℝ)*L ≤ (occurrenceCap k : ℝ)*L :=
    mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) hL
  have he : (Real.exp L)^Fintype.card (Fiber p q) =
      Real.exp ((Fintype.card (Fiber p q) : ℝ)*L) := by rw [← Real.exp_nat_mul]
  refine ⟨selectedBlockWeight_fiber_nonneg C origin p q, ?_, ?_⟩
  · exact h.1.trans (by rw [he]; exact Real.exp_le_exp.mpr hbudget)
  · intro v
    have hv := h.2 v
    rw [he, ← Real.exp_add] at hv
    exact hv.trans (Real.exp_le_exp.mpr (by linarith))

end Ostmann.Arithmetic.HistorySelectedFlagMassBounds

end

end OAI
