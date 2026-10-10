import OAI.NumberTheory.Ostmann.Supply.ActualLogBudget
import OAI.NumberTheory.Ostmann.Supply.TensorModeReflection

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.Supply
open Filter Finset Ostmann.Preliminaries
open TensorModes
open scoped BigOperators

def actualComplementSupport (d : Decomposition) (p : ℕ) : Finset (ZMod p) :=
  if hp : p = 0 then ∅ else letI : NeZero p := ⟨hp⟩; (actualSupport d p)ᶜ

@[simp] theorem actualComplementSupport_eq (d : Decomposition) (p : ℕ) [NeZero p] :
    actualComplementSupport d p = (actualSupport d p)ᶜ := by
  simp [actualComplementSupport, NeZero.ne p]

def actualSecondSupport (d : Decomposition) : ∀ p : ℕ, Finset (ZMod p) :=
  reflectedSupport (actualComplementSupport d)

@[simp] theorem supportRatio_actualSupport (d : Decomposition) (p : ℕ) :
    supportRatio (actualSupport d) p = actualRatio d p := rfl

theorem supportRatio_actualComplementSupport (d : Decomposition) {p : ℕ} (hp : p.Prime) :
    supportRatio (actualComplementSupport d) p = (actualRatio d p)⁻¹ := by
  let : NeZero p := ⟨hp.ne_zero⟩
  have hs : ((d.residueSupport p).card : ℝ) ≠ 0 := by
    exact_mod_cast card_ne_zero.mpr (d.residueSupport_nonempty p)
  have ht : (((d.residueSupport p)ᶜ).card : ℝ) ≠ 0 := by
    exact_mod_cast card_ne_zero.mpr (d.residueSupport_compl_nonempty p hp)
  have hc : ((d.residueSupport p).card : ℝ) + (((d.residueSupport p)ᶜ).card : ℝ) = p := by
    exact_mod_cast (by simpa only [ZMod.card p] using card_add_card_compl (d.residueSupport p))
  have hr : actualRatio d p = (((d.residueSupport p)ᶜ).card : ℝ) /
      ((d.residueSupport p).card : ℝ) := by
    rw [actualRatio, actualSupport_eq]
    field_simp
    linarith
  rw [supportRatio, actualComplementSupport_eq, actualSupport_eq, hr, inv_div]
  field_simp
  linarith

@[simp] theorem supportRatio_actualSecondSupport (d : Decomposition) {p : ℕ} (hp : p.Prime) :
    supportRatio (actualSecondSupport d) p = (actualRatio d p)⁻¹ := by
  rw [actualSecondSupport, supportRatio_reflectedSupport,
    supportRatio_actualComplementSupport d hp]

theorem abs_log_actualSecondSupport (d : Decomposition) {p : ℕ} (hp : p.Prime) :
    |Real.log (supportRatio (actualSecondSupport d) p)| = |Real.log (actualRatio d p)| := by
  rw [supportRatio_actualSecondSupport d hp, Real.log_inv, abs_neg]

theorem completion_primesUpTo_eq_primesLE (R : ℕ) :
    CompletionCounting.primesUpTo R = R.primesLE := by
  ext p
  simp only [CompletionCounting.primesUpTo, mem_filter, mem_Icc, Nat.mem_primesLE]
  exact ⟨fun h => ⟨h.1.2, h.2⟩, fun h => ⟨⟨h.2.two_le, h.1⟩, h.2⟩⟩

theorem logBudget_actualSupport (d : Decomposition) (R : ℕ) :
    (∑ p ∈ CompletionCounting.primesUpTo R, |Real.log (supportRatio (actualSupport d) p)| / p) =
      actualLogBudget d R := by
  rw [completion_primesUpTo_eq_primesLE]
  rfl

theorem logBudget_actualSecondSupport (d : Decomposition) (R : ℕ) :
    (∑ p ∈ CompletionCounting.primesUpTo R,
      |Real.log (supportRatio (actualSecondSupport d) p)| / p) = actualLogBudget d R := by
  rw [completion_primesUpTo_eq_primesLE, actualLogBudget]
  apply sum_congr rfl
  intro p hp
  rw [abs_log_actualSecondSupport d (Nat.mem_primesLE.mp hp).2]

theorem eventually_actualWindow_supports (d : Decomposition) :
    ∀ᶠ R : ℕ in atTop,
      (upperWindow d.A (R^2)).Nonempty ∧ (upperWindow d.B (R^2)).Nonempty ∧
      (∀ a ∈ upperWindow d.A (R^2), ∀ p, p.Prime → p ≤ R →
        (a : ZMod p) ∈ actualSupport d p) ∧
      (∀ b ∈ upperWindow d.B (R^2), ∀ p, p.Prime → p ≤ R →
        (b : ZMod p) ∈ actualSecondSupport d p) := by
  have hpow : Tendsto (fun R : ℕ => R^2) atTop atTop := tendsto_pow_atTop (by decide)
  filter_upwards [hpow.eventually (eventually_upperWindow_collision d),
    hpow.eventually (eventually_upperWindow_large d.cutoff)] with R hn hlarge
  have hsqrt : Real.sqrt ((R^2 : ℕ) : ℝ) = (R : ℝ) := by
    rw [Nat.cast_pow, Real.sqrt_sq (Nat.cast_nonneg R)]
  rw [hsqrt] at hlarge
  refine ⟨hn.1, hn.2.1, ?_, ?_⟩
  · intro a ha p hp hpR
    let : NeZero p := ⟨hp.ne_zero⟩
    obtain ⟨haA, haR, halarge⟩ := mem_upperWindow.mp ha
    have hra : R + d.cutoff < a := by exact_mod_cast hlarge.trans_le halarge
    rw [actualSupport_eq]
    exact (d.mem_residueSupport p _).mpr ⟨a, haA, by omega, rfl⟩
  · intro b hb p hp hpR
    let : NeZero p := ⟨hp.ne_zero⟩
    obtain ⟨hbB, hbR, hblarge⟩ := mem_upperWindow.mp hb
    have hrb : R + d.cutoff < b := by exact_mod_cast hlarge.trans_le hblarge
    rw [actualSecondSupport, mem_reflectedSupport, actualComplementSupport_eq, actualSupport_eq]
    apply d.negResidueSupport_subset_compl p hp
    exact (d.mem_negResidueSupport p _).mpr ⟨b, hbB, by omega, rfl⟩

end Ostmann.Supply

end

end OAI
