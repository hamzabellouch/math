import OAI.NumberTheory.Ostmann.Arithmetic.HistoryCompensationAtomBasic
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryCompensationMomentSelected

namespace OAI

open Erdos970

noncomputable section
open scoped BigOperators
namespace Ostmann.Arithmetic.HistoryCompensationAtom
open Construction CompensationEqualityPatterns HistoryCompensationMoment CounterpartNormalizationBound
attribute [local instance] Classical.propDecidable
variable {ι η : Type*} [Fintype ι] [DecidableEq ι] [Fintype η] [DecidableEq η]
variable {d : Decomposition} {Bs BD Bz L : ℝ} {k : ℕ} {E : Finset ℕ}

def selectedBlockWeight (C : InitialSourceChoice d Bs BD Bz k L E)
    (origin : ι → ℕ) (pick : η → ι) (v : CommonSample C.sources origin) : ℝ :=
  blockWeight (fun i => sourceWeight C.sources origin (pick i)) (fun w => (w.val : ℝ)) v

omit [DecidableEq ι] [DecidableEq η] in
lemma selectedBlockWeight_nonneg (C : InitialSourceChoice d Bs BD Bz k L E)
    (origin : ι → ℕ) (pick : η → ι) (v : CommonSample C.sources origin) :
    0 ≤ selectedBlockWeight C origin pick v :=
  blockWeight_nonneg _ _ (fun i w => sourceWeight_nonneg C.sources origin (pick i) w)
    (fun _w => Nat.cast_nonneg _) v

omit [DecidableEq ι] in
theorem selectedBlockWeight_mass_le (C : InitialSourceChoice d Bs BD Bz k L E)
    (origin : ι → ℕ) (pick : η → ι) (j : η) :
    (∑ v : CommonSample C.sources origin, selectedBlockWeight C origin pick v) ≤
      ∏ i ∈ Finset.univ.erase j, C.sourceNormalization (origin (pick i)) :=
  selected_source_block_moment_le C origin pick j

omit [DecidableEq ι] [DecidableEq η] in

theorem selectedBlockWeight_atom_le (C : InitialSourceChoice d Bs BD Bz k L E)
    (origin : ι → ℕ) (pick : η → ι) (j : η) (H : ℝ)
    (hsource : ∀ p : (C.sources (origin (pick j))).Sample,
      (C.sources (origin (pick j))).law.mass p ≠ 0 → H ≤ Real.log (p.val : ℝ))
    (v : CommonSample C.sources origin) :
    selectedBlockWeight C origin pick v ≤ Real.exp (-H) *
      ∏ i, C.sourceNormalization (origin (pick i)) := by
  apply blockWeight_atom_le _ _ _ j H
  · intro i w
    exact sourceWeight_nonneg C.sources origin (pick i) w
  · intro w
    exact_mod_cast (commonSample_prime C.sources origin w).pos
  · intro i
    exact sourceNormalization_nonneg C _
  · intro i w
    exact selected_sourceWeight_mass_mul_le C origin (pick i) w
  · intro w hw
    unfold sourceWeight at hw
    split_ifs at hw with hmem
    · exact hsource ⟨w.val, hmem⟩ hw
    · exact (hw rfl).elim

omit [DecidableEq ι] in
theorem selectedBlockWeight_uniform_bounds (C : InitialSourceChoice d Bs BD Bz k L E)
    (origin : ι → ℕ) (pick : η → ι) (j : η) {R H : ℝ} (hR : 1 ≤ R)
    (hcap : ∀ i, C.sourceNormalization (origin (pick i)) ≤ R)
    (hsource : ∀ p : (C.sources (origin (pick j))).Sample,
      (C.sources (origin (pick j))).law.mass p ≠ 0 → H ≤ Real.log (p.val : ℝ)) :
    (∑ v : CommonSample C.sources origin, selectedBlockWeight C origin pick v) ≤ R^Fintype.card η ∧
      ∀ v : CommonSample C.sources origin,
        selectedBlockWeight C origin pick v ≤ Real.exp (-H) * R^Fintype.card η := by
  have hprod : (∏ i, C.sourceNormalization (origin (pick i))) ≤ R^Fintype.card η := by
    simpa only [Finset.prod_const, Finset.card_univ] using
      Finset.prod_le_prod₀ (s:=Finset.univ)
        (fun i _ => sourceNormalization_nonneg C (origin (pick i))) (fun i _ => hcap i)
  constructor
  · apply (selectedBlockWeight_mass_le C origin pick j).trans
    calc
      _ ≤ ∏ i ∈ Finset.univ.erase j, R :=
        Finset.prod_le_prod₀ (fun i _ => sourceNormalization_nonneg C (origin (pick i)))
          (fun i _ => hcap i)
      _ = R^(Finset.univ.erase j).card := by simp
      _ ≤ R^Fintype.card η := pow_le_pow_right₀ hR
        (by simpa only [Finset.card_univ] using Finset.card_le_card (Finset.erase_subset j Finset.univ))
  · intro v
    exact (selectedBlockWeight_atom_le C origin pick j H hsource v).trans
      (mul_le_mul_of_nonneg_left hprod (Real.exp_nonneg _))

end Ostmann.Arithmetic.HistoryCompensationAtom

end

end OAI
