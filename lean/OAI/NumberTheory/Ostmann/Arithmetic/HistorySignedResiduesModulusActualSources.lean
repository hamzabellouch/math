import OAI.NumberTheory.Ostmann.Arithmetic.HistorySmoothWeightScaleNumerics
import OAI.NumberTheory.Ostmann.Construction.SourceRangeSeparation

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.Arithmetic.HistorySignedResidues
open Construction Conclusion Filter

def actualFactorConstant (Bs BD Bz : ℝ) (k : ℕ) : ℝ :=
  scaleLinearConstant Bs BD Bz k + 3*(2:ℝ)^k + 1

def actualFactorCap (Bs BD Bz : ℝ) (k : ℕ) (L : ℝ) : ℝ :=
  Real.exp (actualFactorConstant Bs BD Bz k*((bulkSize k L:ℝ)+1) +
    actualFactorConstant Bs BD Bz k*Real.exp ((1/100:ℝ)*L))

def actualFactorCount (k : ℕ) (L : ℝ) : ℕ :=
  2^k*(6+4*k)*(bulkSize k L+1)

theorem actualFactorConstant_pos (Bs BD Bz : ℝ) (k : ℕ) :
    0 < actualFactorConstant Bs BD Bz k := by
  have := scaleLinearConstant_pos Bs BD Bz k
  unfold actualFactorConstant
  positivity

theorem actualFactorCap_one_le (Bs BD Bz : ℝ) (k : ℕ) (L : ℝ) :
    1 ≤ actualFactorCap Bs BD Bz k L := by
  apply Real.one_le_exp
  exact add_nonneg (mul_nonneg (actualFactorConstant_pos _ _ _ _).le (by positivity))
    (mul_nonneg (actualFactorConstant_pos _ _ _ _).le (Real.exp_pos _).le)

theorem sourceMass_value_le {sources : SourceFamily} {B : ℝ}
    (h : ∀ origin, ∀ p : (sources origin).Sample,
      (sources origin).law.mass p ≠ 0 → ((p:ℕ):ℝ) ≤ B)
    {q : SmallSlot} (hq : sourceMass sources q ≠ 0) : (q.value:ℝ) ≤ B := by
  unfold sourceMass at hq
  split_ifs at hq with hm
  · exact h q.origin ⟨q.value,hm⟩ hq
  · exact (hq rfl).elim

def sourceLogCap (S : PrimeSource) (A : ℝ) : Prop :=
  ∀ p : S.Sample, S.law.mass p ≠ 0 → Real.log (p:ℕ) ≤ A

theorem initialSourceFamily_log_le (b k : ℕ) (bulk : PrimeSource)
    (top : Fin 3 → PrimeSource) (comp : Fin k → Fin 2 → PrimeSource) (A : ℝ)
    (hb : ∀ p : bulk.Sample, bulk.law.mass p ≠ 0 → Real.log (p:ℕ) ≤ A)
    (ht : ∀ i, ∀ p : (top i).Sample, (top i).law.mass p ≠ 0 → Real.log (p:ℕ) ≤ A)
    (hc : ∀ j i, ∀ p : (comp j i).Sample, (comp j i).law.mass p ≠ 0 → Real.log (p:ℕ) ≤ A) :
    ∀ origin, ∀ p : (initialSourceFamily b k bulk top comp origin).Sample,
      (initialSourceFamily b k bulk top comp origin).law.mass p ≠ 0 → Real.log (p:ℕ) ≤ A := by
  intro origin
  change sourceLogCap (initialSourceFamily b k bulk top comp origin) A
  unfold initialSourceFamily initialSourceValue
  split_ifs
  · exact hb
  · exact ht _
  · exact hc _ _
  · exact hb

theorem sources_log_le {d : Decomposition} {Bs BD Bz : ℝ} {k : ℕ} {L : ℝ} {E : Finset ℕ}
    (C : InitialSourceChoice d Bs BD Bz k L E) (A : ℝ)
    (hb : ∀ p : C.bulk.Sample, C.bulk.law.mass p ≠ 0 → Real.log (p:ℕ) ≤ A)
    (ha : ∀ i, ∀ p : (C.auxiliary i).Sample,
      (C.auxiliary i).law.mass p ≠ 0 → Real.log (p:ℕ) ≤ A) :
    ∀ origin, ∀ p : (C.sources origin).Sample,
      (C.sources origin).law.mass p ≠ 0 → Real.log (p:ℕ) ≤ A := by
  apply initialSourceFamily_log_le
  · exact hb
  · exact fun i => ha (.inl i)
  · exact fun j i => ha (.inr (j,i))

theorem selected_sources_factorCap_eventually (d : Decomposition) (Bs BD Bz : ℝ)
    {k : ℕ} (hk : 0 < k) :
    ∀ᶠ L : ℝ in atTop, ∀ (E : Finset ℕ) (C : InitialSourceChoice d Bs BD Bz k L E),
      Real.exp ((1/20:ℝ)*L) ≤ C.blockBase →
      C.blockBase-2 < (C.giantCenter:ℝ) →
      (C.giantCenter:ℝ) < C.blockBase+favorableBlockWidth L+2 →
      |(C.bulkBin:ℝ)| ≤ favorableBlockWidth L/16 →
      |(C.spectatorBin:ℝ)| ≤ favorableBlockWidth L/16 →
      ∀ origin, ∀ p : (C.sources origin).Sample, (C.sources origin).law.mass p ≠ 0 →
        ((p:ℕ):ℝ) ≤ actualFactorCap Bs BD Bz k L := by
  filter_upwards [SourceRangeSeparation.broad_range_gaps_eventually k,
    nominalTotals_eventually Bs BD Bz hk] with L hgap hnom
  intro E C hG hcl hcu hb hd
  have hG0 : 0 ≤ C.blockBase := (Real.exp_pos _).le.trans hG
  have hcenters := hnom C.blockBase C.giantCenter C.bulkBin C.spectatorBin hG0
    ⟨hcl.le,hcu.le⟩ hb hd
  have hh : 1000 ≤ favorableBlockWidth L := by linarith [hgap.2.1]
  have hlog : ∀ origin, ∀ p : (C.sources origin).Sample,
      (C.sources origin).law.mass p ≠ 0 →
        Real.log (p:ℕ) ≤ 3*(2:ℝ)^k*Real.exp ((1/100:ℝ)*L) := by
    apply sources_log_le C
    · intro p hp
      have he := (harmonicBand_log_support C.bulkPositive p).2
      have hsmall : Real.exp ((3/500:ℝ)*L) ≤ Real.exp ((1/100:ℝ)*L) :=
        Real.exp_le_exp.mpr (by nlinarith [hgap.1])
      have hcoef : 1 ≤ 3*(2:ℝ)^k := by
        have hpow : 1 ≤ (2:ℝ)^k := one_le_pow₀ (by norm_num)
        linarith
      exact he.trans (hsmall.trans (le_mul_of_one_le_left (Real.exp_pos _).le hcoef))
    · intro i p hp
      exact (C.cells.auxSource_log_bounds hh hcenters.2.1
        (fun j => hcenters.2.2 j.val j.isLt) E C.deleted_card i p hp).2
  intro origin p hp
  have hpos : (0:ℝ) < (p:ℕ) := by exact_mod_cast (C.sources origin).prime _ p.property |>.pos
  rw [← Real.exp_log hpos]
  apply Real.exp_le_exp.mpr
  apply (hlog origin p hp).trans
  have hC : 3*(2:ℝ)^k ≤ actualFactorConstant Bs BD Bz k := by
    have := scaleLinearConstant_pos Bs BD Bz k
    unfold actualFactorConstant
    linarith
  have hmul := mul_le_mul_of_nonneg_right hC (Real.exp_pos ((1/100:ℝ)*L)).le
  have hnonneg := mul_nonneg (actualFactorConstant_pos Bs BD Bz k).le
    (show 0 ≤ (bulkSize k L:ℝ)+1 by positivity)
  change _ ≤ actualFactorConstant Bs BD Bz k*((bulkSize k L:ℝ)+1) +
    actualFactorConstant Bs BD Bz k*Real.exp ((1/100:ℝ)*L)
  linarith

end Ostmann.Arithmetic.HistorySignedResidues

end

end OAI
