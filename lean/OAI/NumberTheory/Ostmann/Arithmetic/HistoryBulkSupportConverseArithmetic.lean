import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkSupportConverseKnown

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.Arithmetic.HistoryBulkSupportConverse
open Construction HistorySignedDecode HistorySignedSupportReduction
open HistoryOccurrenceVariables HistorySignedNumerators HistoryFrequencyResidues
open HistorySignedResidueFactorization

theorem internalOutside_node_iff {l : ℕ} {a : State} {p : ℕ}
    {u hp hm : List SmallSlot} {left right : History l} {outside : List ℕ} :
    (∀ i : InternalKey (.node a p u hp hm left right), ∀q∈outside,
      Nat.Coprime (internalSlot (.node a p u hp hm left right) i).value q) ↔
    (∀b∈u,∀q∈outside,Nat.Coprime b.value q) ∧
    (∀i : InternalKey left,∀q∈outside,Nat.Coprime (internalSlot left i).value q) ∧
    (∀i : InternalKey right,∀q∈outside,Nat.Coprime (internalSlot right i).value q) := by
  simp only [InternalKey, Sum.forall, internalSlot, Sum.elim_inl, Sum.elim_inr]
  constructor
  · rintro ⟨hu,hl,hr⟩
    refine ⟨?_,hl,hr⟩
    intro b hb
    obtain ⟨i,rfl⟩ := List.mem_iff_get.mp hb
    exact hu i
  · rintro ⟨hu,hl,hr⟩
    exact ⟨fun i=>hu _ (List.get_mem _ _),hl,hr⟩

theorem rootArithmetic_rebuild_iff_static {l : ℕ} {V : ℕ → ℕ}
    (h : History l) (hs : StaticSkeleton V h) (Xp Xm : ℤ) :
    RootArithmetic V (rebuild h Xp Xm) ↔ RootFrequencyGiantCoprime (rebuild h Xp Xm) := by
  have hd := hs.root
  change _ ↔ ∀ v ∈ frequencies (rebuild h Xp Xm), _
  simp only [RootArithmetic, rebuild_root]
  exact ⟨fun hh => hh.2.2.2.2, fun hh => ⟨hd.primeSmall, hd.templateAt, hd.frequency_ne_zero,
    hd.frequency_bound, hh⟩⟩

theorem arithmeticGuards_rebuild_iff_static {l : ℕ} {V : ℕ → ℕ} {outside : List ℕ}
    (h : History l) (hs : StaticSkeleton V h)
    (hout : ∀ i : InternalKey h, ∀ q∈outside, Nat.Coprime (internalSlot h i).value q)
    (Xp Xm : ℤ) :
    ArithmeticGuards V outside (rebuild h Xp Xm) ↔
      FrequencyGiantCoprime (rebuild h Xp Xm) ∧
      (∀ i : InternalKey h, ¬((internalSlot h i).value : ℤ)^2 ∣ actual h Xp Xm i) ∧
      PivotOutsideCoprime outside (rebuild h Xp Xm) := by
  induction h generalizing Xp Xm with
  | leaf a =>
    have hr := rootArithmetic_rebuild_iff_static (.leaf a) hs Xp Xm
    simp only [rebuild] at hr
    rw [ArithmeticGuards.eq_def]
    simp only [rebuild]
    rw [hr]
    simp [FrequencyGiantCoprime, PivotOutsideCoprime, InternalKey]
  | @node l a p u hp hm left right ihl ihr =>
    obtain ⟨huc, hlc, hrc⟩ := internalOutside_node_iff.mp hout
    have hr := rootArithmetic_rebuild_iff_static (.node a p u hp hm left right) hs Xp Xm
    simp only [rebuild] at hr
    rw [ArithmeticGuards.eq_def]
    simp only [rebuild]
    rw [hr]
    simp only [FrequencyGiantCoprime, PivotOutsideCoprime, rebuild_root,
      LocalArithmetic]
    rw [ihl hs.2.2.1 hlc,
      ihr hs.2.2.2 hrc]
    rw [numeratorSquares_node_iff]
    simp only [pow_two]
    constructor
    · rintro ⟨hr, ⟨hn, hp, hsq, ho, hc⟩, hl, hright⟩
      exact ⟨⟨hr, hl.1, hright.1⟩, ⟨hsq, hl.2.1, hright.2.1⟩, ho, hl.2.2, hright.2.2⟩
    · rintro ⟨⟨hr, hl, hright⟩, ⟨hsq, hsl, hsr⟩, ho, hol, hor⟩
      exact ⟨hr, ⟨hs.2.1.distinctComp, hs.2.1.primeComp, hsq, ho, huc⟩, ⟨hl, hsl, hol⟩,
        ⟨hright, hsr, hor⟩⟩

end Ostmann.Arithmetic.HistoryBulkSupportConverse

end

end OAI
