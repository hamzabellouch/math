import OAI.NumberTheory.Ostmann.Arithmetic.HistorySignedFrequencyUnits
import OAI.NumberTheory.Ostmann.Arithmetic.HistorySignedNumeratorsBasic
import OAI.NumberTheory.Ostmann.Arithmetic.HistorySignedSpectatorSupport
import OAI.NumberTheory.Ostmann.Arithmetic.HistorySupportReductionLocal

namespace OAI

noncomputable section
namespace Ostmann.Arithmetic.HistorySignedResidueFactorization
open Construction HistorySignedDecode HistorySignedSupportReduction
open HistoryOccurrenceVariables HistorySignedNumerators HistoryFrequencyResidues

def RootFrequencyGiantCoprime {l : ℕ} (h : SignedHistory l) : Prop :=
  ∀ v ∈ frequencies h, Nat.Coprime h.root.giantPlus.natAbs v.natAbs ∧
    Nat.Coprime h.root.giantMinus.natAbs v.natAbs

def FrequencyGiantCoprime : {l : ℕ} → SignedHistory l → Prop
  | _, .leaf a => RootFrequencyGiantCoprime (.leaf a)
  | _, .node a p u hp hm left right =>
    RootFrequencyGiantCoprime (.node a p u hp hm left right) ∧
      FrequencyGiantCoprime left ∧ FrequencyGiantCoprime right

def PivotOutsideCoprime (outside : List ℕ) : {l : ℕ} → SignedHistory l → Prop
  | _, .leaf _ => True
  | _, .node _ p _ _ _ left right =>
    (∀ q ∈ outside, Nat.Coprime p.natAbs q) ∧
      PivotOutsideCoprime outside left ∧ PivotOutsideCoprime outside right

theorem _root_.OAI.Ostmann.Arithmetic.HistorySignedSpectator.OutsideUnits.pivotOutsideCoprime
    {outside : List ℕ} {l : ℕ} {h : SignedHistory l}
    (ho : HistorySignedSpectator.OutsideUnits outside h) : PivotOutsideCoprime outside h := by
  induction h with
  | leaf a => trivial
  | node a p u hp hm left right ihl ihr => exact ⟨ho.2.1, ihl ho.2.2.1, ihr ho.2.2.2⟩

theorem currentGiantUnits_of_frequencyGiantCoprime {l : ℕ}
    (h : SignedHistory l) (hf : FrequencyGiantCoprime h) : CurrentGiantUnits h := by
  have hroot {j : ℕ} (sh : SignedHistory j) (hu : RootFrequencyGiantCoprime sh) :
      IsUnit (sh.root.giantPlus : ZMod sh.root.frequency.natAbs) ∧
        IsUnit (sh.root.giantMinus : ZMod sh.root.frequency.natAbs) := by
    have hmem : sh.root.frequency ∈ frequencies sh := by
      cases sh <;> exact List.mem_cons_self
    have hc := hu _ hmem
    constructor
    · rw [ZMod.coe_int_isUnit_iff_isCoprime, Int.isCoprime_iff_nat_coprime,
        Int.natAbs_natCast]
      exact hc.1.symm
    · rw [ZMod.coe_int_isUnit_iff_isCoprime, Int.isCoprime_iff_nat_coprime,
        Int.natAbs_natCast]
      exact hc.2.symm
  induction h with
  | leaf a => exact hroot _ hf
  | node a p u hp hm left right ihl ihr => exact ⟨hroot _ hf.1, ihl hf.2.1, ihr hf.2.2⟩

theorem rootArithmetic_rebuild_iff {l : ℕ} {V : ℕ → ℕ} {outside : List ℕ}
    (h : History l) (hs : h.Supported V outside) (Xp Xm : ℤ) :
    RootArithmetic V (rebuild h Xp Xm) ↔ RootFrequencyGiantCoprime (rebuild h Xp Xm) := by
  have hd := HistorySupportReduction.rootData_of_supported hs
  change _ ↔ ∀ v ∈ frequencies (rebuild h Xp Xm), _
  simp only [RootArithmetic, rebuild_root]
  exact ⟨fun hh => hh.2.2.2.2, fun hh => ⟨hd.2.1, hd.2.2.1, hd.2.2.2.1,
    hd.2.2.2.2.1, hh⟩⟩

theorem numeratorSquares_node_iff {l : ℕ} (a : State) (p : ℕ)
    (u hp hm : List SmallSlot) (left right : History l) (Xp Xm : ℤ) :
    (∀ i : InternalKey (.node a p u hp hm left right),
      ¬((internalSlot (.node a p u hp hm left right) i).value : ℤ)^2 ∣
        actual (.node a p u hp hm left right) Xp Xm i) ↔
    (∀ b ∈ u, ¬(b.value : ℤ)^2 ∣ reversalNumerator left.root.frequency right.root.frequency
      (Xp*((hp.map SmallSlot.value).prod : ℤ)) (Xm*((hm.map SmallSlot.value).prod : ℤ))) ∧
    (∀ i, ¬((internalSlot left i).value : ℤ)^2 ∣ actual left
      (signedPivot ⟨a.frequency,Xp,Xm,a.small⟩ left.root.frequency right.root.frequency u hp hm) Xp i) ∧
    (∀ i, ¬((internalSlot right i).value : ℤ)^2 ∣ actual right
      (signedPivot ⟨a.frequency,Xp,Xm,a.small⟩ left.root.frequency right.root.frequency u hp hm) Xm i) := by
  simp only [InternalKey, Sum.forall, internalSlot, actual_node, Sum.elim_inl, Sum.elim_inr]
  constructor
  · rintro ⟨hu, hl, hr⟩
    refine ⟨?_, hl, hr⟩
    intro b hb
    obtain ⟨i, rfl⟩ := List.mem_iff_get.mp hb
    exact hu i
  · rintro ⟨hu, hl, hr⟩
    exact ⟨fun i => hu _ (List.get_mem _ _), hl, hr⟩

theorem arithmeticGuards_rebuild_iff {l : ℕ} {V : ℕ → ℕ} {outside : List ℕ}
    (h : History l) (hs : h.Supported V outside)
    (hlarge : HistorySupportReduction.LargePrimes V h) (Xp Xm : ℤ) :
    ArithmeticGuards V outside (rebuild h Xp Xm) ↔
      FrequencyGiantCoprime (rebuild h Xp Xm) ∧
      (∀ i : InternalKey h, ¬((internalSlot h i).value : ℤ)^2 ∣ actual h Xp Xm i) ∧
      PivotOutsideCoprime outside (rebuild h Xp Xm) := by
  induction h generalizing Xp Xm with
  | leaf a =>
    have hr := rootArithmetic_rebuild_iff (.leaf a) hs Xp Xm
    simp only [rebuild] at hr
    rw [ArithmeticGuards.eq_def]
    simp only [rebuild]
    rw [hr]
    simp [FrequencyGiantCoprime, PivotOutsideCoprime, InternalKey]
  | @node l a p u hp hm left right ihl ihr =>
    have ht := HistorySupportReduction.localTests_of_supported_node hs hlarge.2.1
    have hr := rootArithmetic_rebuild_iff (.node a p u hp hm left right) hs Xp Xm
    simp only [rebuild] at hr
    rw [ArithmeticGuards.eq_def]
    simp only [rebuild]
    rw [hr]
    simp only [FrequencyGiantCoprime, PivotOutsideCoprime, rebuild_root,
      LocalArithmetic]
    rw [ihl (History.supported_left hs) hlarge.2.2.1,
      ihr (History.supported_right hs) hlarge.2.2.2]
    rw [numeratorSquares_node_iff]
    simp only [pow_two]
    constructor
    · rintro ⟨hr, ⟨hn, hp, hsq, ho, hc⟩, hl, hright⟩
      exact ⟨⟨hr, hl.1, hright.1⟩, ⟨hsq, hl.2.1, hright.2.1⟩, ho, hl.2.2, hright.2.2⟩
    · rintro ⟨⟨hr, hl, hright⟩, ⟨hsq, hsl, hsr⟩, ho, hol, hor⟩
      exact ⟨hr, ⟨ht.1, ht.2.1, hsq, ho, ht.2.2.2.2⟩, ⟨hl, hsl, hol⟩,
        ⟨hright, hsr, hor⟩⟩

end Ostmann.Arithmetic.HistorySignedResidueFactorization

end

end OAI
