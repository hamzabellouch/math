import OAI.LinearAlgebra.MatrixMultiplication.FieldHistory.IncomingCore
import OAI.LinearAlgebra.MatrixMultiplication.FieldHistory.MaskLaws
import OAI.LinearAlgebra.MatrixMultiplication.FieldHistory.RawMasks
import OAI.LinearAlgebra.MatrixMultiplication.FieldHistory.StageCIncoming
import OAI.LinearAlgebra.MatrixMultiplication.FieldHistory.Tensors

namespace OAI

/-! Finite extraction histories, inherited masks and recovery bounds. -/

noncomputable section

namespace MatrixMultiplication.AllFieldHistoryIncomingMasks

open MatrixMultiplication.Foundation AllFieldHistory AllFieldParameters
open AllFieldHistoryChildLaws AllFieldHistorySupport AllFieldHistoryMasks
open AllFieldHistoryMaskLaws AllFieldHistoryRawMasks InheritedMasks
open scoped BigOperators
attribute [local instance] Classical.propDecidable Classical.decEq

variable {K tick : ℕ}

theorem empiricalLaw_congr_decidable {P A : Type*} [Fintype P]
    (d₁ d₂ : DecidableEq A) (w : P → A) (a : A) :
    @empiricalLaw P A _ d₁ w a = @empiricalLaw P A _ d₂ w a := by
  cases Subsingleton.elim d₁ d₂
  rfl

theorem typeWindow_mono_decidable {P A : Type*} [Fintype P]
    (d₁ d₂ : DecidableEq A) (ν : A → ℝ) {η δ : ℝ} (hη : η ≤ δ)
    (w : P → A) (hw : @typeWindow P A _ d₁ ν η w) :
    @typeWindow P A _ d₂ ν δ w := by
  cases Subsingleton.elim d₁ d₂
  intro a
  exact (hw a).trans hη

theorem weight_append {m n : ℕ} (l : Fin m → Fin 7) (r : Fin n → Fin 7) :
    CWStrands.weight (Fin.append l r) = CWStrands.weight l + CWStrands.weight r := by
  simp [CWStrands.weight, Fin.sum_univ_add]

theorem strand_append {F : Type*} [CommRing F] {m n : ℕ}
    (x y z : (Fin m → Fin 7) × (Fin n → Fin 7)) :
    CWStrands.strand (F := F) (Fin (m + n))
      (Fin.append x.1 x.2) (Fin.append y.1 y.2) (Fin.append z.1 z.2) =
        CWStrands.strand (Fin m) x.1 y.1 z.1 * CWStrands.strand (Fin n) x.2 y.2 z.2 := by
  simp [CWStrands.strand, Fin.prod_univ_add]

theorem shapeTensor_append {F : Type*} [CommRing F] {m n : ℕ} (g : Shape)
    (x y z : (Fin m → Fin 7) × (Fin n → Fin 7)) :
    CWStrands.shapeTensor (F := F) (Fin (m + n)) g
      (Fin.append x.1 x.2) (Fin.append y.1 y.2) (Fin.append z.1 z.2) =
        CWStrands.shapeTensor (Fin m ⊕ Fin n) g
          (Sum.elim x.1 x.2) (Sum.elim y.1 y.2) (Sum.elim z.1 z.2) := by
  simp only [CWStrands.shapeTensor, weight_append, CWStrands.weight_sum_elim,
    strand_append, CWStrands.strand_sum_elim, Tensor.product]

theorem shapeTensor_joinHalves {F : Type*} [CommRing F] (w : Work K) (g : Shape)
    (x y z : (Fin w.halfLength → Fin 7) × (Fin w.halfLength → Fin 7)) :
    CWStrands.shapeTensor (F := F) (Fin (currentLength w.source)) g
      (joinHalves w x) (joinHalves w y) (joinHalves w z) =
        CWStrands.shapeTensor (Fin w.halfLength ⊕ Fin w.halfLength) g
          (Sum.elim x.1 x.2) (Sum.elim y.1 y.2) (Sum.elim z.1 z.2) := by
  cases w <;> exact shapeTensor_append g x y z

def defaultStatistic : (w : Work K) → w.Statistic
  | .stageA _ => (0, 0)
  | .stageB _ => (0 : Fin 6)
  | .stageC _ => PUnit.unit

def choiceAt (h : Active K tick) (a : Statistic h) : SymbolChoice K tick :=
  Function.update (fun g => defaultStatistic g.val.1) h a

@[simp] theorem choiceAt_self (h : Active K tick) (a : Statistic h) :
    choiceAt h a h = a := by simp [choiceAt]

theorem rawPairCount_eq_wordPopulation (allocation : Allocation) (m : ℕ)
    (i : MaskIndex K tick) (w : ActiveRawPairs (K := K) (tick := tick) allocation m) :
    rawPairCount allocation m i w =
      (wordPopulation (fun j => (statistic i.1 (w i.1 j).1,
        statistic i.1 (w i.1 j).2)) (i.2.1 i.1, i.2.2 i.1) : ℝ) := by
  simp only [rawPairCount, wordPopulation, Fintype.card_subtype,
    Finset.natCast_card_filter, Prod.mk.injEq]

@[simp] theorem fourStatistic_append (l r : Fin 2 → Fin 7) :
    CWCompleteStatistics.fourStatistic (Fin.append l r) =
      (CWCompleteStatistics.twoStatistic l, CWCompleteStatistics.twoStatistic r) := rfl

@[simp] theorem append_singletons (l r : Fin 1 → Fin 7) :
    Fin.append l r = ![l 0, r 0] := by
  funext i
  fin_cases i <;> rfl

theorem rawPass_stageB_typeWindow (allocation : Allocation) (m : ℕ) (ε : ℝ)
    (side : Fin 3) (w : ActiveRawPairs (K := K) (tick := tick) allocation m)
    (hw : rawPass allocation m ε side w) (h : APositive K) (phi : Placement)
    (ht : FiniteSchedule.lotTick (Work.stageB h).lot (Work.stageB h).stage = tick) :
    typeWindow (fun ij : PairSlot => (halfLaw (aShape h.val) (phi.symm side) ij : ℝ))
      (pairWidth ε (stageBActive h phi ht))
      (fun j => CWCompleteStatistics.fourStatistic
        (joinHalves (.stageB h) (w (stageBActive h phi ht) j))) := by
  intro ij
  have hp := hw (stageBActive h phi ht,
    choiceAt (stageBActive h phi ht) ij.1, choiceAt (stageBActive h phi ht) ij.2)
  rw [center_stageB] at hp
  simp only [choiceAt_self (stageBActive h phi ht) ij.1,
    choiceAt_self (stageBActive h phi ht) ij.2] at hp
  have hcard : Fintype.card (JointPopulation.Positions (activeCounts allocation m)
      (stageBActive h phi ht)) = population allocation m
        ((stageBActive h phi ht).val.1.source, (stageBActive h phi ht).val.2) := by
    exact (Fintype.card_congr
      (sourcePositionsEquiv allocation m (stageBActive h phi ht))).trans
        (Fintype.card_fin _)
  have hcount : (wordPopulation (fun j =>
      (statistic (stageBActive h phi ht) (w (stageBActive h phi ht) j).1,
        statistic (stageBActive h phi ht) (w (stageBActive h phi ht) j).2)) ij : ℝ) =
      rawPairCount allocation m (stageBActive h phi ht,
        choiceAt (stageBActive h phi ht) ij.1, choiceAt (stageBActive h phi ht) ij.2) w := by
    rcases ij with ⟨a, b⟩
    simp only [wordPopulation, Fintype.card_subtype,
      Finset.natCast_card_filter, rawPairCount]
    apply Finset.sum_congr rfl
    intro j _
    apply if_congr
    · simp only [choiceAt_self (stageBActive h phi ht) a,
        choiceAt_self (stageBActive h phi ht) b]
      exact Prod.mk_inj
    · rfl
    · rfl
  have hword : (fun j => CWCompleteStatistics.fourStatistic
      (joinHalves (.stageB h) (w (stageBActive h phi ht) j))) =
      (fun j => (statistic (stageBActive h phi ht) (w (stageBActive h phi ht) j).1,
        statistic (stageBActive h phi ht) (w (stageBActive h phi ht) j).2)) := by
    funext j
    rfl
  have he : empiricalLaw (fun j => CWCompleteStatistics.fourStatistic
      (joinHalves (.stageB h) (w (stageBActive h phi ht) j))) ij =
      empiricalLaw (fun j =>
        (statistic (stageBActive h phi ht) (w (stageBActive h phi ht) j).1,
          statistic (stageBActive h phi ht) (w (stageBActive h phi ht) j).2)) ij := by
    rw [hword]
    exact empiricalLaw_congr_decidable _ _ _ _
  rw [he]
  unfold empiricalLaw
  rw [hcard, hcount]
  exact hp

attribute [local irreducible] activeCounts population

theorem incoming_stageA (allocation : Allocation) (m : ℕ) (ε : ℝ)
    (side : Fin 3) (w : ActiveRawPairs (K := K) (tick := tick) allocation m)
    (h : InitialPositive K) (phi : Placement)
    (ht : FiniteSchedule.lotTick (Work.stageA h).lot (Work.stageA h).stage = tick) :
    residentMask allocation m ε ((Work.stageA h).source, phi) side
      (incomingWord allocation m ⟨(.stageA h, phi), ht⟩ w) := by
  trivial

theorem incoming_stageB (allocation : Allocation) (m : ℕ) {ε : ℝ} (hε : 0 ≤ ε)
    (side : Fin 3) (w : ActiveRawPairs (K := K) (tick := tick) allocation m)
    (hw : rawPass allocation m ε side w) (h : APositive K) (phi : Placement)
    (ht : FiniteSchedule.lotTick (Work.stageB h).lot (Work.stageB h).stage = tick) :
    residentMask allocation m ε ((Work.stageB h).source, phi) side
      (incomingWord allocation m (stageBActive h phi ht) w) := by
  intro _
  have hraw := rawPass_stageB_typeWindow allocation m ε side w hw h phi ht
  have htransport := (JointCanonicalization.typeWindow_reindex
    (fun ij : PairSlot => (halfLaw (aShape h.val) (phi.symm side) ij : ℝ))
    (pairWidth ε (stageBActive h phi ht))
    (fun j => CWCompleteStatistics.fourStatistic
      (joinHalves (.stageB h) (w (stageBActive h phi ht) j)))
    (sourcePositionsEquiv allocation m (stageBActive h phi ht)).symm).2 hraw
  have hwidth : pairWidth ε (stageBActive h phi ht) ≤ ε / 8 := by
    change ε / 16 ^ 1 ≤ ε / 8
    norm_num
    linarith
  dsimp only [Work.source, residentLaw, residentLawRat, residentWidth, residentStatistic]
  exact typeWindow_mono_decidable _ _ _ hwidth _ htransport

theorem incoming_stageC (allocation : Allocation) {m : ℕ} (hm : 0 < m)
    {ε : ℝ} (hε : 0 ≤ ε) (side : Fin 3)
    (e : JointPopulation.Target (activeCounts (K := K) (tick := tick) allocation m))
    (w : ActiveRawPairs (K := K) (tick := tick) allocation m)
    (h : PartC K) (phi : Placement)
    (ht : FiniteSchedule.lotTick (Work.stageC h).lot (Work.stageC h).stage = tick)
    (hweights : ∀ j,
      CWLeafStatistics.weight ((w (AllFieldHistoryStageCIncoming.stageCActive h phi ht) j).1 (0 : Fin 1)) =
        (JointPopulation.shapeSide side ((e (AllFieldHistoryStageCIncoming.stageCActive h phi ht)).val j)).val ∧
      CWLeafStatistics.weight ((w (AllFieldHistoryStageCIncoming.stageCActive h phi ht) j).2 (0 : Fin 1)) =
        activeParentShape (AllFieldHistoryStageCIncoming.stageCActive h phi ht) side -
          (JointPopulation.shapeSide side ((e (AllFieldHistoryStageCIncoming.stageCActive h phi ht)).val j)).val) :
    residentMask allocation m ε ((Work.stageC h).source, phi) side
      (incomingWord allocation m (AllFieldHistoryStageCIncoming.stageCActive h phi ht) w) := by
  intro _
  have hraw := AllFieldHistoryStageCIncoming.typeWindow_of_target_side_weights
    allocation hm h phi ht e w side hweights (ε / 256) (div_nonneg hε (by norm_num))
  have hword :
      (fun j => CWCompleteStatistics.twoStatistic
        (joinHalves (.stageC h)
          (w (AllFieldHistoryStageCIncoming.stageCActive h phi ht) j))) =
      (fun j => CWCompleteStatistics.twoStatistic
        ![(w (AllFieldHistoryStageCIncoming.stageCActive h phi ht) j).1 (0 : Fin 1),
          (w (AllFieldHistoryStageCIncoming.stageCActive h phi ht) j).2 (0 : Fin 1)]) := by
    funext j
    exact congrArg CWCompleteStatistics.twoStatistic (append_singletons _ _)
  rw [← hword] at hraw
  have htransport := (JointCanonicalization.typeWindow_reindex
    (fun a : Fin 6 => (littleLaw (cParameterParent h) (cShapeParent h) (phi.symm side) a : ℝ))
    (ε / 256)
    (fun j => CWCompleteStatistics.twoStatistic
      (joinHalves (.stageC h)
        (w (AllFieldHistoryStageCIncoming.stageCActive h phi ht) j)))
    (sourcePositionsEquiv allocation m (AllFieldHistoryStageCIncoming.stageCActive h phi ht)).symm).2 hraw
  exact typeWindow_mono_decidable _ _ _ le_rfl _ htransport

def stageCWeights (allocation : Allocation) (m : ℕ) (side : Fin 3)
    (e : JointPopulation.Target (activeCounts (K := K) (tick := tick) allocation m))
    (w : ActiveRawPairs (K := K) (tick := tick) allocation m) : Prop :=
  ∀ (h : PartC K) (phi : Placement)
    (ht : FiniteSchedule.lotTick (Work.stageC h).lot (Work.stageC h).stage = tick) j,
      CWLeafStatistics.weight ((w (AllFieldHistoryStageCIncoming.stageCActive h phi ht) j).1 (0 : Fin 1)) =
        (JointPopulation.shapeSide side ((e (AllFieldHistoryStageCIncoming.stageCActive h phi ht)).val j)).val ∧
      CWLeafStatistics.weight ((w (AllFieldHistoryStageCIncoming.stageCActive h phi ht) j).2 (0 : Fin 1)) =
        activeParentShape (AllFieldHistoryStageCIncoming.stageCActive h phi ht) side -
          (JointPopulation.shapeSide side ((e (AllFieldHistoryStageCIncoming.stageCActive h phi ht)).val j)).val

theorem received_of_rawPass (allocation : Allocation) {m : ℕ} (hm : 0 < m)
    {ε : ℝ} (hε : 0 ≤ ε) (side : Fin 3)
    (e : JointPopulation.Target (activeCounts (K := K) (tick := tick) allocation m))
    (w : ActiveRawPairs (K := K) (tick := tick) allocation m)
    (hw : rawPass allocation m ε side w) (hc : stageCWeights allocation m side e w) :
    received allocation m ε side w := by
  rintro ⟨⟨work, phi⟩, ht⟩
  cases work with
  | stageA h => exact incoming_stageA allocation m ε side w h phi ht
  | stageB h => exact incoming_stageB allocation m hε side w hw h phi ht
  | stageC h => exact incoming_stageC allocation hm hε side e w h phi ht (hc h phi ht)

end MatrixMultiplication.AllFieldHistoryIncomingMasks

end

end OAI
