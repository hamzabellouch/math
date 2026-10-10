import OAI.NumberTheory.Ostmann.Arithmetic.HistoryPairMixedReplacementCorrectedBasic

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.Arithmetic.HistoryPairSmoothXi
open Construction Characters.RationalHistory HistoryOccurrenceVariables
open HistoryPairPattern InitialCoordinatesTemplate
open scoped FourierTransform
variable {l : ℕ} {V : ℕ → ℕ} {outside : List ℕ}

def pairedDiagonalHKeys (h k : History l) (j : ℕ) : List (PairKey h k) :=
  (diagonalHKeys k j).map (rightMap h k)

def pairedDiagonalUKeys (h k : History l) (j : ℕ) : List (PairKey h k) :=
  (diagonalUKeys k j).map (rightMap h k)

@[simp] theorem pairedDiagonalHKeys_length (h k : History l) (j : ℕ) :
    (pairedDiagonalHKeys h k j).length = (diagonalHKeys k j).length :=
  List.length_map _

@[simp] theorem pairedDiagonalUKeys_length (h k : History l) (j : ℕ) :
    (pairedDiagonalUKeys h k j).length = (diagonalUKeys k j).length :=
  List.length_map _

def pairedDiagonalCellCenter (k : History l) (j : ℕ) (G : ℝ) (center : ℕ → ℝ) :
    Fin (diagonalCellKeys k j).length → ℝ :=
  fun i => diagonalKeyCenter k G center ((diagonalCellKeys k j).get i)

def pairedDiagonalCellKey (h k : History l) (j : ℕ) :
    Fin (diagonalCellKeys k j).length → PairKey h k :=
  fun i => rightMap h k ((diagonalCellKeys k j).get i)

def pairedRootCounterpart (h k : History l) (j : ℕ) (A B G : ℝ)
    (center : ℕ → ℝ) (x : PairKey h k → ℝ) : ℝ :=
  rootCounterpart A B (pairedDiagonalHKeys h k j) (pairedDiagonalUKeys h k j)
    (Finset.univ : Finset (Fin (diagonalCellKeys k j).length))
    (pairedDiagonalCellCenter k j G center) (pairedDiagonalCellKey h k j) x

theorem pairedRootCounterpart_pullback (h k : History l) (j : ℕ) (A B G : ℝ)
    (center : ℕ → ℝ) (x : PairKey h k → ℝ) :
    pairedRootCounterpart h k j A B G center x =
      diagonalRootCounterpart k j A B G center (x ∘ rightMap h k) := by
  simp only [pairedRootCounterpart, diagonalRootCounterpart, pairedDiagonalHKeys,
    pairedDiagonalUKeys, pairedDiagonalCellKey,
    rootCounterpart, List.map_map, Function.comp_def]
  rfl

theorem pairedRootCounterpart_integer_sample (h k : History l)
    (hgiants : RootGiantsAgree h k)
    (sources : SourceFamily) (T : List SourceSlot) (j : ℕ) (giant : PrimeSource) (p : ℕ)
    (u : SourceAssignment sources (Template.extracted j T))
    (x : RemainingSample sources (Template.remainder j T) giant) (v : ℤ)
    (hroot : k.root = remainingState sources T j giant p u x v)
    (A B G : ℝ) (center : ℕ → ℝ) :
    pairedRootCounterpart h k j A B G center (fun i => (pairSample h k i : ℝ)) =
      remainingCounterpart sources T j giant A B G center u x := by
  rw [pairedRootCounterpart_pullback, rightMap_cast_comp h k hgiants]
  exact diagonalRootCounterpart_integer_sample k sources T j giant p u x v hroot A B G center

theorem correctedPairedRealXi_diagonal_integer_sample
    (b s : ℕ) (X tb td G : ℝ) (h k : History l)
    (hs : h.Supported V outside) (ks : k.Supported V outside)
    (hgiants : RootGiantsAgree h k)
    (sources : SourceFamily) (T : List SourceSlot) (j : ℕ) (giant : PrimeSource) (p : ℕ)
    (u : SourceAssignment sources (Template.extracted j T))
    (x : RemainingSample sources (Template.remainder j T) giant) (v : ℤ)
    (hroot : k.root = remainingState sources T j giant p u x v)
    (A B : ℝ) (center : ℕ → ℝ) :
    correctedPairedRealXi b s X tb td G h k hs ks A B
      (pairedDiagonalHKeys h k j) (pairedDiagonalUKeys h k j)
      (Finset.univ : Finset (Fin (diagonalCellKeys k j).length))
      (pairedDiagonalCellCenter k j G center) (pairedDiagonalCellKey h k j)
      (fun i => (pairSample h k i : ℝ)) =
    (remainingCounterpart sources T j giant A B G center u x : ℂ) *
      (smoothHistoryScalar X (fun t => (𝓕 SchwartzCutoff.psi) t)
        (sourceStateBins b s tb td) outside smoothPartition G h *
      star (smoothHistoryScalar X (fun t => (𝓕 SchwartzCutoff.psi) t)
        (sourceStateBins b s tb td) outside smoothPartition G k)) := by
  change (pairedRootCounterpart h k j A B G center _ : ℂ) *
    pairedRealXi b s X tb td G h k hs ks _ = _
  rw [pairedRootCounterpart_integer_sample h k hgiants sources T j giant p u x v hroot,
    pairedRealXi_integer_sample b s X tb td G h k hs ks hgiants]

end Ostmann.Arithmetic.HistoryPairSmoothXi

end

end OAI
