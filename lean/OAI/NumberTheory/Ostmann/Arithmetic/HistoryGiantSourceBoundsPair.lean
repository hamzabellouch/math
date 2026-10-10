import OAI.NumberTheory.Ostmann.Arithmetic.HistoryActiveSourceDomain
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryPairGiantCoordinatesBasic

namespace OAI

noncomputable section
namespace Ostmann.Arithmetic.HistoryGiantSourceBounds
open Construction HistoryOccurrenceVariables HistorySymbolicEncoding
open HistoryPairPattern HistoryPairGiantCoordinates HistoryActiveCoordinates

theorem left_background_sourceDomain {b k l : ℕ} {G : ℝ} {center : ℕ → ℝ}
    (h g : History l)
    (hh : SourceDomain b k G center h (fun i => (integerSample h i : ℝ))) :
    SourceDomain b k G center h (fun i => pairBackground h g (leftMap h g i)) := by
  simpa only [pairBackground, leftMap_sample] using hh

theorem right_background_sourceDomain {b k l : ℕ} {G : ℝ} {center : ℕ → ℝ}
    (h g : History l)
    (hh : SourceDomain b k G center h (fun i => (integerSample h i : ℝ)))
    (hg : SourceDomain b k G center g (fun i => (integerSample g i : ℝ))) :
    SourceDomain b k G center g (fun i => pairBackground h g (rightMap h g i)) := by
  constructor
  · intro i
    rcases i with a | i
    · rw [← shared_giant]
      simpa only [pairBackground, leftMap_sample] using hh.positive (.inl a)
    · exact hg.positive (.inr i)
  · intro i q hi hq
    rcases i with a | i
    · cases hi
    · exact hg.source (.inr i) q hi hq
  · intro a
    rw [← shared_giant]
    simpa only [pairBackground, leftMap_sample] using hh.giant a
  · exact hg.leaves

theorem left_giant_sourceBounds {b k l : ℕ} {G : ℝ} {center : ℕ → ℝ}
    (h g : History l)
    (hh : SourceDomain b k G center h (fun i => (integerSample h i : ℝ))) :
    SourceBounds b k G center h (leftMap h g) (giantCoordinates h g)
      (pairBackground h g) (fun _ => G-1) (fun _ => G+1) := by
  refine ⟨left_background_sourceDomain h g hh, ?_, ?_⟩
  · intro i q hi hq hm
    rcases i with a | i
    · cases hi
    · exact (left_small_not_mem h g i hm).elim
  · intro a hm
    exact ⟨le_rfl, le_rfl⟩

theorem right_giant_sourceBounds {b k l : ℕ} {G : ℝ} {center : ℕ → ℝ}
    (h g : History l)
    (hh : SourceDomain b k G center h (fun i => (integerSample h i : ℝ)))
    (hg : SourceDomain b k G center g (fun i => (integerSample g i : ℝ))) :
    SourceBounds b k G center g (rightMap h g) (giantCoordinates h g)
      (pairBackground h g) (fun _ => G-1) (fun _ => G+1) := by
  refine ⟨right_background_sourceDomain h g hh hg, ?_, ?_⟩
  · intro i q hi hq hm
    rcases i with a | i
    · cases hi
    · exact (right_small_not_mem h g i hm).elim
  · intro a hm
    exact ⟨le_rfl, le_rfl⟩

end Ostmann.Arithmetic.HistoryGiantSourceBounds

end

end OAI
