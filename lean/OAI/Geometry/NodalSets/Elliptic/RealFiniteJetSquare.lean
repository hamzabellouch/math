import Mathlib.Data.List.OfFn
import OAI.Geometry.NodalSets.Elliptic.RealJetErrorEquation

namespace OAI

namespace Yau.Geometry
open Yau.Analysis
open scoped ContDiff
noncomputable section

def realFiniteJetSquare (W : Yau.Jets.Coord → ℝ) (n : ℕ) (x : Yau.Jets.Coord) : ℝ :=
  ∑ r ∈ Finset.range (n+1), ∑ w : Fin r → Fin 4, (partialJet W (List.ofFn w) x)^2

lemma realFiniteJetSquare_nonneg (W : Yau.Jets.Coord → ℝ) (n : ℕ) (x : Yau.Jets.Coord) :
    0 ≤ realFiniteJetSquare W n x :=
  Finset.sum_nonneg (fun _ _ ↦ Finset.sum_nonneg (fun _ _ ↦ sq_nonneg _))

lemma realFiniteJetSquare_smooth (W : Yau.Jets.Coord → ℝ) (hW : ContDiff ℝ ∞ W) (n : ℕ) :
    ContDiff ℝ ∞ (realFiniteJetSquare W n) :=
  ContDiff.sum (fun _ _ ↦ ContDiff.sum (fun w _ ↦ (partialJet_smooth W hW (List.ofFn w)).pow 2))

lemma partialJet_sq_le_realFiniteJetSquare (W : Yau.Jets.Coord → ℝ) (n : ℕ)
    (ds : List (Fin 4)) (hd : ds.length ≤ n) (x : Yau.Jets.Coord) :
    (partialJet W ds x)^2 ≤ realFiniteJetSquare W n x := by
  have h₁ : (partialJet W ds x)^2 ≤
      ∑ w : Fin ds.length → Fin 4, (partialJet W (List.ofFn w) x)^2 := by
    simpa only [List.ofFn_get] using
      (Finset.single_le_sum (fun w _ ↦ sq_nonneg (partialJet W (List.ofFn w) x))
        (Finset.mem_univ ds.get))
  exact h₁.trans (Finset.single_le_sum (s := Finset.range (n+1)) (a := ds.length)
    (f := fun r ↦ ∑ w : Fin r → Fin 4, (partialJet W (List.ofFn w) x)^2)
    (fun r _ ↦ Finset.sum_nonneg (fun w _ ↦ sq_nonneg (partialJet W (List.ofFn w) x)))
    (Finset.mem_range.mpr (by omega)))

end
end Yau.Geometry

end OAI
