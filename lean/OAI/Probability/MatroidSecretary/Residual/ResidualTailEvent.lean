import OAI.Probability.MatroidSecretary.Residual.ResidualTailExact
import OAI.Probability.MatroidProphet.Main

namespace OAI

/-! Effective tail for the actual deterministic residual-family bad event,
with every outside mask and the parity fixed, but without conditioning on listing. -/

namespace MatroidProphet.SourceProof

open Finset MainAlgorithm Pivots

variable {α : Type*} [DecidableEq α]

/-- Exact effective union bound for an arbitrary deterministic residual family. -/
theorem residualBad_tail_exact (q : α → ℝ)
    (hq0 : ∀ e, 0 ≤ q e) (hqhalf : ∀ e, q e ≤ 1 / 2)
    (V : Finset α) (F : Finset (Finset α)) (hF : ∀ R ∈ F, R ⊆ V)
    (hcard : (F.card : ℝ) ≤ Real.exp
      (1000 * Real.log densityThreshold / densityThreshold * V.card))
    (hn : densityThreshold ≤ (V.card : ℝ)) :
    bitsExpectation q V (residualBadIndicator F (residualDelta * V.card)) ≤
      Real.exp (-((2 : ℝ)^73) * Real.log 2) := by
  calc
    _ ≤ (F.card : ℝ) * Real.exp (-(residualDelta * V.card) * Real.log 2) :=
      bitsExpectation_residualBad_le q hq0 hqhalf V F hF _
    _ ≤ Real.exp (1000 * Real.log densityThreshold / densityThreshold * V.card) *
        Real.exp (-(residualDelta * V.card) * Real.log 2) :=
      mul_le_mul_of_nonneg_right hcard (Real.exp_nonneg _)
    _ = Real.exp ((1000 * Real.log densityThreshold / densityThreshold -
        residualDelta * Real.log 2) * V.card) := by
      rw [← Real.exp_add]
      congr 1
      ring
    _ ≤ _ := (residual_tail_exact (V.card : ℝ) hn).1

/-- The source's conditional bad event for the actual focal residual family.
The fixed data contain H, parity, and all outside coordinates; only the focal
D,C,T coordinates are integrated. Empty discovery outcomes are retained. -/
theorem focalResidualBad_tail_exact {n : ℕ} (M : Matroid (Fin n))
    (hE : M.E = Set.univ) (d : MainMasks n) (s : Fin n → Option ℤ)
    (i : ℤ) (ε : Fin 2)
    (hn : densityThreshold ≤ ((trueGroup M d s i).card : ℝ)) :
    tripleMaskExpectation (fun _ => (1 : ℝ)/4) (fun _ => thinningRate)
      (fun _ => thinningRate) (trueGroup M d s i)
      (fun A B _C => residualBadIndicator (focalResidualFamily M hE (2^100) d s i ε)
        (residualDelta * (trueGroup M d s i).card) (A ∪ B)) ≤
        Real.exp (-((2 : ℝ)^73) * Real.log 2) ∧
      Real.exp (-((2 : ℝ)^73) * Real.log 2) < residualDelta := by
  have hne : (trueGroup M d s i).Nonempty := by
    apply card_pos.mp
    exact_mod_cast lt_of_lt_of_le constants_positive.2.1 hn
  have hcard : ((focalResidualFamily M hE (2^100) d s i ε).card : ℝ) ≤
      Real.exp (1000 * Real.log densityThreshold / densityThreshold *
        (trueGroup M d s i).card) := by
    have hc := labeledResidualFamily_card M hE (trueGroup M d s i) hne (2^100)
      (by norm_num) (guardedPath M hE (2^100)
        (groupMask M (focalReference M d s i) s (focalReference M d s i).D)
        (groupMask M (focalReference M d s i) s (focalReference M d s i).C)
        (focalIndex M d s i)) (activation (focalIndex M d s i)) ε
      (fun b => lowerCompetition M hE (2^100)
        (groupMask M (focalReference M d s i) s (focalReference M d s i).D)
        (groupMask M (focalReference M d s i) s (focalReference M d s i).C)
        (groupMask M (focalReference M d s i) s (focalReference M d s i).T)
        b.val.val (focalIndex M d s i))
    simpa only [Nat.cast_pow, Nat.cast_ofNat, densityThreshold, focalResidualFamily] using hc
  refine ⟨?_, (residual_tail_exact ((trueGroup M d s i).card : ℝ) hn).2⟩
  unfold tripleMaskExpectation
  simp_rw [bitsExpectation_const]
  rw [bitsExpectation_union]
  apply residualBad_tail_exact _ _ _ _ _ _ hcard hn
  · intro e
    norm_num [thinningRate]
  · intro e
    norm_num [thinningRate]
  · exact labeledResidualFamily_subsets M _ _ _ _ ε _

end MatroidProphet.SourceProof

end OAI
