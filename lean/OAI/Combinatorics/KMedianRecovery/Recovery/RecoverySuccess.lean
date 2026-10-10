import Mathlib
import OAI.Combinatorics.KMedianRecovery.Sampling.ZeroFairSuccess
import OAI.Combinatorics.KMedianRecovery.Recovery.RecoveryFeasible

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryRecovery
open Completion FiniteSampling Sampling
attribute [local irreducible] BinaryZeroBranch.output BinaryObservableBranch.output
variable {n H : ℕ} [PseudoMetricSpace (Fin n)]
lemma result_success
    (δ : Fin n→Fin n→ℚ) (hδ : ∀ i j,(δ i j:ℝ)=dist i j)
    (D F S O : Finset (Fin n)) (C : Comparison D S O) (hD : D.Nonempty)
    (hSF : S⊆F) (hOF : O⊆F) (hS : S.Nonempty)
    (Δ : ℚ) (hΔ : 0≤Δ) (hbound : ∀ x,∀ f∈F,δ x f≤Δ)
    (s : RationalSampling.State n) (hs : C.Correct hD (1/1000000) s.real)
    (hP : 0<comparisonCost D C.assign) (hm0 : 0<C.bad.card)
    (hI : C.removalTotal (Δ:ℝ) s.real≤(1/1000000:ℝ)*comparisonCost D C.assign)
    (hN : C.nearTotal (Δ:ℝ) s.real≤(1/1000000:ℝ)*comparisonCost D C.assign)
    (hn : n≤H) (hm : C.bad.card≤H) (hH : 1≤H) (hp : s.leaves.length≤H) (r0 y0 : Fin n) :
    (1/(32*Real.exp 1))^C.bad.card*(3/197:ℝ)≤
      probability (fun seed:Fin (tapeSize H)→Bool=>realCost D
        (result δ D F S Δ s hn hm hH hp r0 y0 seed)≤(197/100:ℝ)*comparisonCost D C.assign) := by
  classical
  let R:=C.nonproxy\s.real.deleted
  let dest:=C.designatedDestination hD s.real (19/50)
  let B:=designatedBlue R dest
  let Q:=designatedRed R dest
  let Z:=B.image (C.blueDestination hD s.real (19/50))
  have hqn : Q.card≤n := (Finset.card_le_univ Q).trans_eq (Fintype.card_fin n)
  have hcn : Z.card≤n := (Finset.card_le_univ Z).trans_eq (Fintype.card_fin n)
  let q : Fin (n+1):=⟨Q.card,Nat.lt_succ_of_le hqn⟩
  let c : Fin (n+1):=⟨Z.card,Nat.lt_succ_of_le hcn⟩
  have hB : B.card≤C.bad.card := by
    apply (Finset.card_filter_le _ _).trans
    rw [←C.nonproxy_card]
    exact Finset.card_le_card Finset.sdiff_subset
  rcases hb : B.card with _|b
  · have hgood := BinaryZeroBranch.fair_zero_completion δ hδ D F S O C hD hSF hOF hS Δ hΔ hbound s hs hP hm0 hI hN hb
    have hevent : (1/(32*Real.exp 1))^C.bad.card*(3/197:ℝ)≤
        probability (fun seed:Fin (tapeSize H)→Bool=>realCost D (zero δ D F S Δ s hn hH hp seed q)≤
          (197/100:ℝ)*comparisonCost D C.assign) := by
      exact hgood.trans_eq (zeroSeed_probability hn hH hp
        (fun z:BinaryRandomizedZeroBranch.Seed n s.leaves.length=>realCost D
          (BinaryZeroBranch.output δ D F S Δ s (fun i=>ColorLabel.color (z.1 i)) q.val z.2)≤
            (197/100:ℝ)*comparisonCost D C.assign)).symm
    apply hevent.trans
    exact probability_mono (fun seed h=>(result_cost_le_zero δ hδ D F S hSF hS Δ hΔ hbound s hn hm hH hp r0 y0 seed q).trans h)
  · have hbm : b<C.bad.card := by omega
    let bi : Fin C.bad.card:=⟨b,hbm⟩
    have hgood := BinaryObservableBranch.fair_color_label_completion δ hδ D F S O C hD hSF hOF hS Δ hΔ hbound s hs hP hm0 hI hN
      (b+1) (by omega) hb r0 y0
    have hevent : (1/(32*Real.exp 1))^C.bad.card*(3/197:ℝ)≤
        probability (fun seed:Fin (tapeSize H)→Bool=>realCost D (positive δ D F S Δ s hn hm hp r0 y0 seed q c bi)≤
          (197/100:ℝ)*comparisonCost D C.assign) := by
      exact hgood.trans_eq (positiveSeed_probability hn hm hp bi
        (fun z:BinaryBranchTape.Seed n (b+1) s.leaves.length=>realCost D
          (BinaryObservableBranch.output δ D F S Δ s (fun i=>ColorLabel.color (z.1.1 i))
            (fun i=>ColorLabel.label (b+1) (by omega) (z.1.2 i)) q.val c.val r0 y0 z.2)≤
              (197/100:ℝ)*comparisonCost D C.assign)).symm
    apply hevent.trans
    exact probability_mono (fun seed h=>(result_cost_le_positive δ hδ D F S hSF hS Δ hΔ hbound s hn hm hH hp r0 y0 seed q c bi).trans h)
end MetricKMedianRecovery.BitMachine.BinaryRecovery

end OAI
