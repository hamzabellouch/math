import Mathlib
import OAI.Combinatorics.KMedianRecovery.Branching.DesignatedBranchSuccess

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryZeroBranch
open Completion Categorical FiniteSampling BinaryBranchContext Sampling BinaryBranchProgram
variable {n : ℕ} [PseudoMetricSpace (Fin n)]
lemma fair_zero_completion
    (δ : Fin n→Fin n→ℚ) (hδ : ∀ i j,(δ i j:ℝ)=dist i j)
    (D F S O : Finset (Fin n)) (C : Comparison D S O) (hD : D.Nonempty)
    (hSF : S⊆F) (hOF : O⊆F) (hS : S.Nonempty)
    (Δ : ℚ) (hΔ : 0≤Δ) (hbound : ∀ x,∀ f∈F,δ x f≤Δ)
    (s : RationalSampling.State n) (hs : C.Correct hD (1/1000000) s.real)
    (hP : 0<comparisonCost D C.assign) (hm : 0<C.bad.card)
    (hI : C.removalTotal (Δ:ℝ) s.real≤(1/1000000:ℝ)*comparisonCost D C.assign)
    (hN : C.nearTotal (Δ:ℝ) s.real≤(1/1000000:ℝ)*comparisonCost D C.assign)
    (hcard : (designatedBlue (C.nonproxy\s.real.deleted) (C.designatedDestination hD s.real (19/50))).card=0) :
    let q:=(designatedRed (C.nonproxy\s.real.deleted) (C.designatedDestination hD s.real (19/50))).card
    (1/(32*Real.exp 1))^C.bad.card*(3/197:ℝ)≤
      probability (fun seed : (Fin n→Fin 4) × BinaryObservableBranch.Bits n s.leaves.length=>
        realCost D (output δ D F S Δ s (fun u=>ColorLabel.color (seed.1 u)) q seed.2)≤
          (197/100:ℝ)*comparisonCost D C.assign) := by
  classical
  dsimp only
  let R := C.nonproxy \ s.real.deleted
  let dest := C.designatedDestination hD s.real (19/50)
  let Q := R ∪ designatedProxies R dest
  let PC : (Fin n → Fin 4) → Prop := fun seed =>
    ∀ i ∈ Q, ColorLabel.color (seed i) = requiredColors R dest i
  have hR : R.card ≤ C.bad.card := by
    rw [← C.nonproxy_card]
    exact Finset.card_le_card Finset.sdiff_subset
  have hQ : Q.card ≤ 2*C.bad.card := color_requirement_count R dest C.bad.card hR
  have hc : (1/4:ℝ)^Q.card ≤ probability PC :=
    ColorLabel.color_event_probability Q (requiredColors R dest)
  have hexp : 1 ≤ Real.exp (1:ℝ) := Real.one_le_exp (by norm_num)
  have hbase : 1/(32*Real.exp (1:ℝ)) ≤ 1/16 := by
    rw [div_le_div_iff₀ (by positivity : 0 < 32*Real.exp (1:ℝ)) (by norm_num : (0:ℝ)<16)]
    linarith
  have hp : (1/(32*Real.exp 1))^C.bad.card ≤ probability PC := by
    calc
      _ ≤ (1/16:ℝ)^C.bad.card := pow_le_pow_left₀ (by positivity) hbase _
      _ = (1/4:ℝ)^(2*C.bad.card) := by rw [pow_mul]; norm_num
      _ ≤ (1/4:ℝ)^Q.card := pow_le_pow_of_le_one (by norm_num) (by norm_num) hQ
      _ ≤ probability PC := hc
  apply (mul_le_mul_of_nonneg_right hp (by norm_num : (0:ℝ) ≤ 3/197)).trans
  refine probability_prod_lower PC
    (fun seed bits => realCost D (output δ D F S Δ s
      (fun u => ColorLabel.color (seed u)) (designatedRed R dest).card bits) ≤
        (197/100:ℝ)*comparisonCost D C.assign) ?_
  intro seed hseed
  exact successful_probability δ hδ D F S O C hD hSF hOF hS Δ hΔ hbound s hs hP hm hI hN
    (fun u=>ColorLabel.color (seed u)) hseed hcard
end MetricKMedianRecovery.BitMachine.BinaryZeroBranch

end OAI
