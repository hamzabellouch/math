import Mathlib
import OAI.Combinatorics.KMedianRecovery.Recovery.HitsState
import OAI.Combinatorics.KMedianRecovery.Sampling.SamplerLaw

namespace OAI

namespace MetricKMedianRecovery.RationalSampling
open Sampling Sampling.Comparison Guided FiniteSampling RadiusMenus
variable {n : ℕ} [PseudoMetricSpace (Fin n)]
lemma prefix_success (δ : Fin n→Fin n→ℚ) (hδ : ∀ i j,(δ i j:ℝ)=dist i j)
    (D S O : Finset (Fin n)) (C : Comparison D S O) (hD : D.Nonempty)
    (F : Finset (Fin n)) (hOF : O⊆F) (hSF : S⊆F)
    (Δ P : ℚ) (hΔ : (1:ℚ)≤Δ) (hPeq : (P:ℝ)=comparisonCost D C.assign)
    (hsep : ∀ w∈D,∀ f∈F,(1:ℝ)≤dist w f)
    (hP : 0<comparisonCost D C.assign) (hm : 0<C.bad.card) :
    (1/2:ℝ)^(2*C.bad.card)*samplingBound C.bad.card ≤
      probability (fun bits : Fin (2*C.bad.card)→Fin (integralPrecision D (Δ:ℝ) C.bad.card)→Bool =>
        ∃ i : Fin (2*C.bad.card+1), C.stop hD (Δ:ℝ)
          ((((List.ofFn bits).take i.val).foldl
            (next δ D F S Δ P (1/1000000) C.bad.card (firstSize mainKappa)
              (geometricCap mainKappa mainKappa_pos) (thirdSize mainKappa C.bad.card)
              (integralPrecision D (Δ:ℝ) C.bad.card)) (some State.initial)).map State.real)) := by
  rw [trace_probability δ hδ D F S hD Δ P (1/1000000) C.bad.card (firstSize mainKappa)
    (geometricCap mainKappa mainKappa_pos) (thirdSize mainKappa C.bad.card)
    (integralPrecision D (Δ:ℝ) C.bad.card) (2*C.bad.card)
    (by unfold firstSize;omega) (by unfold thirdSize;omega) (some State.initial)
    (fun xs=>∃ i,C.stop hD (Δ:ℝ) (xs i))]
  have hκ : ((1/1000000:ℚ):ℝ)=mainKappa := by norm_num [mainKappa]
  simp only [hκ,hPeq]
  have hΔ' : (1:ℝ)≤(Δ:ℝ) := by exact_mod_cast hΔ
  have hh:=C.integral_records_success hD F hOF hSF (Δ:ℝ) hΔ' hsep hP hm
  simp only [Guided.hits_iff_exists_state] at hh
  simp only [blindUpdate,integralActions,mainActual,Option.map_some,State.real,State.initial,
    Sampling.State.initial,List.map_nil] at hh ⊢
  convert hh using 1
  congr 1
  funext seed
  congr 1
  funext i
  congr 3
  apply Subsingleton.elim
end MetricKMedianRecovery.RationalSampling

end OAI
