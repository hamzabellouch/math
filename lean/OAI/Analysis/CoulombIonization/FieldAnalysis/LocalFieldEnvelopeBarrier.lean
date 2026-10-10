import Mathlib
import OAI.Analysis.CoulombIonization.RadialBounds.BallAverageKernelBarrier

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory Set Metric

namespace CoulombAtom

def localHistoryFieldValues (E₀ : CoreObservationEnsemble) (y₀ : Space) (a : ℝ)
    (ha : 0 < a) (Z lam : ℝ) : Set ℝ :=
  {t | ∃ n E, CoreLocalHistory E₀ y₀ a ha n E ∧ ∃ y ∈ closedBall y₀ (localHistoryReach a n),
    t = Real.sqrt (E.fieldMoment Z lam y)/((n:ℝ)+2)^8}

def localFieldEnvelope (E₀ : CoreObservationEnsemble) (y₀ : Space) (a : ℝ)
    (ha : 0 < a) (Z lam : ℝ) : ℝ := sSup (localHistoryFieldValues E₀ y₀ a ha Z lam)

lemma localHistoryFieldValues_nonempty (E₀ : CoreObservationEnsemble) (y₀ : Space) {a : ℝ}
    (ha : 0 < a) (Z lam : ℝ) : (localHistoryFieldValues E₀ y₀ a ha Z lam).Nonempty := by
  refine ⟨_,0,E₀,CoreLocalHistory.initial,y₀,?_,rfl⟩
  simp [localHistoryReach]

lemma localHistoryFieldValues_bdd (E₀ : CoreObservationEnsemble) (y₀ : Space) {a Z lam : ℝ}
    (ha : 0 < a) (hsep : 12*a ≤ ‖y₀‖) (hm : E₀.mass = 1) (hZ : 0 ≤ Z) (hlam : 0 ≤ lam) :
    BddAbove (localHistoryFieldValues E₀ y₀ a ha Z lam) := by
  refine ⟨Z/(8*a),?_⟩
  rintro t ⟨n,E,hE,y,hy,rfl⟩
  have hs := CoreLocalHistory.center_nuclear_separation (ha := ha) hsep y hy
  have hField := E.fieldMoment_le_nuclear hZ hlam y
  rw [hE.mass,hm,mul_one] at hField
  have hdiv : Z/‖y‖ ≤ Z/(8*a) := div_le_div_of_nonneg_left hZ (by positivity) hs
  have hsq := pow_le_pow_left₀ (div_nonneg hZ (norm_nonneg _)) hdiv 2
  have hroot : Real.sqrt (E.fieldMoment Z lam y) ≤ Z/(8*a) :=
    (Real.sqrt_le_iff).2 ⟨by positivity,hField.trans hsq⟩
  apply (div_le_iff₀ (by positivity : 0 < ((n:ℝ)+2)^8)).2
  have hw : 1 ≤ ((n:ℝ)+2)^8 := one_le_pow₀ (by have := Nat.cast_nonneg (α := ℝ) n; linarith)
  exact hroot.trans (le_mul_of_one_le_right (by positivity) hw)

lemma localFieldEnvelope_nonneg (E₀ : CoreObservationEnsemble) (y₀ : Space) {a Z lam : ℝ}
    (ha : 0 < a) (hsep : 12*a ≤ ‖y₀‖) (hm : E₀.mass = 1) (hZ : 0 ≤ Z) (hlam : 0 ≤ lam) :
    0 ≤ localFieldEnvelope E₀ y₀ a ha Z lam := by
  obtain ⟨t,ht⟩ := localHistoryFieldValues_nonempty E₀ y₀ ha Z lam
  have ht0 : 0 ≤ t := by
    obtain ⟨n,E,_,y,_,rfl⟩ := ht
    positivity
  exact ht0.trans (le_csSup (localHistoryFieldValues_bdd E₀ y₀ ha hsep hm hZ hlam) ht)

lemma localFieldEnvelope_bound {E₀ E : CoreObservationEnsemble} {y₀ : Space} {a Z lam : ℝ}
    {ha : 0 < a} (hsep : 12*a ≤ ‖y₀‖) (hm : E₀.mass = 1) (hZ : 0 ≤ Z) (hlam : 0 ≤ lam)
    {n : ℕ} (hE : CoreLocalHistory E₀ y₀ a ha n E) (y : Space)
    (hy : y ∈ closedBall y₀ (localHistoryReach a n)) :
    Real.sqrt (E.fieldMoment Z lam y) ≤ localFieldEnvelope E₀ y₀ a ha Z lam*((n:ℝ)+2)^8 := by
  have hh : Real.sqrt (E.fieldMoment Z lam y)/((n:ℝ)+2)^8 ≤ localFieldEnvelope E₀ y₀ a ha Z lam :=
    le_csSup (localHistoryFieldValues_bdd E₀ y₀ ha hsep hm hZ hlam) ⟨n,E,hE,y,hy,rfl⟩
  exact (div_le_iff₀ (by positivity)).1 hh

lemma localFieldEnvelope_outMoment {E₀ E : CoreObservationEnsemble} {y₀ : Space} {a Z lam : ℝ}
    {ha : 0 < a} (hsep : 12*a ≤ ‖y₀‖) (hm : E₀.mass = 1) (hZ : 0 ≤ Z) (hlam : 0 ≤ lam)
    {n : ℕ} (hE : CoreLocalHistory E₀ y₀ a ha n E) (y : Space)
    (hy : y ∈ closedBall y₀ (localHistoryReach a n)) :
    Real.sqrt (E.outMoment y (mul_nonneg (by norm_num : (0:ℝ) ≤ 2) (localHistoryRadius_pos ha n).le)
      (localHistoryRadius_pos ha n) Z lam) ≤ 8*localFieldEnvelope E₀ y₀ a ha Z lam*((n:ℝ)+3)^8 := by
  let u := localHistoryRadius a n
  have hu : 0 < u := localHistoryRadius_pos ha n
  have hn := CoreLocalHistory.center_nuclear_separation (ha := ha) hsep y hy
  have hn' : 5*u ≤ ‖y‖ := by have := localHistoryRadius_le ha n; dsimp [u]; linarith
  let H := localFieldEnvelope E₀ y₀ a ha Z lam
  have hH : 0 ≤ H := localFieldEnvelope_nonneg E₀ y₀ ha hsep hm hZ hlam
  apply Real.sqrt_le_iff.2
  refine ⟨by positivity,?_⟩
  have hh := E.outMoment_le_ball_field y hu hn' hZ hlam (Q := (H*((n:ℝ)+3)^8)^2) ?_
  · calc E.outMoment y _ _ Z lam ≤ 64*(H*((n:ℝ)+3)^8)^2 := hh
         _ = (8*H*((n:ℝ)+3)^8)^2 := by ring
  · intro z hz
    have he := CoreLocalHistory.observe hE y hy
    have hz' := CoreLocalHistory.next_center y z hy hz
    have hh := localFieldEnvelope_bound hsep hm hZ hlam he z hz'
    have hcast : ((n+1:ℕ):ℝ)+2 = (n:ℝ)+3 := by push_cast; ring
    rw [hcast] at hh
    have hsq := pow_le_pow_left₀ (Real.sqrt_nonneg _) hh 2
    rwa [Real.sq_sqrt (CoreObservationEnsemble.fieldMoment_nonneg ..)] at hsq

end CoulombAtom

end

end OAI
