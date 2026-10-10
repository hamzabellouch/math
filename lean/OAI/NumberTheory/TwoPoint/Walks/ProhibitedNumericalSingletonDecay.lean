import OAI.NumberTheory.TwoPoint.Walks.ProhibitedSingletonDecay
import OAI.NumberTheory.TwoPoint.Bounds.NumericalTupleLabels

namespace OAI

/-! Singleton decay on the same fixed-length numerical catalog as the other
trace classes.  The list encoding introduces no multiplicity. -/

namespace TwoPointCorrelations

open Finset Filter
open scoped Classical

theorem eventually_prohibited_numerical_singleton_decay (Cs Cw : ℝ)
    (hCs : 0 ≤ Cs) (hCw : 0 ≤ Cw) :
    ∀ᶠ L : ℝ in atTop, ∀ (h J M R B s n D K H Y : ℕ)
      (data : ProhibitedPrimeFamily h J M) (hB : ∀ p ∈ data.P ∪ data.Q, p ≤ B)
      (F : Finset (Fin R → SignedStep))
      (label : (Fin R → SignedStep) → Fin R × Fin J → ↥(data.P ∪ data.Q))
      (_base : ↥(data.P ∪ data.Q) → Fin B)
      (weight : (Fin R → SignedStep) → (↥(data.P ∪ data.Q) → Fin B) → ℝ)
      (cap : (Fin R → SignedStep) → ℝ) (A : ℝ),
      0 ≤ A → (∀ w ∈ F, 0 ≤ cap w) →
      (∀ w ∈ F, ∀ x, 0 ≤ weight w x) → (∀ w ∈ F, ∀ x, weight w x ≤ cap w) →
      (∀ w ∈ F, cap w * 2 ^ (R * J + (singletonLabels (label w)).card) ≤ A) →
      (∀ w ∈ F, ∀ x y, (∀ i, i ∉ univ.image (label w) → x i = y i) → weight w x = weight w y) →
      (∀ w ∈ F, ∀ x, weight w x ≠ 0 → MainPaddingTests Subtype.val h B (List.ofFn w) x) →
      (∀ w ∈ F, ∀ i, ((w i).tuple, (w i).padding) ∈ data.pairs) →
      (∀ w ∈ F, ∀ i, (w i).tuple.primeFactors = univ.image (fun j => (label w (i, j)).val)) →
      R + n * s ≤ D → (∀ w ∈ F, n * (s * J) < (singletonLabels (label w)).card) →
      (D : ℝ) ≤ 4 * L → ((J + M : ℕ) : ℝ) ≤ Cs * Real.log L →
      0 < n → (n : ℝ) ≤ 4 * L → 8 * K ≤ n →
      L ^ (1 / 12 : ℝ) / 32 ≤ (K : ℝ) → (K : ℝ) ≤ L →
      1 ≤ primeHarmonicMass data.P →
      primeHarmonicMass data.P ≤ L ^ (2 : ℕ) → primeHarmonicMass data.Q ≤ L ^ (2 : ℕ) →
      1 ≤ Y → (Y : ℝ) ≤ Real.exp L →
      (∀ p ∈ data.P, H ≤ p) → (∀ p ∈ data.P, p ≤ Y) →
      Real.exp (L ^ (199 / 200 : ℝ)) ≤ H → A ≤ Real.exp (Cw * L * (Real.log L) ^ 2) →
      (∑ w ∈ F, |prohibitedCenteredAverage data hB s D (List.ofFn w) (label w) (weight w)|) ≤
        Real.exp (-L ^ (21 / 20 : ℝ)) := by
  filter_upwards [eventually_prohibited_singleton_decay Cs Cw hCs hCw] with L hdecay
  intro h J M R B s n D K H Y data hB F label base weight cap A hA hcap hweight hwcap hcost
    hdep hpadding hpairs hlabel hD hn hDL hJM hnpos hnL hKn hKlo hKhi hmass hPmass hQmass
    hYpos hYexp hlo hhi hH hAexp
  have : Nonempty (Fin R → SignedStep) := ⟨fun _ => ⟨true, 1, 1⟩⟩
  let decode : List SignedStep → Fin R → SignedStep := Function.invFun List.ofFn
  have hdecode (w : Fin R → SignedStep) : decode (List.ofFn w) = w :=
    Function.leftInverse_invFun List.ofFn_injective w
  let E := F.image List.ofFn
  have hpull (w : List SignedStep) (hw : w ∈ E) : ∃ v ∈ F, w = List.ofFn v := by
    obtain ⟨v, hv, rfl⟩ := mem_image.mp hw
    exact ⟨v, hv, rfl⟩
  have hb := hdecay h J M R B s n D K H Y data hB E (fun w => label (decode w)) base
    (fun w => weight (decode w)) (fun w => cap (decode w)) A hA
    (by intro w hw; obtain ⟨v,hv,rfl⟩ := hpull w hw; simpa only [hdecode] using hcap v hv)
    (by intro w hw; obtain ⟨v,hv,rfl⟩ := hpull w hw; simpa only [hdecode] using hweight v hv)
    (by intro w hw; obtain ⟨v,hv,rfl⟩ := hpull w hw; simpa only [hdecode] using hwcap v hv)
    (by intro w hw; obtain ⟨v,hv,rfl⟩ := hpull w hw; simpa only [hdecode] using hcost v hv)
    (by intro w hw; obtain ⟨v,hv,rfl⟩ := hpull w hw; simpa only [hdecode] using hdep v hv)
    (by intro w hw; obtain ⟨v,hv,rfl⟩ := hpull w hw; simpa only [hdecode] using hpadding v hv)
    (by intro w hw; obtain ⟨v,hv,rfl⟩ := hpull w hw; simpa only [hdecode] using
      numerical_label_seen data v (label v) (hpairs v hv) (hlabel v hv))
    (by intro w hw; obtain ⟨v,hv,rfl⟩ := hpull w hw; simpa only [hdecode] using
      numerical_label_pool data v (label v) (hpairs v hv) (hlabel v hv))
    (by intro w hw; obtain ⟨v,hv,rfl⟩ := hpull w hw; exact numerical_word_pairs data v (hpairs v hv))
    (by intro w hw; obtain ⟨v,hv,rfl⟩ := hpull w hw; simpa only [hdecode] using
      numerical_label_cover data v (label v) (hlabel v hv))
    (by
      intro w hw
      obtain ⟨v,hv,rfl⟩ := hpull w hw
      rw [hdecode]
      exact numerical_singleton_position data v (label v) (hpairs v hv) (hlabel v hv))
    (by intro w hw; obtain ⟨v,_,rfl⟩ := hpull w hw; simpa only [List.length_ofFn] using hD)
    (by intro w hw; obtain ⟨v,hv,rfl⟩ := hpull w hw; simpa only [hdecode] using hn v hv)
    hDL hJM hnpos hnL hKn hKlo hKhi hmass hPmass hQmass hYpos hYexp hlo hhi hH hAexp
  simpa only [E, sum_image (fun _ _ _ _ he => List.ofFn_injective he), hdecode] using hb

end TwoPointCorrelations

end OAI
