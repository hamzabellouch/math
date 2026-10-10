import OAI.Analysis.LipschitzHilbert.Estimates.AdmissibleListCount
import OAI.Analysis.LipschitzHilbert.Estimates.ReferenceFamilyException

namespace OAI

/-! One exceptional set for all separated significant-direction lists. -/

noncomputable section

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace LipschitzHilbert

/-- Quantitative simultaneous counting from the original measurable
popularity witnesses. The exceptional set is chosen before the point,
separation scale, and list, and costs only total top area. -/
theorem simultaneous_separated_count {ι : Type*} [Fintype ι] [DecidableEq ι]
    (T : ι → SlopeBox) (u : ℝ × ℝ → ℝ) {L : ℝ≥0} (hu : LipschitzWith L u)
    {M : ℕ} (hM : 0 < M) {A q P K θ c c0 B m lambda : ℝ}
    (hA : 0 < A) (hq : 0 < q) (hP : 0 < P) (hK : 0 ≤ K)
    (hAK : A + K ≤ P) (hc0 : 0 ≤ c0) (hc : 4 * (c0 + 1) + 1 ≤ c)
    (hcM : c ≤ M) (hB : 1 < B) (hMB : (M : ℝ) = B ^ 2) (hm : B ^ 2 ≤ m)
    (hθ0 : 0 < θ) (hθ : θ ≤ q / (8 * A * P)) (hlambda : 0 ≤ lambda)
    (d : ι → ℝ) (E : ι → Set (ℝ × ℝ))
    (hE : ∀ i, MeasurableSet (E i))
    (hfinite : ∀ i, (volume.prod volume) (E i) ≠ ∞)
    (hbox : ∀ i, ∀ w ∈ E i, (T i).radius w ≤ A)
    (harea : ∀ i, q * (T i).length * (T i).width ≤ (volume.prod volume).real (E i))
    (hwitness : ∀ i, ∀ w ∈ E i, |u w - (T i).slope| ≤ c0 * d i)
    (hd : ∀ i, 0 ≤ d i) (hwidth : ∀ i, (T i).width = m * (T i).length * d i)
    (hsmall : ∀ i, L * P * m * (T i).length ≤ 1 / 2) :
    ∃ bad : Set (ℝ × ℝ), MeasurableSet bad ∧ (volume.prod volume) bad ≠ ∞ ∧
      (volume.prod volume).real bad ≤
        (∑ i, (T i).length * (T i).width) *
          (384 * K * (K + P) * Real.exp (-θ * lambda / (240 * (1 + c)))) ∧
      ∀ z ∉ bad, ∀ rho : ℝ, 0 < rho → ∀ I : Finset ι,
        (∀ i ∈ I, (T i).radius z ≤ K) →
        (∀ i ∈ I, d i ≤ rho / B ^ 2) →
        (∀ i ∈ I, ∀ j ∈ I, |(T i).slope - (T j).slope| ≤ B * rho) →
        (∀ i ∈ I, ∀ j ∈ I, i ≠ j → rho ≤ |(T i).slope - (T j).slope|) →
        (I.card : ℝ) ≤ 1 + lambda := by
  have hc0' : 0 ≤ c := by linarith
  obtain ⟨N, _, hN, htail⟩ := reference_family_count_setup T u hu.continuous.measurable
    hM hc0' hcM hK hP hθ0
  obtain ⟨hmeas, hmeasure⟩ := htail lambda hlambda
  refine ⟨referenceFamilyException T N K lambda, hmeas,
    referenceFamilyException_measure_ne_top T N K lambda, hmeasure, ?_⟩
  intro z hz rho hrho I hsignificant hprecision hspan hsep
  apply SlopeBox.admissible_list_card_le T I u hu z hM hA hq hP hK hAK hc0 hc
    hB hrho hMB hm hθ hlambda d E
    (fun i _ => hE i) (fun i _ => hfinite i) (fun i _ => hbox i)
    (fun i _ => harea i) (fun i _ => hwitness i) (fun i _ => hd i)
    (fun i _ => hwidth i) hprecision (fun i _ => hsmall i) hspan hsep hsignificant
    N (fun i _ => hN i)
  exact fun i hi => count_le_outside_referenceFamilyException T N hz i (hsignificant i hi)

end LipschitzHilbert

end

end OAI
