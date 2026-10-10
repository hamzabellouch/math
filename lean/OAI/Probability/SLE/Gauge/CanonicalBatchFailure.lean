import OAI.Probability.SLE.Gauge.CanonicalBatchSuccess
import OAI.Probability.SLE.Gauge.BatchProbability

namespace OAI

/-! The exact prescribed batch has a nonempty chronological enumeration
and enough total centered success probability. The finite failure estimate
requires only the corresponding adapted half-probability inequalities. -/
noncomputable section
open Set Filter _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal

namespace SLEExactGauge.Multipoint.CanonicalMass

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {κ : ℝ} {B : ℝ≥0 → Ω → ℝ} {hBm : Measurable (Function.uncurry B)}
  {γ : Ω → ℝ≥0 → ℂ} {G : Ω → ℝ≥0 → ℂ → ℂ}
  (C : CanonicalMass P κ B hBm γ G)
  (hB : IsBrownianReal B P) (hc : ∀ ω, Continuous (fun t => B t ω))
  (h0 : ∀ ω, B 0 ω=0) (hκ : 0<κ) (hκ8 : κ<8) (F : Ω → ℝ≥0 → ℂ → ℂ)
  (hw : ∀ ω, IsCapacityTwoWitness (fun t => Real.sqrt κ*B t ω) (γ ω) (G ω) (F ω))
  (hpublished : PublishedTraceGeneration (P.map (sourceDriverPath B hc)) κ (fun t p => p t))
  (hgrowth : PublishedDiskUnivalentGrowth) (W : Target.WienerLaw) (hW : Target.IsWiener W)

include C hB hc h0 hκ hκ8 F hw hpublished hgrowth W hW in
theorem ordered_batch_success_budget {n : ℕ} (hn : 3≤n) :
    ∃ (J : ℕ) (e : Fin J → ℤ × ℕ), 0<J ∧ Function.Injective e ∧
      (∀ kj, kj ∈ Set.range e ↔ kj.2 < Target.multiplicity κ W n kj.1) ∧
      StrictMono (fun i => Target.entryPosition κ W (n,some (e i))) ∧
      (2:ℝ)^n/8 ≤ ∑ i,
        (centeredDiskLaw P κ B hc (4*(Target.batchLevel κ W n:ℝ)/κ)).real
          {p | MomentBatches.dyadic (e i).1 ≤
            C.diskAtRadius p.1 (4*(Target.batchLevel κ W n:ℝ)/κ) p.2} := by
  obtain ⟨J,e,hi,he,horder⟩ := Target.ordered_repeated_batch κ W (by omega)
    (C.moment_positive hB hc h0 hκ hκ8 F hw hpublished hgrowth W hW 1)
    (C.moment_jensen hB hc h0 hκ hκ8 F hw hgrowth W hW n)
  let q : ℤ → ℝ := fun k =>
    (centeredDiskLaw P κ B hc (4*(Target.batchLevel κ W n:ℝ)/κ)).real
      {p | MomentBatches.dyadic k ≤ C.diskAtRadius p.1 (4*(Target.batchLevel κ W n:ℝ)/κ) p.2}
  have hb : (2:ℝ)^n/8 ≤ ∑ i, q (e i).1 := by
    rw [Target.repeated_batch_sum_eq κ W n J e hi he q]
    exact C.centeredDiskLaw_batch_success hB hc h0 hκ hκ8 F hw hpublished hgrowth W hW hn
  have hJ : 0<J := by
    by_contra h
    have hz : J=0 := by omega
    subst J
    simp only [Finset.univ_eq_empty,Finset.sum_empty] at hb
    exact (div_pos (pow_pos (by norm_num : (0:ℝ)<2) n) (by norm_num)).not_ge hb
  exact ⟨J,e,hJ,hi,he,horder,hb⟩

include C hB hc h0 hκ hκ8 F hw hpublished hgrowth W hW in
theorem ordered_batch_failure_bound
    {Ξ : Type*} [mΞ : MeasurableSpace Ξ] (Q : Measure Ξ) [IsProbabilityMeasure Q]
    (ℱ : Filtration ℕ mΞ) {n J : ℕ} (hn : 3≤n)
    (e : Fin J → ℤ × ℕ) (hi : Function.Injective e)
    (he : ∀ kj, kj ∈ Set.range e ↔ kj.2 < Target.multiplicity κ W n kj.1)
    (success : Fin J → Set Ξ)
    (hmeas : ∀ i, MeasurableSet[ℱ (i.val+1)] (success i))
    (hstep : ∀ i (A : Set Ξ), MeasurableSet[ℱ i.val] A →
      ENNReal.ofReal
        ((centeredDiskLaw P κ B hc (4*(Target.batchLevel κ W n:ℝ)/κ)).real
          {p | MomentBatches.dyadic (e i).1 ≤
            C.diskAtRadius p.1 (4*(Target.batchLevel κ W n:ℝ)/κ) p.2}/2)*Q A ≤
        Q (A∩success i)) :
    Q (⋂ i, (success i)ᶜ) ≤ ENNReal.ofReal (Real.exp (-((2:ℝ)^n/16))) := by
  let ℓ := 4*(Target.batchLevel κ W n:ℝ)/κ
  have hℓ : 0≤ℓ := div_nonneg (by positivity) hκ.le
  let := centeredDiskLaw_isProbability hB hBm hc hκ hκ8 γ G F hw ℓ hℓ
  exact repeated_batch_failure_bound Q ℱ κ W n J e hi he
    (fun k => (centeredDiskLaw P κ B hc ℓ).real
      {p | MomentBatches.dyadic k ≤ C.diskAtRadius p.1 ℓ p.2})
    (fun _ => measureReal_nonneg) (fun _ => measureReal_le_one)
    (C.centeredDiskLaw_batch_success hB hc h0 hκ hκ8 F hw hpublished hgrowth W hW hn)
    success hmeas hstep

end SLEExactGauge.Multipoint.CanonicalMass

end

end OAI
