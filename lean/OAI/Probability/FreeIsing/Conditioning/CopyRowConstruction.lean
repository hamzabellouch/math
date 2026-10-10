import OAI.Probability.FreeIsing.Brownian.RowComparisonConstruction
import OAI.Probability.FreeIsing.Conditioning.CopyIntegralTransport

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal Topology BigOperators

namespace Problem367.ConditionalIntegralTransport

variable {W Ω ι : Type*} [MeasurableSpace W] [MeasurableSpace Ω]

theorem integral_sq_pair
    (ρ : Measure W) [SFinite ρ] (κ : Kernel W Ω) [IsMarkovKernel κ]
    (j : Bool) {H : W × Ω → ℝ} (hH : AEStronglyMeasurable H (ρ ⊗ₘ κ)) :
    (∫ q, H (pair j q) ^ 2 ∂ρ ⊗ₘ (κ ×ₖ κ)) = ∫ q, H q ^ 2 ∂ρ ⊗ₘ κ := by
  simpa using BrownianGrid.integral_sq_sub_comp (pair_measurePreserving ρ κ j)
    hH (aestronglyMeasurable_const : AEStronglyMeasurable
      (fun _ : W × Ω => (0 : ℝ)) (ρ ⊗ₘ κ))

theorem summable_pair_timeEnergy
    (ρ : Measure W) [SFinite ρ] (κ : Kernel W Ω) [IsMarkovKernel κ]
    (H : ι → ℝ≥0 → W × Ω → ℝ)
    (hmH : ∀ a t, AEStronglyMeasurable (H a t) (ρ ⊗ₘ κ))
    (T : ℝ≥0)
    (he : Summable fun a => ∫ t in (0 : ℝ)..(T : ℝ),
      ∫ q, H a t.toNNReal q ^ 2 ∂ρ ⊗ₘ κ) (j : Bool) :
    Summable fun a => ∫ t in (0 : ℝ)..(T : ℝ),
      ∫ q, H a t.toNNReal (pair j q) ^ 2 ∂ρ ⊗ₘ (κ ×ₖ κ) := by
  simpa only [integral_sq_pair ρ κ j (hmH _ _)] using he

theorem exists_conditionalCopy_row_integrals
    (ρ : Measure W) [IsProbabilityMeasure ρ]
    (κ : Kernel W Ω) [IsMarkovKernel κ]
    (B : ι → ℝ≥0 → W → ℝ)
    (F : Filtration ℝ≥0 (inferInstance : MeasurableSpace (W × (Ω × Ω))))
    (hB : ∀ a, IsPreBrownianReal (fun (t : ℝ≥0) (q : W × (Ω × Ω)) => B a t q.1)
      (ρ ⊗ₘ (κ ×ₖ κ)))
    (hAd : ∀ a, StronglyAdapted F (fun (t : ℝ≥0) (q : W × (Ω × Ω)) => B a t q.1))
    (hind : ∀ s t, s ≤ t → Indep
      (MeasurableSpace.comap
        (fun q : W × (Ω × Ω) => fun a => B a t q.1 - B a s q.1) inferInstance)
      (F s) (ρ ⊗ₘ (κ ×ₖ κ)))
    (hcross : ∀ s t, s ≤ t → Pairwise fun a b =>
      IndepFun (fun q : W × (Ω × Ω) => B a t q.1 - B a s q.1)
        (fun q : W × (Ω × Ω) => B b t q.1 - B b s q.1) (ρ ⊗ₘ (κ ×ₖ κ)))
    (H : ι → ℝ≥0 → W × Ω → ℝ)
    (hmH : ∀ a t, AEStronglyMeasurable (H a t) (ρ ⊗ₘ κ))
    (hH : ∀ j a, StronglyAdapted F (fun t q => H a t (pair j q)))
    (hcH : ∀ a, ∀ᵐ q ∂ρ ⊗ₘ κ, Continuous (fun t => H a t q))
    (C : ι → ℝ) (hC : ∀ a, 0 ≤ C a)
    (hbH : ∀ a, ∀ᵐ q ∂ρ ⊗ₘ κ, ∀ t, |H a t q| ≤ C a)
    (T : ℝ≥0)
    (he : Summable fun a => ∫ t in (0 : ℝ)..(T : ℝ),
      ∫ q, H a t.toNNReal q ^ 2 ∂ρ ⊗ₘ κ) :
    ∃ (I : Bool → ι → W × (Ω × Ω) → ℝ) (Y : Bool → W × (Ω × Ω) → ℝ),
      (∀ j a, MemLp (I j a) 2 (ρ ⊗ₘ (κ ×ₖ κ))) ∧
      (∀ j a, Tendsto (fun n => ∫ q,
        (BrownianGrid.uniformSum (fun t p => B a t p.1)
          (fun t p => H a t (pair j p)) T n q - I j a q) ^ 2
        ∂ρ ⊗ₘ (κ ×ₖ κ)) atTop (𝓝 0)) ∧
      (∀ j, Measurable (Y j)) ∧
      (∀ j, AEStronglyMeasurable[F T] (Y j) (ρ ⊗ₘ (κ ×ₖ κ))) ∧
      (∀ j, MemLp (Y j) 2 (ρ ⊗ₘ (κ ×ₖ κ))) ∧
      (∀ j, (∫ q, Y j q ∂ρ ⊗ₘ (κ ×ₖ κ)) = 0) ∧
      (∀ j, (∫ q, Y j q ^ 2 ∂ρ ⊗ₘ (κ ×ₖ κ)) =
        ∑' a, ∫ t in (0 : ℝ)..(T : ℝ), ∫ q, H a t.toNNReal q ^ 2 ∂ρ ⊗ₘ κ) ∧
      (∀ j, Tendsto (fun s : Finset ι => ∫ q,
        ((∑ a ∈ s, I j a q) - Y j q) ^ 2 ∂ρ ⊗ₘ (κ ×ₖ κ)) atTop (𝓝 0)) ∧
      Summable (fun a => ∫ t in (0 : ℝ)..(T : ℝ),
        ∫ q, (H a t.toNNReal (pair true q) - H a t.toNNReal (pair false q)) ^ 2
          ∂ρ ⊗ₘ (κ ×ₖ κ)) ∧
      (∫ q, (Y true q - Y false q) ^ 2 ∂ρ ⊗ₘ (κ ×ₖ κ)) =
        (∑' a, ∫ t in (0 : ℝ)..(T : ℝ),
          ∫ q, (H a t.toNNReal (pair true q) - H a t.toNNReal (pair false q)) ^ 2
            ∂ρ ⊗ₘ (κ ×ₖ κ)) ∧
      (∫ q, (Y true q - Y false q) ^ 2 ∂ρ ⊗ₘ (κ ×ₖ κ)) ≤
        4 * (∑' a, ∫ t in (0 : ℝ)..(T : ℝ), ∫ q, H a t.toNNReal q ^ 2 ∂ρ ⊗ₘ κ) := by
  have hc (j : Bool) (a : ι) : ∀ᵐ q ∂ρ ⊗ₘ (κ ×ₖ κ),
      Continuous (fun t => H a t (pair j q)) :=
    (pair_measurePreserving ρ κ j).quasiMeasurePreserving.ae (hcH a)
  have hb (j : Bool) (a : ι) : ∀ᵐ q ∂ρ ⊗ₘ (κ ×ₖ κ),
      ∀ t, |H a t (pair j q)| ≤ C a :=
    (pair_measurePreserving ρ κ j).quasiMeasurePreserving.ae (hbH a)
  have he' (j : Bool) := summable_pair_timeEnergy ρ κ H hmH T he j
  obtain ⟨I, J, Y, Z, hI, hJ, haI, haJ, hmY, hmZ, htY, htZ,
      hY, hZ, hzY, hzZ, heY, heZ, hsY, hsZ, heD, hdiff, hbound⟩ :=
    BrownianArrayFiltration.exists_paired_infinite_integrals hB hAd hind
      (fun a t q => H a t (pair true q)) (fun a t q => H a t (pair false q))
      (hH true) (hH false) (hc true) (hc false) C C hC hC (hb true) (hb false)
      T (he' true) (he' false) hcross
  have heY' : (∫ q, Y q ^ 2 ∂ρ ⊗ₘ (κ ×ₖ κ)) =
      ∑' a, ∫ t in (0 : ℝ)..(T : ℝ), ∫ q, H a t.toNNReal q ^ 2 ∂ρ ⊗ₘ κ := by
    simpa only [integral_sq_pair ρ κ true (hmH _ _)] using heY
  have heZ' : (∫ q, Z q ^ 2 ∂ρ ⊗ₘ (κ ×ₖ κ)) =
      ∑' a, ∫ t in (0 : ℝ)..(T : ℝ), ∫ q, H a t.toNNReal q ^ 2 ∂ρ ⊗ₘ κ := by
    simpa only [integral_sq_pair ρ κ false (hmH _ _)] using heZ
  refine ⟨(fun j => if j then I else J), (fun j => if j then Y else Z),
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, heD, hdiff, ?_⟩
  · intro j; cases j <;> assumption
  · intro j; cases j <;> assumption
  · intro j; cases j <;> assumption
  · intro j; cases j <;> assumption
  · intro j; cases j <;> assumption
  · intro j; cases j <;> assumption
  · intro j; cases j <;> assumption
  · intro j; cases j <;> assumption
  · change (∫ q, (Y q - Z q) ^ 2 ∂ρ ⊗ₘ (κ ×ₖ κ)) ≤ _
    simp only [integral_sq_pair ρ κ true (hmH _ _),
      integral_sq_pair ρ κ false (hmH _ _)] at hbound
    linarith

end Problem367.ConditionalIntegralTransport

end

end OAI
