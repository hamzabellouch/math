import OAI.NumberTheory.DukePrimeDegree.Entropy.NameErrorEntropy
import OAI.NumberTheory.PrimePackets.DisintegrationEntropy

namespace OAI

/-! # Integrating finite-name covers over conditional probability kernels

Reference names may depend on the conditioning parameter. Errors need
only lie in the bad sets almost surely for the corresponding conditional
measure. Their integrated cost is measured by the actual kernel mixture.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators

namespace DukePrimeDegree
open PrimeDegreePackets

theorem nameEntropy_le_reference_bad_sets
    {Y α : Type*} [MeasurableSpace Y]
    [MeasurableSpace α] [MeasurableSingletonClass α]
    [Fintype α] [Nonempty α] [DecidableEq α]
    (ν : Measure Y) [IsProbabilityMeasure ν] (N M : ℕ)
    (P : Y → Fin N → α) (hP : Measurable P)
    (r : Y → Fin M) (hr : Measurable r) (v : Fin M → Fin N → α)
    (B : Fin N → Set Y)
    (hbad : ∀ i, ∀ᵐ y ∂ν, P y i ≠ v (r y) i → y ∈ B i)
    {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ < 1) :
    observationEntropy ν P ≤ Real.log M+(N : ℝ)*(-Real.log (1-δ))+
      (∑ i : Fin N, ν.real (B i))*(Real.log (Fintype.card α)-Real.log δ) := by
  let R := v ∘ r
  have hR : Measurable R := (measurable_of_finite v).comp hr
  have href : observationEntropy ν R ≤ observationEntropy ν r :=
    observationEntropy_le_of_refines ν R r
      (fun a => hR (measurableSet_singleton a))
      (fun a => hr (measurableSet_singleton a))
      (fun x y h => congrArg v h)
  have hcard : observationEntropy ν r ≤ Real.log M := by
    simpa only [observationEntropy,Fintype.card_fin] using
      (finiteShannon_le_log_card (fun _ => measureReal_nonneg)
        (observation_distribution_sum ν r (fun a => hr (measurableSet_singleton a))))
  have hjoint := observationEntropy_le_add_conditional ν P R
    (fun a => hP (measurableSet_singleton a))
    (fun a => hR (measurableSet_singleton a))
  have hc := conditionalNameEntropy_le_errors ν N P R hP hR hδ hδ1
  have hsum : (∑ i : Fin N, ν.real {y | P y i ≠ R y i}) ≤
      ∑ i : Fin N, ν.real (B i) := by
    apply Finset.sum_le_sum
    intro i _
    exact ENNReal.toReal_mono (measure_ne_top ν (B i)) (measure_mono_ae (hbad i))
  have hslope : 0 ≤ Real.log (Fintype.card α)-Real.log δ := by
    have hn : 1 ≤ (Fintype.card α : ℝ) := by exact_mod_cast Fintype.card_pos
    linarith [Real.log_nonneg hn,Real.log_neg hδ hδ1]
  have hm := mul_le_mul_of_nonneg_right hsum hslope
  linarith

/-- The conditional error estimate integrates against the actual law of
the conditioning parameter. No joint measurability of the chosen reference
labels is needed; only the conditional entropy and bad-set probabilities
are integrated. -/
theorem integral_nameEntropy_le_reference_bad_sets
    {S Y α : Type*} [MeasurableSpace S] [MeasurableSpace Y]
    [MeasurableSpace α] [MeasurableSingletonClass α]
    [Fintype α] [Nonempty α] [DecidableEq α]
    (τ : Measure S) [IsProbabilityMeasure τ]
    (κ : Kernel S Y) [IsMarkovKernel κ] (N M : ℕ)
    (P : Y → Fin N → α) (hP : Measurable P)
    (r : S → Y → Fin M) (hr : ∀ s, Measurable (r s))
    (v : S → Fin M → Fin N → α) (B : Fin N → Set Y)
    (hB : ∀ i, MeasurableSet (B i))
    (hbad : ∀ᵐ s ∂τ, ∀ i, ∀ᵐ y ∂κ s, P y i ≠ v s (r s y) i → y ∈ B i)
    {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ < 1) :
    (∫ s, observationEntropy (κ s) P ∂τ) ≤
      Real.log M+(N : ℝ)*(-Real.log (1-δ))+
        (∑ i : Fin N, (κ ∘ₘ τ).real (B i)) *
          (Real.log (Fintype.card α)-Real.log δ) := by
  let C := Real.log M+(N : ℝ)*(-Real.log (1-δ))
  let L := Real.log (Fintype.card α)-Real.log δ
  have hp : Integrable (fun s => observationEntropy (κ s) P) τ :=
    integrable_kernel_entropy τ κ P (fun a => hP (measurableSet_singleton a))
  have hb (i : Fin N) : Integrable (fun s => (κ s).real (B i)) τ :=
    integrable_kernel_real τ κ (hB i)
  have hs : Integrable (fun s => ∑ i : Fin N, (κ s).real (B i)) τ :=
    integrable_finsetSum _ (fun i _ => hb i)
  have hbound : Integrable (fun s => C+(∑ i : Fin N, (κ s).real (B i))*L) τ :=
    (integrable_const C).add (hs.mul_const L)
  have H := integral_mono_ae hp hbound (hbad.mono fun s hs =>
    nameEntropy_le_reference_bad_sets (κ s) N M P hP (r s) (hr s) (v s) B hs hδ hδ1)
  have he : (∫ s, C+(∑ i : Fin N, (κ s).real (B i))*L ∂τ) =
      C+(∑ i : Fin N, (κ ∘ₘ τ).real (B i))*L := by
    rw [integral_add (integrable_const C) (hs.mul_const L),integral_mul_const,
      integral_finsetSum _ (fun i _ => hb i)]
    simp only [integral_const,probReal_univ,smul_eq_mul,one_mul]
    congr 2
    apply Finset.sum_congr rfl
    intro i _
    exact (kernel_comp_real τ κ (hB i)).symm
  exact H.trans_eq he

/-- In actual disintegration coordinates, the integrated bad-set cost is
exactly the corresponding marginal mass of the original probability law. -/
theorem conditionalSigmaEntropy_fst_le_reference_bad_sets
    {S Y α : Type*} [MeasurableSpace S] [MeasurableSpace Y]
    [StandardBorelSpace Y] [Nonempty Y]
    [MeasurableSpace α] [MeasurableSingletonClass α]
    [Fintype α] [Nonempty α] [DecidableEq α]
    (ρ : Measure (S × Y)) [IsProbabilityMeasure ρ] (N M : ℕ)
    (P : Y → Fin N → α) (hP : Measurable P)
    (r : S → Y → Fin M) (hr : ∀ s, Measurable (r s))
    (v : S → Fin M → Fin N → α) (B : Fin N → Set Y)
    (hB : ∀ i, MeasurableSet (B i))
    (hbad : ∀ᵐ s ∂ρ.fst, ∀ i, ∀ᵐ y ∂ρ.condKernel s,
      P y i ≠ v s (r s y) i → y ∈ B i)
    {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ < 1) :
    conditionalSigmaEntropy ρ (fun z => P z.2)
      (MeasurableSpace.comap Prod.fst (inferInstance : MeasurableSpace S)) ≤
      Real.log M+(N : ℝ)*(-Real.log (1-δ))+
        (∑ i : Fin N, ρ.snd.real (B i)) *
          (Real.log (Fintype.card α)-Real.log δ) := by
  have hPT : Measurable (fun z : S × Y => P z.2) := hP.comp measurable_snd
  rw [conditionalSigmaEntropy_fst ρ (fun z => P z.2)
    (fun a => hPT (measurableSet_singleton a))]
  have H := integral_nameEntropy_le_reference_bad_sets ρ.fst ρ.condKernel
    N M P hP r hr v B hB hbad hδ hδ1
  have hm : ρ.condKernel ∘ₘ ρ.fst = ρ.snd := by
    rw [←Measure.snd_compProd,Measure.disintegrate]
  simpa only [hm] using H

end DukePrimeDegree

end

end OAI
