import OAI.NumberTheory.Jacobsthal.Estimates.RawInitialPacking

namespace OAI

namespace Erdos970

section

namespace Erdos970Dependency.MarkedVisits
open Filter Set MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory ENNReal Classical
open NumberTheoryLean.FinitePathMeasures NumberTheoryLean.PairedCostProcess
open NumberTheoryLean.PairedCostGrouping NumberTheoryLean.TransitionKernels

abbrev RawEvenMarkedHitTrace (a : ℕ) :=
  Σ k : ℕ, RawHistory ((a+1)+2*k) × RawMarkedHitTrace ((a+1)+2*k)

noncomputable def rawEvenHitContinuation (a : ℕ) (v H : ℝ) : Kernel (RawInitialPackedTrace a) (RawEvenMarkedHitTrace a) :=
  sigmaFamilyKernel (fun k : ℕ =>
    (Kernel.id : Kernel (RawHistory ((a+1)+2*k)) (RawHistory ((a+1)+2*k))) ×ₖ
      rawRegMarkedFirstHitKernel ((a+1)+2*k) v H)

instance rawEvenHitContinuation_isFiniteKernel (a : ℕ) (v H : ℝ) : IsFiniteKernel (rawEvenHitContinuation a v H) := by
  apply sigmaFamilyKernel_isFinite_of_bound _ (B := 1) (by simp)
  intro k y
  rw [Kernel.id_prod_apply' _ _ MeasurableSet.univ,preimage_univ]
  exact rawRegMarkedFirstHit_mass_le_one _ v H y

noncomputable def rawEvenMarkedHitKernel (a : ℕ) (v H : ℝ) : Kernel (RawHistory a) (RawEvenMarkedHitTrace a) :=
  rawEvenHitContinuation a v H ∘ₖ packedInitialKernel a

instance rawEvenMarkedHitKernel_isFiniteKernel (a : ℕ) (v H : ℝ) : IsFiniteKernel (rawEvenMarkedHitKernel a v H) := by
  unfold rawEvenMarkedHitKernel
  infer_instance

theorem rawEvenMarkedHit_mass (a : ℕ) (v H : ℝ) (h : RawHistory a) (s : EvenState)
    (hs : rawLast a h=(Sum.inl s,0)) :
    rawEvenMarkedHitKernel a v H h univ=ordinaryInitialHitMass s v H := by
  let G : CostState → ℝ≥0∞ := fun c => ordinaryMarkedHit v H (decodeReturnedOdd c) univ
  have hG : Measurable G := ((ordinaryMarkedHit v H).measurable_coe MeasurableSet.univ).comp decodeReturnedOdd_measurable
  have he : (fun r => rawEvenHitContinuation a v H r univ) =ᵐ[packedInitialKernel a h]
      fun r => G (packedInitialEndpoint a r) := by
    filter_upwards [packedInitial_ae_regeneration a h s hs] with r hr
    rcases r with ⟨k,y⟩
    rw [rawEvenHitContinuation,sigmaFamilyKernel_mass,Kernel.id_prod_apply' _ _ MeasurableSet.univ,preimage_univ,
      rawRegMarkedFirstHitKernel,stateFilter_input,
      ite_eq_left (show y ∈ lastRegeneration ((a+1)+2*k) from hr)]
    let z := decodeReturnedOdd (rawLast ((a+1)+2*k) y)
    have hz : rawLast ((a+1)+2*k) y=embedOdd z := (embed_decodeReturnedOdd_of_regeneration _ hr).symm
    rw [rawMarkedFirstHit_mass _ v H y z hz]
    rfl
  rw [rawEvenMarkedHitKernel,Kernel.comp_apply' _ _ _ MeasurableSet.univ,lintegral_congr_ae he,
    ← lintegral_map (g := packedInitialEndpoint a) hG (packedInitialEndpoint_measurable a),
    packedInitial_endpoint_law a h s hs,lintegral_map hG embedOdd_measurable]
  rfl

lemma rawEvenMarkedHit_mass_le_one (a : ℕ) (v H : ℝ) (h : RawHistory a) (s : EvenState)
    (hs : rawLast a h=(Sum.inl s,0)) : rawEvenMarkedHitKernel a v H h univ ≤ 1 := by
  rw [rawEvenMarkedHit_mass a v H h s hs]
  exact ordinaryInitialHitMass_le_one s v H

theorem rawEvenMarkedHit_exponential (S : ℝ) : ∃ eta C eta0 B : ℝ,
    0 < eta ∧ 0 < C ∧ 0 < eta0 ∧ 0 ≤ B ∧ ∀ (a : ℕ) (h : RawHistory a) (s : EvenState),
      rawLast a h=(Sum.inl s,0) → s.1 ≤ S → ∀ v H : ℝ, 0 ≤ H →
        1-rawEvenMarkedHitKernel a v H h univ ≤
          ENNReal.ofReal (C*Real.exp (-eta*H)+B*Real.exp (-eta0*v)) := by
  obtain ⟨eta,C,eta0,B,heta,hC,heta0,hB,hBound⟩ := ordinaryInitialHit_exponential S
  refine ⟨eta,C,eta0,B,heta,hC,heta0,hB,?_⟩
  intro a h s hs hS v H hH
  rw [rawEvenMarkedHit_mass a v H h s hs]
  exact hBound s hS v H hH

theorem moving_raw_even_marked_hit {eps : ℝ} (heps : 0 < eps) :
    ∃ rho : ℝ, 10 < rho ∧ ∀ K : ℝ, 0 < K →
      ∀ᶠ w : ℝ in atTop, 3 ≤ w ∧ ∀ r : ℝ, w ≤ r → ∀ (a : ℕ) (h : RawHistory a) (s : EvenState),
        rawLast a h=(Sum.inl s,0) → 199/100 ≤ s.1 → s.1 ≤ 23/10 →
        1-rawEvenMarkedHitKernel a (Real.log (r/(rho*K*(Real.log w)^2))) (Real.log (rho/10)) h univ ≤
          ENNReal.ofReal eps := by
  obtain ⟨rho,hrho,hMoving⟩ := moving_ordinary_marked_hit heps
  refine ⟨rho,hrho,?_⟩
  intro K hK
  filter_upwards [hMoving K hK] with w hw
  refine ⟨hw.1,?_⟩
  intro r hr a h s hs hs0 hs1
  rw [rawEvenMarkedHit_mass a _ _ h s hs]
  exact hw.2 r hr s hs0 hs1

end Erdos970Dependency.MarkedVisits

end

end Erdos970

end OAI
