import OAI.NumberTheory.Jacobsthal.Probability.RawFirstPrefixLaw

namespace OAI

namespace Erdos970

section

namespace Erdos970Dependency.MarkedVisits
open Set MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory ENNReal

noncomputable def sigmaInputKernel {ι : Type*} {X : ι → Type*} {Z : Type*}
    [∀ i, MeasurableSpace (X i)] [MeasurableSpace Z] (K : ∀ i, Kernel (X i) Z) : Kernel (Σ i, X i) Z where
  toFun r := K r.1 r.2
  measurable' := measurable_sigma_family (fun i => (K i).measurable)

lemma sigmaInputKernel_isFinite_of_bound {ι : Type*} {X : ι → Type*} {Z : Type*}
    [∀ i, MeasurableSpace (X i)] [MeasurableSpace Z] (K : ∀ i, Kernel (X i) Z)
    {B : ℝ≥0∞} (hB : B < ∞) (hK : ∀ i x, K i x univ ≤ B) : IsFiniteKernel (sigmaInputKernel K) :=
  ⟨⟨B,hB,fun r => hK r.1 r.2⟩⟩

noncomputable def canonicalWordFirstPrefix : (a : ℕ) → List Bool → Bool → Kernel (RawHistory a) FiniteRawHistory
  | a, [], b => ((rawExtension a (a+1)).restrict (firstPrefixMarkEvent_measurable a b)).map
      (@Sigma.mk ℕ RawHistory (a+1))
  | a, c::w, b => sigmaInputKernel (fun n : ℕ => canonicalWordFirstPrefix (a+2*(n+1)) w b) ∘ₖ
      rawBranchReturnKernel a c

lemma canonicalWordFirstPrefix_bound (w : List Bool) : ∀ a b,
    IsFiniteKernel (canonicalWordFirstPrefix a w b) ∧ ∀ h, canonicalWordFirstPrefix a w b h univ ≤ 1 := by
  induction w with
  | nil =>
    intro a b
    constructor
    · unfold canonicalWordFirstPrefix
      infer_instance
    · intro h
      rw [canonicalWordFirstPrefix,Kernel.map_apply' _ (measurableSigmaMk (a+1)) _ MeasurableSet.univ,
        preimage_univ,Kernel.restrict_apply]
      exact (Measure.restrict_le_self univ).trans_eq measure_univ
  | cons c w ih =>
    intro a b
    let (n : ℕ) : IsFiniteKernel (canonicalWordFirstPrefix (a+2*(n+1)) w b) := (ih _ b).1
    have : IsFiniteKernel (sigmaInputKernel (fun n : ℕ => canonicalWordFirstPrefix (a+2*(n+1)) w b)) :=
      sigmaInputKernel_isFinite_of_bound _ (B := 1) (by simp) (fun n h => (ih (a+2*(n+1)) b).2 h)
    constructor
    · unfold canonicalWordFirstPrefix
      infer_instance
    · intro h
      rw [canonicalWordFirstPrefix,Kernel.comp_apply' _ _ _ MeasurableSet.univ]
      calc
        _ ≤ ∫⁻ _r, (1:ℝ≥0∞) ∂rawBranchReturnKernel a c h := lintegral_mono (fun r => (ih _ b).2 r.2)
        _ = rawBranchReturnKernel a c h univ := by simp
        _ ≤ 1 := rawBranchReturn_mass_le_one a c h

instance canonicalWordFirstPrefix_isFiniteKernel (a : ℕ) (w : List Bool) (b : Bool) :
    IsFiniteKernel (canonicalWordFirstPrefix a w b) := (canonicalWordFirstPrefix_bound w a b).1

instance canonicalWordContinuation_isFiniteKernel (a : ℕ) (w : List Bool) (b : Bool) :
    IsFiniteKernel (sigmaInputKernel (fun n : ℕ => canonicalWordFirstPrefix (a+2*(n+1)) w b)) :=
  sigmaInputKernel_isFinite_of_bound _ (B := 1) (by simp)
    (fun n h => (canonicalWordFirstPrefix_bound w (a+2*(n+1)) b).2 h)

noncomputable def wordFirstPrefix (a : ℕ) (w : List Bool) (b : Bool) :
    RawCycleWordTrace a (w++[b]).length → FiniteRawHistory := selectedVisitPrefix ∘ lastRawCycle a w b

lemma wordFirstPrefix_measurable (a : ℕ) (w : List Bool) (b : Bool) : Measurable (wordFirstPrefix a w b) :=
  selectedVisitPrefix_measurable.comp (lastRawCycle_measurable w a b)

end Erdos970Dependency.MarkedVisits

end

end Erdos970

end OAI
