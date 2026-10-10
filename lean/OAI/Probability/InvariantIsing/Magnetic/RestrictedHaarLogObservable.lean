import OAI.Probability.InvariantIsing.Cavity.CavityHaarLogObservable
import OAI.Probability.InvariantIsing.Magnetic.RestrictedSpinPrior

namespace OAI

/-! The fresh-frame capped logarithm with its actual constrained cavity prior. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron

namespace InvariantIsing

def restrictedHaarLogObservable {m q d n : ℕ} {dims : Fin m → ℕ} {Ω X : Type*}
    [MeasurableSpace X] (C : Finset (Spin n)) (hC : C.Nonempty) (ν : Ω → Measure X)
    (e : Fin d → Fin m × Fin q) (v : Ω → (a : Fin m) → X → Fin (dims a) → ℝ)
    (A₀ : (a : Fin m) → Matrix (Fin (dims a)) (Fin q) ℝ)
    (B : Ω → CavityFactorBlocks d n) (t cap δ : ℝ)
    (p : Ω × ((a : Fin m) → Orthogonal (dims a))) : ℝ :=
  Real.log (∫ x, Real.exp
    (min (t*cavityLogFactor (B p.1).1 (B p.1).2.1 (B p.1).2.2
      (cavitySelectedSiteProjection e (v p.1) (cavityGroupHaarFrames A₀ p.2) x.1) x.2) cap -
      δ*(1+‖cavitySelectedSiteProjection e (v p.1) (cavityGroupHaarFrames A₀ p.2) x.1‖^2))
    ∂(ν p.1).prod (restrictedSpinPrior C hC : Measure (Spin n)))

lemma measurable_restrictedHaarLogObservable {m q d n : ℕ} {dims : Fin m → ℕ} {Ω X : Type*}
    [MeasurableSpace Ω] [MeasurableSpace X] [Countable X] [MeasurableSingletonClass X]
    (C : Finset (Spin n)) (hC : C.Nonempty) (ν : Ω → Measure X) (hν : Measurable ν) [∀ ω, IsProbabilityMeasure (ν ω)]
    (e : Fin d → Fin m × Fin q) (v : Ω → (a : Fin m) → X → Fin (dims a) → ℝ)
    (hv : ∀ x, Measurable (fun ω a => v ω a x))
    (A₀ : (a : Fin m) → Matrix (Fin (dims a)) (Fin q) ℝ)
    (B : Ω → CavityFactorBlocks d n) (hB : Measurable B) (t cap δ : ℝ) :
    Measurable (restrictedHaarLogObservable C hC ν e v A₀ B t cap δ) := by
  let U := (a : Fin m) → Orthogonal (dims a)
  let κ := cavityHaarSpinPriorKernel (U := U) ν hν (restrictedSpinPrior C hC : Measure (Spin n))
  let Y := fun p : (Ω × U) × (X × Spin n) =>
    cavitySelectedSiteProjection e (v p.1.1) (cavityGroupHaarFrames A₀ p.1.2) p.2.1
  have hY : Measurable Y := (measurable_cavitySelectedSiteProjection e v hv A₀).comp
    (measurable_fst.prodMk measurable_snd.fst)
  let H := fun p : (Ω × U) × (X × Spin n) =>
    min (t*cavityLogFactor (B p.1.1).1 (B p.1.1).2.1 (B p.1.1).2.2 (Y p) p.2.2) cap -
      δ*(1+‖Y p‖^2)
  have hH : Measurable H := by
    have hB' : Measurable (fun p : (Ω × U) × (X × Spin n) => B p.1.1) :=
      hB.comp measurable_fst.fst
    dsimp only [H]
    unfold cavityLogFactor cavityQuadratic
    fun_prop
  have hh := (measurable_random_referencePartition (ν := fun p => κ p) κ.measurable hH).log
  change Measurable (fun p => restrictedHaarLogObservable C hC ν e v A₀ B t cap δ p)
  simpa only [κ, cavityHaarSpinPriorKernel_apply, H, Y, restrictedHaarLogObservable,
    referencePartition] using hh

lemma restrictedHaarLogObservable_bound {m q d n : ℕ} {dims : Fin m → ℕ} {Ω X : Type*}
    [MeasurableSpace X] [Countable X] [MeasurableSingletonClass X]
    (C : Finset (Spin n)) (hC : C.Nonempty) (ν : Ω → Measure X) [∀ ω, IsProbabilityMeasure (ν ω)]
    (e : Fin d → Fin m × Fin q) (v : Ω → (a : Fin m) → X → Fin (dims a) → ℝ)
    (A₀ : (a : Fin m) → Matrix (Fin (dims a)) (Fin q) ℝ)
    (B : Ω → CavityFactorBlocks d n) (t cap δ : ℝ) (hcap : 0 ≤ cap)
    {D R : ℝ} (hD : ∀ ω, cavityFactorSize (B ω).1 (B ω).2.1 (B ω).2.2 ≤ D)
    (hy : ∀ ω W x, ‖cavitySelectedSiteProjection e (v ω) (cavityGroupHaarFrames A₀ W) x‖^2 ≤ R)
    (p : Ω × ((a : Fin m) → Orthogonal (dims a))) :
    |restrictedHaarLogObservable C hC ν e v A₀ B t cap δ p| ≤ (|t| *D+|δ|)*(1+R) := by
  simpa only [logMean, one_mul, div_one, restrictedHaarLogObservable] using
    logMean_bounds ((ν p.1).prod (restrictedSpinPrior C hC : Measure (Spin n)))
      (measurable_of_countable _) (by norm_num : (0:ℝ)<1)
      (fun x => cavity_capped_factor_growth_bound (B p.1) (hD p.1) _ (hy p.1 p.2 x.1) x.2
        t cap δ hcap)

end InvariantIsing

end

end OAI
