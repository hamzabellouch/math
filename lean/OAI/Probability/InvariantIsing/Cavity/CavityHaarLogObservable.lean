import OAI.Probability.InvariantIsing.Cavity.CavityHaarSpinModel
import OAI.Probability.InvariantIsing.Cavity.CavityVanishingPenalty

namespace OAI

/-! The capped logarithmic observable in the actual fresh-Haar Gibbs
model, with its measurable original prior and quadratic penalty. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron

namespace InvariantIsing

def cavityHaarLogObservable {m q d n : ℕ} {dims : Fin m → ℕ} {Ω X : Type*}
    [MeasurableSpace X] (ν : Ω → Measure X)
    (e : Fin d → Fin m × Fin q) (v : Ω → (a : Fin m) → X → Fin (dims a) → ℝ)
    (A₀ : (a : Fin m) → Matrix (Fin (dims a)) (Fin q) ℝ)
    (B : Ω → CavityFactorBlocks d n) (t cap δ : ℝ)
    (p : Ω × ((a : Fin m) → Orthogonal (dims a))) : ℝ :=
  Real.log (∫ x, Real.exp
    (min (t*cavityLogFactor (B p.1).1 (B p.1).2.1 (B p.1).2.2
      (cavitySelectedSiteProjection e (v p.1) (cavityGroupHaarFrames A₀ p.2) x.1) x.2) cap -
      δ*(1+‖cavitySelectedSiteProjection e (v p.1) (cavityGroupHaarFrames A₀ p.2) x.1‖^2))
    ∂(ν p.1).prod (uniformSpinPrior n : Measure (Spin n)))

lemma measurable_cavityHaarLogObservable {m q d n : ℕ} {dims : Fin m → ℕ} {Ω X : Type*}
    [MeasurableSpace Ω] [MeasurableSpace X] [Countable X] [MeasurableSingletonClass X]
    (ν : Ω → Measure X) (hν : Measurable ν) [∀ ω, IsProbabilityMeasure (ν ω)]
    (e : Fin d → Fin m × Fin q) (v : Ω → (a : Fin m) → X → Fin (dims a) → ℝ)
    (hv : ∀ x, Measurable (fun ω a => v ω a x))
    (A₀ : (a : Fin m) → Matrix (Fin (dims a)) (Fin q) ℝ)
    (B : Ω → CavityFactorBlocks d n) (hB : Measurable B) (t cap δ : ℝ) :
    Measurable (cavityHaarLogObservable ν e v A₀ B t cap δ) := by
  let U := (a : Fin m) → Orthogonal (dims a)
  let κ := cavityHaarSpinPriorKernel (U := U) ν hν (uniformSpinPrior n : Measure (Spin n))
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
  change Measurable (fun p => cavityHaarLogObservable ν e v A₀ B t cap δ p)
  simpa only [κ, cavityHaarSpinPriorKernel_apply, H, Y, cavityHaarLogObservable,
    referencePartition] using hh

lemma cavity_capped_factor_growth_bound {d n : ℕ} (B : CavityFactorBlocks d n)
    {D R : ℝ} (hD : cavityFactorSize B.1 B.2.1 B.2.2 ≤ D)
    (y : EuclideanSpace ℝ (Fin d)) (hy : ‖y‖^2 ≤ R) (ε : Spin n)
    (t cap δ : ℝ) (hcap : 0 ≤ cap) :
    |min (t*cavityLogFactor B.1 B.2.1 B.2.2 y ε) cap - δ*(1+‖y‖^2)| ≤
      (|t| *D+|δ|)*(1+R) := by
  have hd := (cavityFactorSize_nonneg B.1 B.2.1 B.2.2).trans hD
  have hg : |cavityLogFactor B.1 B.2.1 B.2.2 y ε| ≤ D*(1+R) :=
    (cavity_logFactor_growth B.1 B.2.1 B.2.2 y ε).trans
      (mul_le_mul hD (add_le_add (le_refl 1) hy) (by positivity) hd)
  calc
    _ ≤ |min (t*cavityLogFactor B.1 B.2.1 B.2.2 y ε) cap|+|δ*(1+‖y‖^2)| := abs_sub _ _
    _ ≤ |t| *(D*(1+R))+|δ| *(1+R) := by
      rw [abs_mul, abs_of_nonneg (by positivity : 0 ≤ 1+‖y‖^2)]
      exact add_le_add ((cavity_abs_min_cap hcap).trans
        (by rw [abs_mul]; exact mul_le_mul_of_nonneg_left hg (abs_nonneg t)))
        (mul_le_mul_of_nonneg_left (add_le_add (le_refl 1) hy) (abs_nonneg δ))
    _ = _ := by ring

lemma cavityHaarLogObservable_bound {m q d n : ℕ} {dims : Fin m → ℕ} {Ω X : Type*}
    [MeasurableSpace X] [Countable X] [MeasurableSingletonClass X]
    (ν : Ω → Measure X) [∀ ω, IsProbabilityMeasure (ν ω)]
    (e : Fin d → Fin m × Fin q) (v : Ω → (a : Fin m) → X → Fin (dims a) → ℝ)
    (A₀ : (a : Fin m) → Matrix (Fin (dims a)) (Fin q) ℝ)
    (B : Ω → CavityFactorBlocks d n) (t cap δ : ℝ) (hcap : 0 ≤ cap)
    {D R : ℝ} (hD : ∀ ω, cavityFactorSize (B ω).1 (B ω).2.1 (B ω).2.2 ≤ D)
    (hy : ∀ ω W x, ‖cavitySelectedSiteProjection e (v ω) (cavityGroupHaarFrames A₀ W) x‖^2 ≤ R)
    (p : Ω × ((a : Fin m) → Orthogonal (dims a))) :
    |cavityHaarLogObservable ν e v A₀ B t cap δ p| ≤ (|t| *D+|δ|)*(1+R) := by
  simpa only [logMean, one_mul, div_one, cavityHaarLogObservable] using
    logMean_bounds ((ν p.1).prod (uniformSpinPrior n : Measure (Spin n)))
      (measurable_of_countable _) (by norm_num : (0:ℝ)<1)
      (fun x => cavity_capped_factor_growth_bound (B p.1) (hD p.1) _ (hy p.1 p.2 x.1) x.2
        t cap δ hcap)

end InvariantIsing

end

end OAI
