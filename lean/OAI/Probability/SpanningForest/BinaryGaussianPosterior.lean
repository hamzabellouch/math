import OAI.Probability.SpanningForest.FiniteGaussianPosterior

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal BigOperators ProbabilityTheory

namespace Problem336.FinitePosterior

def binaryValue (b : Bool) : ℝ := if b then 1 else 0

lemma binaryValue_binary (b : Bool) : binaryValue b = 0 ∨ binaryValue b = 1 := by
  cases b <;> simp [binaryValue]

def binarySummary {I ι : Type*} (observed : ι → I) (target : I) (x : I → Bool) :
    Bool × (ι → Bool) := (x target, fun j => x (observed j))

lemma measurable_binarySummary {I ι : Type*} (observed : ι → I) (target : I) :
    Measurable (binarySummary observed target) := by
  unfold binarySummary
  fun_prop

def gaussianFiniteTilt {I ι : Type*} [Fintype ι] (ν : Measure (I → Bool))
    (observed : ι → I) (target : I) (t : ℝ) (y : ι → ℝ) : ℝ :=
  (∫ x, Real.exp (∑ j, (y j - t / 2) * binaryValue (x (observed j))) *
    binaryValue (x target) ∂ν) /
  (∫ x, Real.exp (∑ j, (y j - t / 2) * binaryValue (x (observed j))) ∂ν)

lemma finiteMarginal_ratio_eq_integral {A Θ : Type*} [MeasurableSpace A]
    [Fintype Θ] [MeasurableSpace Θ] [MeasurableSingletonClass Θ]
    (ν : Measure A) [IsFiniteMeasure ν] (R : A → Θ) (hR : Measurable R)
    (w g : Θ → ℝ) :
    (∑ θ, ((ν.map R) {θ}).toReal * w θ * g θ) /
      (∑ θ, ((ν.map R) {θ}).toReal * w θ) =
    (∫ x, w (R x) * g (R x) ∂ν) / (∫ x, w (R x) ∂ν) := by
  rw [← integral_map_of_stronglyMeasurable hR
      (measurable_of_countable (fun θ => w θ * g θ)).stronglyMeasurable,
    ← integral_map_of_stronglyMeasurable hR (measurable_of_countable w).stronglyMeasurable]
  simp only [integral_fintype (Integrable.of_finite), Measure.real, smul_eq_mul, mul_assoc]

theorem binaryField_gaussian_condExp
    {Ω I ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (ν : Measure (I → Bool)) [IsProbabilityMeasure ν]
    (X : Ω → (I → Bool)) (noise : Ω → (ι → ℝ))
    (hX : Measurable X) (hnoise : Measurable noise)
    (observed : ι → I) (target : I) (t : ℝ≥0) (ht : t ≠ 0)
    (hprior : P.map X = ν)
    (hnoiseLaw : P.map noise = Measure.pi (fun _ : ι => gaussianReal 0 t))
    (hindep : X ⟂ᵢ[P] noise) :
    let Yobs := fun ω j => (t : ℝ) * binaryValue (X ω (observed j)) + noise ω j
    P[fun ω => binaryValue (X ω target) |
      (inferInstance : MeasurableSpace (ι → ℝ)).comap Yobs] =ᵐ[P]
      fun ω => gaussianFiniteTilt ν observed target t (Yobs ω) := by
  classical
  let R : (I → Bool) → Bool × (ι → Bool) := binarySummary observed target
  have hR : Measurable R := measurable_binarySummary observed target
  let π := ν.map R
  let : IsProbabilityMeasure π := inferInstance
  let signal : (Bool × (ι → Bool)) → ι → ℝ := fun θ j => binaryValue (θ.2 j)
  let g : (Bool × (ι → Bool)) → ℝ := fun θ => binaryValue θ.1
  have hsignal : ∀ θ j, signal θ j = 0 ∨ signal θ j = 1 := by
    intro θ j
    exact binaryValue_binary _
  have hprior' : P.map (fun ω => R (X ω)) = π := by
    change P.map (R ∘ X) = ν.map R
    rw [← Measure.map_map hR hX, hprior]
  have hindep' : (fun ω => R (X ω)) ⟂ᵢ[P] noise := by
    simpa only [Function.comp_def, id_eq] using hindep.comp hR measurable_id
  have h := gaussian_condExp_eq_exponential_ratio_of_independent P
    (fun ω => R (X ω)) noise (hR.comp hX) hnoise π t ht signal hsignal
    hprior' hnoiseLaw hindep' g
  have hratio (y : ι → ℝ) :
      (∑ θ, (π {θ}).toReal * Real.exp (∑ j, (y j - (t : ℝ) / 2) * signal θ j) * g θ) /
        (∑ θ, (π {θ}).toReal * Real.exp (∑ j, (y j - (t : ℝ) / 2) * signal θ j)) =
      gaussianFiniteTilt ν observed target t y := by
    simpa only [π, R, signal, g, binarySummary, gaussianFiniteTilt] using
      finiteMarginal_ratio_eq_integral ν R hR
        (fun θ => Real.exp (∑ j, (y j - (t : ℝ) / 2) * signal θ j)) g
  filter_upwards [h] with ω hω
  exact hω.trans (hratio _)

end Problem336.FinitePosterior

end

end OAI
