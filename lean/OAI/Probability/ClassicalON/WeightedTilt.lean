import OAI.Probability.ClassicalON.FerromagneticMean

namespace OAI

universe uX uY

noncomputable section
open MeasureTheory
namespace ClassicalON

section Tilt
variable {X : Type uX} [Preorder X] [TopologicalSpace X] [CompactSpace X]
  [MeasurableSpace X] [BorelSpace X] {μ : Measure X} [IsProbabilityMeasure μ]

theorem weightedMean_tilt_mono {w v f : X → ℝ} (hw : Continuous w) (hv : Continuous v)
    (hp : ∀ x,0<w x) (hvp : ∀ x,0<v x) (hA : ContinuousAssociated μ w)
    (hf : Continuous f) (hfn : ∀ x,0≤f x) (hfm : Monotone f)
    (hr : Monotone (fun x => v x/w x)) : weightedMean μ w f ≤ weightedMean μ v f := by
  have hrc : Continuous (fun x => v x/w x) := hv.div hw (fun x => (hp x).ne')
  have h := hA f (fun x => v x/w x) hf hrc hfn
    (fun x => div_nonneg (hvp x).le (hp x).le) hfm hr
  rw [weightedMean_inequality_iff hw hp] at h
  have he1 : (fun x => w x*(v x/w x))=v := by
    funext x
    field_simp [(hp x).ne']
  have he2 : (fun x => w x*(f x*(v x/w x)))=(fun x => v x*f x) := by
    funext x
    field_simp [(hp x).ne']
  rw [he1,he2] at h
  unfold weightedMean
  exact (div_le_div_iff₀ (compact_integral_pos hw hp) (compact_integral_pos hv hvp)).2 (by nlinarith)

end Tilt

section Product
variable {X : Type uX} {Y : Type uY} [TopologicalSpace X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
  [TopologicalSpace Y] [CompactSpace Y] [MeasurableSpace Y] [BorelSpace Y]
  [SecondCountableTopology X] [FirstCountableTopology Y] [LocallyCompactSpace Y]
  (μ : Measure X) (ν : Measure Y) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]

def marginalWeight (w : Y×X → ℝ) (y : Y) : ℝ := ∫ x,w (y,x) ∂μ

def conditionalMean (w f : Y×X → ℝ) (y : Y) : ℝ :=
  weightedMean μ (fun x => w (y,x)) (fun x => f (y,x))

omit [CompactSpace Y] [MeasurableSpace Y] [BorelSpace Y] [SecondCountableTopology X] in
theorem marginalWeight_continuous {w : Y×X → ℝ} (hw : Continuous w) :
    Continuous (marginalWeight μ w) := compact_parametric_integral _ hw

omit [CompactSpace Y] [MeasurableSpace Y] [BorelSpace Y] [SecondCountableTopology X]
  [FirstCountableTopology Y] [LocallyCompactSpace Y] in
theorem marginalWeight_pos {w : Y×X → ℝ} (hw : Continuous w) (hp : ∀ p,0<w p) (y : Y) :
    0 < marginalWeight μ w y := compact_integral_pos (by fun_prop) (fun x => hp (y,x))

omit [CompactSpace Y] [MeasurableSpace Y] [BorelSpace Y] [SecondCountableTopology X] in
theorem conditionalMean_continuous {w f : Y×X → ℝ} (hw : Continuous w) (hf : Continuous f)
    (hp : ∀ p,0<w p) : Continuous (conditionalMean μ w f) := by
  exact (compact_parametric_integral _ (hw.mul hf)).div (marginalWeight_continuous μ hw)
    (fun y => (marginalWeight_pos μ hw hp y).ne')

omit [FirstCountableTopology Y] [LocallyCompactSpace Y] in
theorem weightedMean_prod {w f : Y×X → ℝ} (hw : Continuous w) (hf : Continuous f)
    (hp : ∀ p,0<w p) :
    weightedMean (ν.prod μ) w f = weightedMean ν (marginalWeight μ w) (conditionalMean μ w f) := by
  unfold weightedMean
  rw [integral_prod (fun p => w p*f p) (compact_integrable (show Continuous (fun p => w p*f p) from hw.mul hf)),
    integral_prod w (compact_integrable hw)]
  congr 1
  apply integral_congr_ae
  filter_upwards with y
  dsimp only [marginalWeight,conditionalMean,weightedMean]
  have hm : (∫ x,w (y,x) ∂μ)≠0 := (marginalWeight_pos μ hw hp y).ne'
  field_simp

end Product
end ClassicalON

end

end OAI
