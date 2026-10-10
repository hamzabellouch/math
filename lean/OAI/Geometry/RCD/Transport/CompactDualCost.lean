import OAI.Geometry.RCD.Transport.CompactCouplingSlack

namespace OAI

/-! # A saturated dual pair minimizes the compact transport cost -/

open Set Filter MeasureTheory
noncomputable section
namespace RegularPointCoordinates
variable {X Y : Type*} [MetricSpace X] [MetricSpace Y]
  [MeasurableSpace X] [MeasurableSpace Y] [BorelSpace X] [BorelSpace Y]
  [CompactSpace X] [CompactSpace Y]
  (μ : Measure X) (ν : Measure Y) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]

omit [IsProbabilityMeasure ν] in
theorem coupling_potential_integral (π : Measure (X × Y))
    (hl : π.map Prod.fst=μ) (hr : π.map Prod.snd=ν)
    (f : C(X,ℝ)) (g : C(Y,ℝ)) (c : ℝ) :
    (∫ z, f z.1+g z.2+c ∂π)=(∫ x, f x ∂μ)+(∫ y, g y ∂ν)+c := by
  let : IsProbabilityMeasure (π.map Prod.fst) := by rw [hl]; infer_instance
  let : IsProbabilityMeasure π := Measure.isProbabilityMeasure_of_map measurable_fst.aemeasurable
  have hf : Integrable (fun z : X × Y => f z.1) π :=
    (f.continuous.comp continuous_fst).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hg : Integrable (fun z : X × Y => g z.2) π :=
    (g.continuous.comp continuous_snd).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  rw [integral_add (f := fun z : X × Y => f z.1+g z.2) (g := fun _ : X × Y => c)
    (hf.add hg) (integrable_const c),
    integral_add (f := fun z : X × Y => f z.1) (g := fun z : X × Y => g z.2) hf hg]
  have he : (∫ z, f z.1 ∂π)=∫ x, f x ∂μ := by
    rw [← hl,integral_map measurable_fst.aemeasurable f.continuous.aestronglyMeasurable]
  have he' : (∫ z, g z.2 ∂π)=∫ y, g y ∂ν := by
    rw [← hr,integral_map measurable_snd.aemeasurable g.continuous.aestronglyMeasurable]
  simp only [he,he',integral_const,probReal_univ,smul_eq_mul,one_mul]

omit [IsProbabilityMeasure ν] in
theorem compact_dual_cost_minimizer [SecondCountableTopology Y]
    (Q : Measure (X × Y)) (hQl : Q.map Prod.fst=μ) (hQr : Q.map Prod.snd=ν)
    (f : C(X,ℝ)) (g : C(Y,ℝ)) (cost : C(X × Y,ℝ)) (c : ℝ)
    (hdual : ∀ x y, y ∈ ν.support → f x+g y+c ≤ cost (x,y))
    (heq : ∀ᵐ z ∂Q, f z.1+g z.2+c=cost z) :
    ∀ π : Measure (X × Y), π.map Prod.fst=μ → π.map Prod.snd=ν →
      (∫ z, cost z ∂Q) ≤ ∫ z, cost z ∂π := by
  intro π hl hr
  let : IsProbabilityMeasure (π.map Prod.fst) := by rw [hl]; infer_instance
  let : IsProbabilityMeasure π := Measure.isProbabilityMeasure_of_map measurable_fst.aemeasurable
  have hle := integral_mono_ae
    (((f.continuous.comp continuous_fst).add (g.continuous.comp continuous_snd)).add continuous_const
      |>.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
    (cost.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
    (by
      filter_upwards [coupling_snd_support (ν := ν) (π := π) hr] with z hz
      exact hdual z.1 z.2 hz)
  calc
    (∫ z, cost z ∂Q) = ∫ z, f z.1+g z.2+c ∂Q := integral_congr_ae (by
      filter_upwards [heq] with z hz
      exact hz.symm)
    _ = (∫ x, f x ∂μ)+(∫ y, g y ∂ν)+c := coupling_potential_integral μ ν Q hQl hQr f g c
    _ = (∫ z, f z.1+g z.2+c ∂π) := (coupling_potential_integral μ ν π hl hr f g c).symm
    _ ≤ (∫ z, cost z ∂π) := hle

end RegularPointCoordinates

end

end OAI
