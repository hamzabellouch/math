import OAI.Combinatorics.Progressions.Estimates.RawSourceTolerance

namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped ContDiff NNReal BigOperators

theorem exists_raw_source_density_tolerance
    {Ω D G Z α Y : Type*} [MeasurableSpace Ω] [MeasurableSpace Y]
    [Fintype D] [DecidableEq D] [Fintype Z] [DecidableEq Z] [Fintype α] [DecidableEq α]
    {B O L : D → Type*} [∀ d, Fintype (B d)] [∀ d, DecidableEq (B d)]
    [∀ d, Fintype (O d)] [∀ d, DecidableEq (O d)] [∀ d, Nonempty (O d)]
    (c : Ω → ∀ d, B d → ℝ) (hc : ∀ d b, Measurable (fun a => c a d b))
    (z : Ω → Z → ℝ) (hz : ∀ j, Measurable (fun a => z a j))
    (sets : ∀ d, O d → Finset α) (hsets : ∀ d, Function.Injective (sets d))
    (h : D → ℕ) (hh : ∀ d, 0 < h d) (hcard : ∀ d o, (sets d o).card ≤ h d)
    (block : ∀ d, O d → B d) (hblock : ∀ d, Function.Injective (block d))
    (c₀ C : D → ℝ) (hc₀ : ∀ d, 0 < c₀ d) (hC : ∀ d, 0 ≤ C d)
    (ψ : ℝ → ℝ) (hψ : ContDiff ℝ ∞ ψ) (hrange : ∀ t, ψ t ∈ Set.Icc (0 : ℝ) 1)
    (hzero : ∀ t, |t| ≤ 1 → ψ t = 0) (hone : ∀ t, 2 ≤ |t| → ψ t = 1)
    (A T : ℝ≥0) (hLip : LipschitzWith A ψ) (hTransition : LipschitzWith T Real.smoothTransition)
    (terms : ∀ d, Finset (L d)) (weight : ∀ d, L d → ℝ)
    (exponent : ∀ d, L d → SamplerTupleIndex G B h →₀ ℕ)
    (coefficientIndex : ∀ d, L d → Z) (extra : G → Option α → Z)
    {degree : ℕ} (hdegree : ∀ d, h d ≤ degree)
    (htaildegree : ∀ d n, n ∈ terms d → (exponent d n).sum (fun _ e => e) ≤ degree)
    {Csum Wsum : ℝ} (hCsum : 0 ≤ Csum) (hWsum : 0 ≤ Wsum)
    (hwsum : ∀ d, (∑ n ∈ terms d, |weight d n|) ≤ Wsum)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ t : ℝ, 0 < t ∧ t ≤ 1 ∧
      ∀ (Q : Ω → D → ℝ) (scale : SamplerTupleIndex G B h → ℝ) (constant : Ω → D → ℝ),
      (∀ a d, Q a d ≠ 0) → (∀ k, 0 < scale k) →
      (∀ d, Measurable (fun a => constant a d)) →
      ∀ μ : Measure Ω, IsProbabilityMeasure μ →
      (∀ᵐ a ∂μ, ∀ j, |z a j| ≤ 1) →
      (∀ᵐ a ∂μ, ∀ d o, c₀ d ≤ |c a d (block d o)|) →
      (∀ᵐ a ∂μ, ∀ d o, |c a d (block d o)| ≤ C d) →
      (∀ᵐ a ∂μ, ∀ d, (∑ b, |c a d b|) ≤ Csum) →
      ∀ P : Ω × ((Σ d, O d) → ℝ) → Y, Measurable P →
      ∀ (ν : Measure Y) (f g : Y → ℝ),
      Measurable f → Measurable g → Integrable f ν → Integrable g ν →
      (∀ y, 0 ≤ f y) → (∀ y, 0 ≤ g y) →
      (μ.prod (scaledJointCubeSource h (fun i => scale (.inr i)))).map
        (fun p => P (p.1, rawSourceOutput h c sets terms weight exponent coefficientIndex extra
          Q scale constant 0 z p)) = realDensityMeasure ν f →
      (μ.prod (scaledJointCubeSource h (fun i => scale (.inr i)))).map
        (fun p => P (p.1, rawSourceOutput h c sets terms weight exponent coefficientIndex extra
          Q scale constant t z p)) = realDensityMeasure ν g →
      (∫ y, |f y-g y| ∂ν) ≤ ε := by
  obtain ⟨t, ht, ht1, hcomp⟩ := exists_raw_source_tolerance (Y := Y) c hc z hz sets hsets h hh hcard
    block hblock c₀ C hc₀ hC ψ hψ hrange hzero hone A T hLip hTransition terms weight exponent
    coefficientIndex extra hdegree htaildegree hCsum hWsum hwsum hε
  refine ⟨t, ht, ht1, ?_⟩
  intro Q scale constant hQ hscale hconstant μ hμ hbox hclow hcup hcsum P hP ν f g
    hfm hgm hfi hgi hf0 hg0 hUf hVg
  have hraw (u : ℝ) := rawSourceOutput_measurable h c hc sets terms weight exponent coefficientIndex extra
    Q scale constant hQ (fun k => (hscale k).ne') hconstant u z hz
  apply imageComparison_density_l1
    (μ.prod (scaledJointCubeSource h (fun i => scale (.inr i)))) ν
    (fun p => P (p.1, rawSourceOutput h c sets terms weight exponent coefficientIndex extra
      Q scale constant 0 z p))
    (fun p => P (p.1, rawSourceOutput h c sets terms weight exponent coefficientIndex extra
      Q scale constant t z p))
    (hP.comp (measurable_fst.prodMk (hraw 0))) (hP.comp (measurable_fst.prodMk (hraw t)))
    f g hfm hgm hfi hgi hf0 hg0 hUf hVg
  intro φ hφ hbound
  exact hcomp Q scale constant hQ hscale hconstant μ hμ hbox hclow hcup hcsum P hP φ hφ hbound

end Erdos3

end

end OAI
