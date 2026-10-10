import Mathlib
import OAI.Geometry.SmoothYau.Estimates.CanonicalPhaseTripleSmallBall
import OAI.Geometry.SmoothYau.Estimates.PhaseDensityInvBound
import OAI.Geometry.SmoothYau.SphereMetric.CompactProfileThreePhaseData
import OAI.Geometry.SmoothYau.SphereMetric.ExistsAlignedUnit

namespace OAI

noncomputable section
namespace YauCounterexamples
section
open Set Filter
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open MvPolynomial
open Set Filter
open scoped ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter MvPolynomial
open scoped Topology ContDiff
open Set Filter Function MvPolynomial
open scoped Topology ContDiff
open Set Filter Function MvPolynomial
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff
open scoped Topology
open Set Filter Manifold Bundle MeasureTheory
open scoped Topology ContDiff ENNReal
open Matrix
open scoped Topology Matrix.Norms.Elementwise
open Set Filter Manifold Bundle
open scoped Topology ContDiff
open Set Filter MeasureTheory ProbabilityTheory Matrix
open scoped Topology ContDiff ENNReal Matrix.Norms.Elementwise

lemma actualHessianForm_symm (φ : PhaseSpace → ℝ) (hφ : ContDiff ℝ ∞ φ) :
    (actualHessianForm φ).IsSymm := by
  constructor
  intro v w
  exact (hφ.contDiffAt.isSymmSndFDerivAt (by
    rw [minSmoothness_of_isRCLikeNormedField]
    exact le_of_lt (WithTop.coe_lt_coe.mpr (ENat.natCast_lt_top 2)))).eq v w

lemma inverse_sqrt_eventually_small {ε : ℝ} (hε : 0 < ε) :
    ∃ N : ℝ, 1 ≤ N ∧ ∀ n : ℝ, N ≤ n →
      1 ≤ n ∧ 0 < (Real.sqrt n)⁻¹ ∧ (Real.sqrt n)⁻¹ < ε ∧
        ((Real.sqrt n)⁻¹)^2 = 1/n := by
  have ht : Tendsto (fun n : ℝ => (Real.sqrt n)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp Real.tendsto_sqrt_atTop
  obtain ⟨N,hN⟩ := eventually_atTop.mp (ht.eventually (gt_mem_nhds hε))
  refine ⟨max 1 N,le_max_left _ _,?_⟩
  intro n hn
  have hn1 : 1 ≤ n := (le_max_left _ _).trans hn
  have hn0 : 0 < n := zero_lt_one.trans_le hn1
  refine ⟨hn1,inv_pos.mpr (Real.sqrt_pos.mpr hn0),hN n ((le_max_right _ _).trans hn),?_⟩
  rw [inv_pow,Real.sq_sqrt hn0.le,one_div]

theorem compact_profile_canonical_smallBall {X : Type*} [TopologicalSpace X] [CompactSpace X]
    (g : X → Fin 3 → Fin 3 → (Fin 3 → ℝ) → ℂ)
    (b₀ : X → Fin 3 → (Fin 3 → ℝ) → ℂ)
    (hg : ∀ p i j, ContDiff ℝ ∞ (g p i j)) (hb₀ : ∀ p i, ContDiff ℝ ∞ (b₀ p i))
    (hg0 : ∀ p i j, g p i j 0 = if i = j then 1 else 0)
    (hdg0 : ∀ p i j, fderiv ℝ (g p i j) 0 = 0)
    (hgc : ∀ i j k, Continuous (fun q : X × (Fin 3 → ℝ) => iteratedFDeriv ℝ k (g q.1 i j) q.2))
    (hbc : ∀ i k, Continuous (fun q : X × (Fin 3 → ℝ) => iteratedFDeriv ℝ k (b₀ q.1 i) q.2))
    (φ : X → PhaseSpace → ℝ) (hφ : ∀ p, ContDiff ℝ ∞ (φ p))
    (hφ0 : Continuous (fun p => φ p 0))
    (hφ2 : Continuous (fun q : X × PhaseSpace => iteratedFDeriv ℝ 2 (φ q.1) q.2))
    (ha : Continuous (fun p => gradient (φ p) 0))
    (hnc : ∀ p, gradient (φ p) 0 ≠ 0 → ∃ b,
      inner ℝ (gradient (φ p) 0) b = 0 ∧ ‖b‖^2 = 1+‖gradient (φ p) 0‖^2 ∧
      0 < actualHessianForm (φ p) (gradient (φ p) 0) (gradient (φ p) 0)+actualHessianForm (φ p) b b)
    (hcrit : ∀ p, gradient (φ p) 0 = 0 → ∃ P : Submodule ℝ PhaseSpace,
      Module.finrank ℝ P = 2 ∧ ∀ v ∈ P, v ≠ 0 → 0 < actualHessianForm (φ p) v v)
    (F : X → (Fin 3 → ℝ) → ℂ) (hF : ∀ p, ContDiff ℝ ∞ (F p))
    (hF0 : ∀ p, F p 0 = (φ p 0 : ℂ))
    (hFc : ∀ k, Continuous (fun q : X × (Fin 3 → ℝ) => iteratedFDeriv ℝ k (F q.1) q.2))
    (ζ : (Fin 3 → ℝ) → ℂ) (hζ : ζ =ᶠ[𝓝 0] fun _ => 1) (m D : ℕ) :
    ∃ κ > 0, ∃ C > 0, ∃ B > 0, ∃ r₀ > 0, ∃ K > 0, ∃ N : ℝ, 1 ≤ N ∧
      ∀ p (n : ℝ), N ≤ n → ∃ (z : Fin 3 → Fin 3 → ℂ) (Q : Fin 3 → ComplexPhaseMatrix),
        (∀ ℓ, ‖z ℓ‖ ≤ B) ∧ (∀ ℓ, ∑ i, z ℓ i*z ℓ i = -1) ∧
        (∀ ℓ, PhaseMatrixValid (actualHessianForm (φ p)) (z ℓ) κ C (Q ℓ)) ∧
        (∀ ℓ, ‖phaseRealVector (z ℓ)-gradient (φ p) 0‖ ≤ (Real.sqrt n)⁻¹) ∧
      let U := fun ℓ => canonicalCutoffWave (g p) (b₀ p) (φ p 0 : ℂ) (z ℓ) (Q ℓ) ζ m D n
      ∀ x : Fin 3 → ℝ, ‖x‖ < r₀ → ‖x‖ ≤ 1/n →
      ∀ R : ℝ, 0 ≤ R → R ≤ n^6*Real.exp (n*(F p x).re) →
      let W := Real.exp (n*(F p x).re)+R
      ∀ (Ω : Type*) [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
        (noise : Ω → ((Fin 1 ⊕ Fin 3) → ℝ)), Measurable noise → ∀ r : ℝ, 0 ≤ r →
      (μ.prod (Measure.pi (fun _ : Fin 3 => stdGaussian ℂ)))
        {v | complexRealResponse (fun ℓ => complexWaveJet n (W : ℂ) (U ℓ) x) v.2+noise v.1 ∈
          Metric.closedBall 0 r} ≤ ENNReal.ofReal (K*n^28*r^4) := by
  let a := fun p => gradient (φ p) 0
  obtain ⟨δ₀,hδ₀,κ,hκ,η,hη,C,hC,hdata⟩ := compact_profile_three_phase_data
    (fun p => actualHessianForm (φ p)) a (continuous_actualHessianForm φ hφ2) ha
    (fun p => actualHessianForm_symm (φ p) (hφ p)) hnc hcrit
  obtain ⟨A₀,hA₀⟩ := isCompact_univ.exists_bound_of_continuousOn ha.continuousOn
  let A := max A₀ 0
  have hA : 0 ≤ A := le_max_right _ _
  have hAa (p) : ‖a p‖ ≤ A := (hA₀ p (mem_univ p)).trans (le_max_left _ _)
  obtain ⟨r₀,hr₀,c₀,hc₀,ε,hε,hsmall⟩ := canonical_phase_triple_smallBall g b₀ hg hb₀ hg0 hdg0 hgc hbc
    φ hφ0 hφ2 F hF hF0 hFc (2*A+3) C κ (A+1) η (by linarith) hη ζ hζ m D
  obtain ⟨N,hN,hthreshold⟩ := inverse_sqrt_eventually_small (lt_min hδ₀ (lt_min hε zero_lt_one))
  refine ⟨κ,hκ,C,hC,2*A+3,by positivity,r₀,hr₀,
    16*(Real.sqrt η/2*(c₀/2)^4)⁻¹,by positivity,N,hN,?_⟩
  intro p n hn
  obtain ⟨hn1,hδ,hδsmall,hδsq⟩ := hthreshold n hn
  let δ := (Real.sqrt n)⁻¹
  have hδ₀le : δ ≤ δ₀ := (hδsmall.trans_le (min_le_left _ _)).le
  have hδε : δ < ε := hδsmall.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have hδ1 : δ ≤ 1 := (hδsmall.trans_le ((min_le_right _ _).trans (min_le_right _ _))).le
  obtain ⟨ν,hν,halign⟩ := exists_aligned_unit (a p)
  obtain ⟨b,c,hb,hc,hbn,hcn,hbA,hcA,hang,Q,hz,hnull,hQ⟩ :=
    (hdata p ν hν halign δ ⟨hδ.le,hδ₀le⟩).bounded_spec hν halign hA (hAa p) hδ.le hδ1
  let z := ![complexPhaseVector (a p) b,complexPhaseVector (a p) c,
    complexPhaseVector (a p+δ • ν) (shiftedPhaseImag (a p) ν b δ)]
  refine ⟨z,Q,hz,hnull,hQ,three_phase_real_deviation (a p) ν b c
    (shiftedPhaseImag (a p) ν b δ) δ hν hδ.le,?_⟩
  dsimp only
  intro x hxr hx R hR0 hR Ω _ μ _ noise hnoise r hr
  exact (hsmall p n δ hn1 hδ hδε hδsq (a p) ν b c (shiftedPhaseImag (a p) ν b δ)
    ((hAa p).trans (by linarith)) hν hb hc hbn hcn hbA hcA hang Q hz hnull hQ
    x hxr hx R hR0 hR Ω μ noise hnoise r hr).trans
      (phase_density_power_bound η c₀ n δ r hη hc₀ hn1 hδ hδsq hr)


end

open Set Filter
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open MvPolynomial
open Set Filter
open scoped ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter MvPolynomial
open scoped Topology ContDiff
open Set Filter Function MvPolynomial
open scoped Topology ContDiff
open Set Filter Function MvPolynomial
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff
open scoped Topology
open Set Filter Manifold Bundle MeasureTheory
open scoped Topology ContDiff ENNReal
open Matrix
open scoped Topology Matrix.Norms.Elementwise
open Set Filter Manifold Bundle
open scoped Topology ContDiff
open Set Filter MeasureTheory ProbabilityTheory Matrix
open scoped Topology ContDiff ENNReal Matrix.Norms.Elementwise
theorem compact_profile_canonical_smallBall_uniform_orders {X : Type*} [TopologicalSpace X] [CompactSpace X]
    (g : X → Fin 3 → Fin 3 → (Fin 3 → ℝ) → ℂ)
    (b₀ : X → Fin 3 → (Fin 3 → ℝ) → ℂ)
    (hg : ∀ p i j, ContDiff ℝ ∞ (g p i j)) (hb₀ : ∀ p i, ContDiff ℝ ∞ (b₀ p i))
    (hg0 : ∀ p i j, g p i j 0 = if i = j then 1 else 0)
    (hdg0 : ∀ p i j, fderiv ℝ (g p i j) 0 = 0)
    (hgc : ∀ i j k, Continuous (fun q : X × (Fin 3 → ℝ) => iteratedFDeriv ℝ k (g q.1 i j) q.2))
    (hbc : ∀ i k, Continuous (fun q : X × (Fin 3 → ℝ) => iteratedFDeriv ℝ k (b₀ q.1 i) q.2))
    (φ : X → PhaseSpace → ℝ) (hφ : ∀ p, ContDiff ℝ ∞ (φ p))
    (hφ0 : Continuous (fun p => φ p 0))
    (hφ2 : Continuous (fun q : X × PhaseSpace => iteratedFDeriv ℝ 2 (φ q.1) q.2))
    (ha : Continuous (fun p => gradient (φ p) 0))
    (hnc : ∀ p, gradient (φ p) 0 ≠ 0 → ∃ b,
      inner ℝ (gradient (φ p) 0) b = 0 ∧ ‖b‖^2 = 1+‖gradient (φ p) 0‖^2 ∧
      0 < actualHessianForm (φ p) (gradient (φ p) 0) (gradient (φ p) 0)+actualHessianForm (φ p) b b)
    (hcrit : ∀ p, gradient (φ p) 0 = 0 → ∃ P : Submodule ℝ PhaseSpace,
      Module.finrank ℝ P = 2 ∧ ∀ v ∈ P, v ≠ 0 → 0 < actualHessianForm (φ p) v v)
    :
    ∃ κ > 0, ∃ C > 0, ∃ B > 0,
    ∀ (F : X → (Fin 3 → ℝ) → ℂ) (_hF : ∀ p, ContDiff ℝ ∞ (F p))
    (_hF0 : ∀ p, F p 0 = (φ p 0 : ℂ))
    (_hFc : ∀ k, Continuous (fun q : X × (Fin 3 → ℝ) => iteratedFDeriv ℝ k (F q.1) q.2))
    (ζ : (Fin 3 → ℝ) → ℂ) (_hζ : ζ =ᶠ[𝓝 0] fun _ => 1) (m D : ℕ),
    ∃ r₀ > 0, ∃ K > 0, ∃ N : ℝ, 1 ≤ N ∧
      ∀ p (n : ℝ), N ≤ n → ∃ (z : Fin 3 → Fin 3 → ℂ) (Q : Fin 3 → ComplexPhaseMatrix),
        (∀ ℓ, ‖z ℓ‖ ≤ B) ∧ (∀ ℓ, ∑ i, z ℓ i*z ℓ i = -1) ∧
        (∀ ℓ, PhaseMatrixValid (actualHessianForm (φ p)) (z ℓ) κ C (Q ℓ)) ∧
        (∀ ℓ, ‖phaseRealVector (z ℓ)-gradient (φ p) 0‖ ≤ (Real.sqrt n)⁻¹) ∧
      let U := fun ℓ => canonicalCutoffWave (g p) (b₀ p) (φ p 0 : ℂ) (z ℓ) (Q ℓ) ζ m D n
      ∀ x : Fin 3 → ℝ, ‖x‖ < r₀ → ‖x‖ ≤ 1/n →
      ∀ R : ℝ, 0 ≤ R → R ≤ n^6*Real.exp (n*(F p x).re) →
      let W := Real.exp (n*(F p x).re)+R
      ∀ (Ω : Type*) [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
        (noise : Ω → ((Fin 1 ⊕ Fin 3) → ℝ)), Measurable noise → ∀ r : ℝ, 0 ≤ r →
      (μ.prod (Measure.pi (fun _ : Fin 3 => stdGaussian ℂ)))
        {v | complexRealResponse (fun ℓ => complexWaveJet n (W : ℂ) (U ℓ) x) v.2+noise v.1 ∈
          Metric.closedBall 0 r} ≤ ENNReal.ofReal (K*n^28*r^4) := by
  let a := fun p => gradient (φ p) 0
  obtain ⟨δ₀,hδ₀,κ,hκ,η,hη,C,hC,hdata⟩ := compact_profile_three_phase_data
    (fun p => actualHessianForm (φ p)) a (continuous_actualHessianForm φ hφ2) ha
    (fun p => actualHessianForm_symm (φ p) (hφ p)) hnc hcrit
  obtain ⟨A₀,hA₀⟩ := isCompact_univ.exists_bound_of_continuousOn ha.continuousOn
  let A := max A₀ 0
  have hA : 0 ≤ A := le_max_right _ _
  have hAa (p) : ‖a p‖ ≤ A := (hA₀ p (mem_univ p)).trans (le_max_left _ _)
  refine ⟨κ,hκ,C,hC,2*A+3,by positivity,?_⟩
  intro F hF hF0 hFc ζ hζ m D
  obtain ⟨r₀,hr₀,c₀,hc₀,ε,hε,hsmall⟩ := canonical_phase_triple_smallBall g b₀ hg hb₀ hg0 hdg0 hgc hbc
    φ hφ0 hφ2 F hF hF0 hFc (2*A+3) C κ (A+1) η (by linarith) hη ζ hζ m D
  obtain ⟨N,hN,hthreshold⟩ := inverse_sqrt_eventually_small (lt_min hδ₀ (lt_min hε zero_lt_one))
  refine ⟨r₀,hr₀,
    16*(Real.sqrt η/2*(c₀/2)^4)⁻¹,by positivity,N,hN,?_⟩
  intro p n hn
  obtain ⟨hn1,hδ,hδsmall,hδsq⟩ := hthreshold n hn
  let δ := (Real.sqrt n)⁻¹
  have hδ₀le : δ ≤ δ₀ := (hδsmall.trans_le (min_le_left _ _)).le
  have hδε : δ < ε := hδsmall.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have hδ1 : δ ≤ 1 := (hδsmall.trans_le ((min_le_right _ _).trans (min_le_right _ _))).le
  obtain ⟨ν,hν,halign⟩ := exists_aligned_unit (a p)
  obtain ⟨b,c,hb,hc,hbn,hcn,hbA,hcA,hang,Q,hz,hnull,hQ⟩ :=
    (hdata p ν hν halign δ ⟨hδ.le,hδ₀le⟩).bounded_spec hν halign hA (hAa p) hδ.le hδ1
  let z := ![complexPhaseVector (a p) b,complexPhaseVector (a p) c,
    complexPhaseVector (a p+δ • ν) (shiftedPhaseImag (a p) ν b δ)]
  refine ⟨z,Q,hz,hnull,hQ,three_phase_real_deviation (a p) ν b c
    (shiftedPhaseImag (a p) ν b δ) δ hν hδ.le,?_⟩
  dsimp only
  intro x hxr hx R hR0 hR Ω _ μ _ noise hnoise r hr
  exact (hsmall p n δ hn1 hδ hδε hδsq (a p) ν b c (shiftedPhaseImag (a p) ν b δ)
    ((hAa p).trans (by linarith)) hν hb hc hbn hcn hbA hcA hang Q hz hnull hQ
    x hxr hx R hR0 hR Ω μ noise hnoise r hr).trans
      (phase_density_power_bound η c₀ n δ r hη hc₀ hn1 hδ hδsq hr)



end YauCounterexamples
end

end OAI
