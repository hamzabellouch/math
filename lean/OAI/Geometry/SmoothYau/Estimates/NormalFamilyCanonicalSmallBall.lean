import Mathlib
import OAI.Geometry.SmoothYau.Limits.CompactProfileCanonicalSmallBall
import OAI.Geometry.SmoothYau.Limits.ContinuousGradientIterated
import OAI.Geometry.SmoothYau.Smoothness.AdmissibleCutoffWaveLocalizedDerivatives

namespace OAI

noncomputable section
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
open Set Filter
open scoped ContDiff Topology
open Set Filter MeasureTheory ProbabilityTheory Matrix
open scoped Topology ContDiff ENNReal Matrix.Norms.Elementwise
namespace YauCounterexamples

theorem normal_family_canonical_smallBall_uniform
    (g : SmoothMetric NormalWaveSpace NormalWaveSpace)
    (φ : NormalWaveSpace → ℝ) (hφ : ContDiff ℝ ∞ φ)
    {K : Set NormalWaveSpace} (hK : IsCompact K)
    (A : NormalWaveParameter × (Fin 3 → ℝ) → Matrix (Fin 3) (Fin 3) ℂ)
    (b : NormalWaveParameter × (Fin 3 → ℝ) → Fin 3 → ℂ)
    (hA : ContDiff ℝ ∞ A) (hb : ContDiff ℝ ∞ b)
    (hA0 : ∀ q ∈ metricFrameSet g K, ∀ i j, A (q,0) i j = if i = j then 1 else 0)
    (hAd : ∀ q ∈ metricFrameSet g K, ∀ i j, fderiv ℝ (fun x => A (q,x) i j) 0 = 0)
    (hnc : ∀ q ∈ metricFrameSet g K, gradient (normalWaveProfile g φ q) 0 ≠ 0 → ∃ v,
      inner ℝ (gradient (normalWaveProfile g φ q) 0) v = 0 ∧
      ‖v‖^2 = 1+‖gradient (normalWaveProfile g φ q) 0‖^2 ∧
      0 < actualHessianForm (normalWaveProfile g φ q) (gradient (normalWaveProfile g φ q) 0)
        (gradient (normalWaveProfile g φ q) 0)+actualHessianForm (normalWaveProfile g φ q) v v)
    (hcrit : ∀ q ∈ metricFrameSet g K, gradient (normalWaveProfile g φ q) 0 = 0 →
      ∃ P : Submodule ℝ PhaseSpace, Module.finrank ℝ P = 2 ∧
        ∀ v ∈ P, v ≠ 0 → 0 < actualHessianForm (normalWaveProfile g φ q) v v) :
    ∃ κ > 0, ∃ C > 0, ∃ B > 0,
    ∀ (ζ : (Fin 3 → ℝ) → ℂ) (_hζ : ζ =ᶠ[𝓝 0] fun _ => 1) (m D : ℕ),
    ∃ r₀ > 0, ∃ C₀ > 0, ∃ N : ℝ, 1 ≤ N ∧
      ∀ q ∈ metricFrameSet g K, ∀ (n : ℝ), N ≤ n → ∃ (z : Fin 3 → Fin 3 → ℂ) (Q : Fin 3 → ComplexPhaseMatrix),
        (∀ ℓ, ‖z ℓ‖ ≤ B) ∧ (∀ ℓ, ∑ i, z ℓ i*z ℓ i = -1) ∧
        (∀ ℓ, PhaseMatrixValid (actualHessianForm (normalWaveProfile g φ q)) (z ℓ) κ C (Q ℓ)) ∧
        (∀ ℓ, ‖phaseRealVector (z ℓ)-gradient (normalWaveProfile g φ q) 0‖ ≤ (Real.sqrt n)⁻¹) ∧
      let U := fun ℓ => normalFamilyWave g φ A b q (z ℓ) (Q ℓ) ζ m D n
      ∀ x : Fin 3 → ℝ, ‖x‖ < r₀ → ‖x‖ ≤ 1/n →
      ∀ R : ℝ, 0 ≤ R → R ≤ n^6*Real.exp (n*normalWaveProfile g φ q (normalWaveEquiv x)) →
      let W := Real.exp (n*normalWaveProfile g φ q (normalWaveEquiv x))+R
      ∀ (Ω : Type*) [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
        (noise : Ω → ((Fin 1 ⊕ Fin 3) → ℝ)), Measurable noise → ∀ r : ℝ, 0 ≤ r →
      (μ.prod (Measure.pi (fun _ : Fin 3 => stdGaussian ℂ)))
        {v | complexRealResponse (fun ℓ => complexWaveJet n (W : ℂ) (U ℓ) x) v.2+noise v.1 ∈
          Metric.closedBall 0 r} ≤ ENNReal.ofReal (C₀*n^28*r^4) := by
  let X := metricFrameSet g K
  let : CompactSpace X := isCompact_iff_compactSpace.mp (metricFrameSet_isCompact g hK)
  let G : X → Fin 3 → Fin 3 → (Fin 3 → ℝ) → ℂ := fun q i j x => A (q.val,x) i j
  let β : X → Fin 3 → (Fin 3 → ℝ) → ℂ := fun q j x => b (q.val,x) j
  let Φ : X → PhaseSpace → ℝ := fun q => normalWaveProfile g φ q.val
  have hG (q : X) (i j : Fin 3) : ContDiff ℝ ∞ (G q i j) :=
    (contDiff_pi.mp (contDiff_pi.mp hA i) j).comp (contDiff_const.prodMk contDiff_id)
  have hβ (q : X) (j : Fin 3) : ContDiff ℝ ∞ (β q j) :=
    (contDiff_pi.mp hb j).comp (contDiff_const.prodMk contDiff_id)
  have hG0 (q : X) (i j : Fin 3) : G q i j 0 = if i = j then 1 else 0 := hA0 q.val q.property i j
  have hGd (q : X) (i j : Fin 3) : fderiv ℝ (G q i j) 0 = 0 := hAd q.val q.property i j
  have hGc (i j : Fin 3) (k : ℕ) : Continuous (fun w : X × (Fin 3 → ℝ) =>
      iteratedFDeriv ℝ k (G w.1 i j) w.2) := by
    exact (continuous_parameter_iteratedFDeriv (fun w => A w i j)
      (contDiff_pi.mp (contDiff_pi.mp hA i) j) k).comp
      ((continuous_subtype_val.comp continuous_fst).prodMk continuous_snd)
  have hβc (j : Fin 3) (k : ℕ) : Continuous (fun w : X × (Fin 3 → ℝ) =>
      iteratedFDeriv ℝ k (β w.1 j) w.2) := by
    exact (continuous_parameter_iteratedFDeriv (fun w => b w j)
      (contDiff_pi.mp hb j) k).comp
      ((continuous_subtype_val.comp continuous_fst).prodMk continuous_snd)
  have hΦ (q : X) : ContDiff ℝ ∞ (Φ q) :=
    (contDiff_normalWaveProfile g hφ).comp (contDiff_const.prodMk contDiff_id)
  have hΦ0 : Continuous (fun q : X => Φ q 0) :=
    (contDiff_normalWaveProfile g hφ).continuous.comp
      (continuous_subtype_val.prodMk continuous_const)
  have hΦ2 : Continuous (fun w : X × PhaseSpace => iteratedFDeriv ℝ 2 (Φ w.1) w.2) :=
    continuous_normalWaveProfile_iteratedFDeriv g hφ K 2
  have ha : Continuous (fun q : X => gradient (Φ q) 0) :=
    continuous_gradient_of_iterated Φ (continuous_normalWaveProfile_iteratedFDeriv g hφ K 1)
  obtain ⟨κ,hκ,C,hC,B,hB,hsmall⟩ := compact_profile_canonical_smallBall_uniform_orders
    G β hG hβ hG0 hGd hGc hβc Φ hΦ hΦ0 hΦ2 ha
    (fun q => hnc q.val q.property) (fun q => hcrit q.val q.property)
  refine ⟨κ,hκ,C,hC,B,hB,?_⟩
  intro ζ hζ m D
  let F : X → (Fin 3 → ℝ) → ℂ := fun q x => (Φ q (normalWaveEquiv x) : ℂ)
  have hF (q : X) : ContDiff ℝ ∞ (F q) :=
    Complex.ofRealCLM.contDiff.comp ((hΦ q).comp normalWaveEquiv.contDiff)
  have hF0 (q : X) : F q 0 = (Φ q 0 : ℂ) := by simp [F]
  have hFc (k : ℕ) : Continuous (fun w : X × (Fin 3 → ℝ) => iteratedFDeriv ℝ k (F w.1) w.2) := by
    have hf : ContDiff ℝ ∞ (fun w : NormalWaveParameter × (Fin 3 → ℝ) =>
        (normalWaveProfile g φ w.1 (normalWaveEquiv w.2) : ℂ)) :=
      Complex.ofRealCLM.contDiff.comp ((contDiff_normalWaveProfile g hφ).comp
        (contDiff_fst.prodMk (normalWaveEquiv.contDiff.comp contDiff_snd)))
    exact (continuous_parameter_iteratedFDeriv _ hf k).comp
      ((continuous_subtype_val.comp continuous_fst).prodMk continuous_snd)
  obtain ⟨r₀,hr₀,C₀,hC₀,N,hN,hs⟩ := hsmall F hF hF0 hFc ζ hζ m D
  refine ⟨r₀,hr₀,C₀,hC₀,N,hN,?_⟩
  intro q hq n hn
  simpa only [normalFamilyWave,F,G,β,Φ,Complex.ofReal_re] using hs ⟨q,hq⟩ n hn

end YauCounterexamples

end

end OAI
