import Mathlib
import OAI.Geometry.SmoothYau.Spectrum.ProductFrequencyTop
import OAI.Geometry.SmoothYau.Estimates.EventualProductScalarCorrectionRate
import OAI.Geometry.SmoothYau.Smoothness.EventuallyPositiveFactorEventualJets

namespace OAI

noncomputable section
namespace YauCounterexamples
section
open Set Filter Function
open scoped Topology ContDiff Manifold SchwartzMap
open Set Filter Manifold Bundle MeasureTheory NNReal
open scoped Topology ContDiff ENNReal
open Set Filter Topology NNReal
open Set Filter Module
open scoped Topology
open Set Filter Manifold Bundle MeasureTheory
open scoped Topology ContDiff ENNReal
open Set Filter
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff Manifold
open Set Filter Function
open scoped Topology ContDiff Manifold Matrix
open Set Filter Function
open scoped Topology ContDiff Manifold Matrix
open Set Filter Function
open scoped Topology ContDiff Manifold Matrix
open Set Filter
open scoped Topology
open Set Filter Function MeasureTheory FourierTransform TemperedDistribution
open scoped Topology SchwartzMap ENNReal Real Laplacian BoundedContinuousFunction
open Set Filter Function
open scoped Topology ContDiff Manifold
open scoped Topology ContDiff Manifold
variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ,E) ∞ M]

theorem conformal_exactification_with_scale {b s U v : M → ℝ}
    (hd : Module.finrank ℝ E=3)
    (hb : ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,ℝ) ∞ b)
    (hU : ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,ℝ) ∞ U)
    (hv : ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,ℝ) ∞ v) (g : SmoothMetric E M)
    {Λ : ℝ} (hΛ : Λ ≠ 0) (hb0 : ∀ x, 0 < b x) (hv0 : ∀ x, 0 < v x)
    (hw : ∀ x, weightedLaplacian g b U x+Λ*s x*U x=0)
    (hfactor : ∀ x, weightedLaplacian g b v x=Λ*b x^3*v x^5-Λ*s x*v x) :
    ∃ ĝ : SmoothMetric E M, ∃ u : M → ℝ,
      ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,ℝ) ∞ u ∧
      (∀ x, -laplaceBeltrami ĝ u x=Λ*u x) ∧
      (∀ x, u x=U x/v x) ∧ (∀ x, u x=0 ↔ U x=0) ∧
      (∀ x, ĝ.inner x=(b x*v x^2)^2 • g.inner x) := by
  let q := fun x => b x*v x^2
  have hq : ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,ℝ) ∞ q := hb.mul (hv.pow 2)
  have hq0 : ∀ x, 0 < q x := fun x => mul_pos (hb0 x) (sq_pos_of_pos (hv0 x))
  let u := fun x => U x/v x
  refine ⟨conformalMetric g q hq hq0,u,hU.div₀ hv (fun x => (hv0 x).ne'),?_,
    fun _ => rfl,?_,fun _ => rfl⟩
  · intro x
    have he := intrinsic_conjugated_equation hb hU hv g hΛ (fun x => (hv0 x).ne') hw x
    rw [hfactor x] at he
    rw [conformalMetric_laplacian_three hd]
    dsimp only [q,u] at he ⊢
    have hbn := (hb0 x).ne'
    have hvn := (hv0 x).ne'
    field_simp at he ⊢
    nlinarith [he]
  · intro x
    change U x/v x=0 ↔ U x=0
    simp [(hv0 x).ne']

end

open Set Filter Function
open scoped Topology ContDiff Manifold SchwartzMap
open Set Filter Manifold Bundle MeasureTheory NNReal
open scoped Topology ContDiff ENNReal
open Set Filter Topology NNReal
open Set Filter Module
open scoped Topology
open Set Filter Manifold Bundle MeasureTheory
open scoped Topology ContDiff ENNReal
open Set Filter
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff Manifold
open Set Filter Function
open scoped Topology ContDiff Manifold Matrix
open Set Filter Function
open scoped Topology ContDiff Manifold Matrix
open Set Filter Function
open scoped Topology ContDiff Manifold Matrix
open Set Filter
open scoped Topology
open Set Filter Function MeasureTheory FourierTransform TemperedDistribution
open scoped Topology SchwartzMap ENNReal Real Laplacian BoundedContinuousFunction
open Set Filter Function
open scoped Topology ContDiff Manifold
open Filter
open scoped Topology ContDiff Manifold
variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
  [T2Space M] [CompactSpace M] [Nonempty M]
namespace CompactMetricAtlas
variable {g : SmoothMetric E M} {k : ℕ} {hs : Module.finrank ℝ E < 2*(2*(k:ℝ))}
variable (A : CompactMetricAtlas g k hs)

theorem eventually_quantitative_conformal_exactification
    (hd : Module.finrank ℝ E=3) (N P B D : ℕ)
    (hN : Module.finrank ℝ E < 2*(2*((k+1:ℕ):ℝ)-N))
    (hD : (P+8)+((2*B+21)*(2*(k+1)+2)+10)+2 ≤ D)
    {C : ℝ} (hC : 0 < C) (U W : ℕ → M → ℝ)
    (hU : ∀ n, ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,ℝ) ∞ (U n))
    (hW : ∀ n x, 0 < W n x)
    (hdata : ∀ᶠ n : ℕ in atTop,
      (∀ x, W n x/(n:ℝ)^B ≤ |U n x|+
        Real.sqrt (coordinateGradientPair g (U n) (U n) x)/(n:ℝ)) ∧
      (∀ i : A.t, ∀ y ∈ A.scalarChartSupport i, ∀ j ≤ 2*(k+1)+2,
        ‖iteratedFDeriv ℝ j (U n ∘ (chartAt E (A.p i)).symm) y‖ ≤
          C*(n:ℝ)^(j+4)*W n ((chartAt E (A.p i)).symm y)) ∧
      (∀ i : A.t, ∀ y ∈ A.scalarChartSupport i, ∀ j ≤ 2*(k+1)+1,
        ‖iteratedFDeriv ℝ j
          ((fun x => laplaceBeltrami g (U n) x+sphereFrequency n*U n x) ∘
            (chartAt E (A.p i)).symm) y‖ ≤
          C*(n:ℝ)^4/(n:ℝ)^D*W n ((chartAt E (A.p i)).symm y))) :
    ∀ᶠ n : ℕ in atTop, ∃ v : M → ℝ, ∃ ĝ : SmoothMetric E M, ∃ u : M → ℝ,
      ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,ℝ) ∞ v ∧ (∀ x, 0 < v x) ∧
      A.ChartJetBound N (fun x => ((v x-1:ℝ):ℂ)) (inverseFrequency n^P) ∧
      ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,ℝ) ∞ u ∧ u ≠ 0 ∧ 0 < sphereFrequency n ∧
      (∀ x, -laplaceBeltrami ĝ u x=sphereFrequency n*u x) ∧
      (∀ x, u x=U n x/v x) ∧ (∀ x, u x=0 ↔ U n x=0) ∧
      (∀ x, ĝ.inner x=(intrinsicCorrectionB g (n:ℝ) (sphereFrequency n) (U n) x*v x^2)^2 •
        g.inner x) := by
  classical
  let b := fun n : ℕ => intrinsicCorrectionB g (n:ℝ) (sphereFrequency n) (U n)
  let s := fun n : ℕ => intrinsicCorrectionS g (n:ℝ) (sphereFrequency n) (U n)
  let Coeff : ∀ i, A.PatchCoefficients i := fun i => (A.nonempty_patchCoefficients i).some
  have hscalar := A.eventually_scalar_exactification (2*(k+1)) B (P+8) D (by omega) hD
    hC U W hU hW hdata
  have hsm : ∀ᶠ n : ℕ in atTop,
      ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,ℝ) ∞ (b n) ∧ ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,ℝ) ∞ (s n) :=
    hscalar.mono (fun n hn => ⟨hn.1,hn.2.1⟩)
  have hj : ∀ᶠ n : ℕ in atTop,
      A.ChartJetBound (2*(k+1)) (fun x => ((b n x-1:ℝ):ℂ)) (inverseFrequency n^(P+8)) ∧
      A.ChartJetBound (2*(k+1)) (fun x => ((s n x-1:ℝ):ℂ)) (inverseFrequency n^(P+8)) :=
    hscalar.mono (fun n hn => ⟨hn.2.2.2.2.1,hn.2.2.2.2.2.1⟩)
  have hfactor := A.eventually_positive_factor_of_eventual_jets hd Coeff N P hN b s hsm hj
  filter_upwards [hscalar,hfactor,hdata,eventually_ge_atTop 1] with n hsc hv hn hn1
  obtain ⟨v,hv,hvpos,hveq,hvj⟩ := hv
  have hn0 : 0 < (n:ℝ) := by exact_mod_cast (show 0 < n by omega)
  have hΛ : 0 < sphereFrequency n := by unfold sphereFrequency; positivity
  obtain ⟨ĝ,u,hu,hueq,huv,hzeros,hmetric⟩ := conformal_exactification_with_scale
    hd hsc.1 (hU n) hv g hΛ.ne' (fun x => (hsc.2.2.1 x).1) hvpos hsc.2.2.2.1 hveq
  have hUn : U n ≠ 0 := by
    intro hz
    let x : M := Classical.arbitrary M
    have hjx := hn.1 x
    rw [hz] at hjx
    have hg0 : coordinateGradientPair g (0 : M → ℝ) 0 x=0 := by
      simp [coordinateGradientPair,Function.comp_def]
    simp only [Pi.zero_apply,abs_zero,hg0,Real.sqrt_zero,zero_div,zero_add] at hjx
    exact (not_le_of_gt (div_pos (hW n x) (pow_pos hn0 B))) hjx
  have hun : u ≠ 0 := by
    intro hz
    apply hUn
    funext x
    exact (hzeros x).mp (by rw [hz]; rfl)
  exact ⟨v,ĝ,u,hv,hvpos,hvj,hu,hun,hΛ,hueq,huv,hzeros,hmetric⟩
end CompactMetricAtlas


end YauCounterexamples
end

end OAI
