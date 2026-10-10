import Mathlib
import OAI.Geometry.SmoothYau.Estimates.VaryingPatchCoefficients
import OAI.Geometry.SmoothYau.Estimates.CoefficientPerturbationTendsto
import OAI.Geometry.SmoothYau.Smoothness.ChartDerivativeNeZeroTransfer
import OAI.Geometry.SmoothYau.Smoothness.ChartTensorCoordLocal1
import OAI.Geometry.SmoothYau.Smoothness.JointMetricDet

namespace OAI

noncomputable section
open Set Filter Function Manifold
open scoped Topology ContDiff SchwartzMap
namespace YauCounterexamples
namespace ContinuousSmoothFamilyOn
variable {P E : Type*} [TopologicalSpace P]
  [NormedAddCommGroup E] [NormedSpace ℝ E] {U : Set E}
lemma complex_mul {f g : P → E → ℂ} (hf : ContinuousSmoothFamilyOn f U)
    (hg : ContinuousSmoothFamilyOn g U) : ContinuousSmoothFamilyOn (fun p x => f p x*g p x) U :=
  (hf.prodMk hg).postcomp (fun z : ℂ × ℂ => z.1*z.2) (fun _ _ _ => by fun_prop)
lemma cutoff_complex (χ : E → ℂ) (hχ : ContDiff ℝ ∞ χ)
    {f : P → E → ℂ} (hU : IsOpen U) (hs : tsupport χ ⊆ U)
    (hf : ContinuousSmoothFamilyOn f U) :
    ContinuousSmoothFamilyOn (fun p x => χ x*f p x) univ := by
  apply of_local
  intro x hx
  by_cases hxs : x ∈ tsupport χ
  · exact ⟨U,hU,hs hxs,(const χ (fun y _ => hχ.contDiffAt)).complex_mul hf⟩
  · refine ⟨(tsupport χ)ᶜ,(isClosed_tsupport χ).isOpen_compl,hxs,?_⟩
    apply (scalar_const (fun _ : P => (0:ℂ)) continuous_const).congr (isClosed_tsupport χ).isOpen_compl
    intro p y hy
    simp only [image_eq_zero_of_notMem_tsupport hy,zero_mul]
end ContinuousSmoothFamilyOn
variable {P E M : Type*} [TopologicalSpace P]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
  [CompactSpace M] [T2Space M]
  {g : SmoothMetric E M} {k : ℕ} {hs : Module.finrank ℝ E < 2*(2*(k:ℝ))}
namespace CompactMetricAtlas
variable (A : CompactMetricAtlas g k hs)

omit [T2Space M] in
theorem continuousFamily_varyingLaplacian_tendsto (q : P → SmoothMetric E M)
    (hq : ∀ i j l, ContinuousSmoothFamilyOn
      (fun t y => metricCoefficients (q t) (A.p i) y j l) (chartAt E (A.p i)).target)
    (C : ∀ t i, A.VaryingPatchCoefficients (q t) i) (p₀ : P) :
    Tendsto (fun t => A.varyingLaplacianCLM (q t) (C t)) (𝓝 p₀)
      (𝓝 (A.varyingLaplacianCLM (q p₀) (C p₀))) := by
  apply A.varyingLaplacianCLM_tendsto q (q p₀) C (C p₀)
  · intro i j l
    apply (schwartzToSobolev (2*(k:ℝ))).continuous.tendsto _ |>.comp
    apply Continuous.tendsto
    apply continuous_schwartz_common_support _ ?_ (tsupport (A.χcoord i)) (A.compact_χcoord i)
      (fun t => A.metricCoefficientSchwartz_common_support i _ _)
    intro n
    have he (t : P) : (A.metricCoefficientSchwartz i ((C t i).a j l) ((C t i).smooth_a j l) : E → ℂ) =
        fun y => A.χcoord i y * ((metricCoefficients (q t) (A.p i) y)⁻¹ j l : ℂ) :=
      funext (A.varyingCoefficientSchwartz_a_value (q t) i (C t i) j l)
    simp_rw [he]
    have hf := ((family_metricInverse q (A.p i) (hq i) j l).postcomp
      (fun x : ℝ => (x:ℂ)) (fun _ _ _ => Complex.ofRealCLM.contDiff.contDiffAt)).cutoff_complex
      (A.χcoord i) (A.smooth_χcoord i) (chartAt E (A.p i)).open_target (A.χcoord_target i)
    exact continuousOn_univ.mp (by simpa only [univ_prod_univ] using hf.jets n)
  · intro i j
    apply (schwartzToSobolev (2*(k:ℝ))).continuous.tendsto _ |>.comp
    apply Continuous.tendsto
    apply continuous_schwartz_common_support _ ?_ (tsupport (A.χcoord i)) (A.compact_χcoord i)
      (fun t => A.metricCoefficientSchwartz_common_support i _ _)
    intro n
    have he (t : P) : (A.metricCoefficientSchwartz i ((C t i).c j) ((C t i).smooth_c j) : E → ℂ) =
        fun y => A.χcoord i y * (metricFirstCoefficient (q t) (A.p i) j y : ℂ) :=
      funext (A.varyingCoefficientSchwartz_c_value (q t) i (C t i) j)
    simp_rw [he]
    have hf := ((family_metricFirstCoefficient q (A.p i) (hq i) j).postcomp
      (fun x : ℝ => (x:ℂ)) (fun _ _ _ => Complex.ofRealCLM.contDiff.contDiffAt)).cutoff_complex
      (A.χcoord i) (A.smooth_χcoord i) (chartAt E (A.p i)).open_target (A.χcoord_target i)
    exact continuousOn_univ.mp (by simpa only [univ_prod_univ] using hf.jets n)
end CompactMetricAtlas
end YauCounterexamples
end

end OAI
