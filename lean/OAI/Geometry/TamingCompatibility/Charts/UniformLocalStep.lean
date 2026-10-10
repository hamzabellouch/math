import Mathlib
import OAI.Geometry.TamingCompatibility.Charts.QuantitativeLocalStep
import OAI.Geometry.TamingCompatibility.DifferentialForms.UniformInterior

namespace OAI


noncomputable section
namespace TamingCompatibility.HilbertSobolev
open MeasureTheory TemperedDistribution EuclideanSobolevOperators Filter
open scoped SchwartzMap LineDeriv Topology ContDiff
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

theorem uniform_local_step {ι κ : Type*} [Fintype ι] [Fintype κ]
    (n : ℕ) (a : ℝ → basisIndex E → basisIndex E → 𝓢(E,ℂ))
    (ha : Tendsto (fun r => ‖perturbation (F := F) n (a r)‖) (𝓝 0) (𝓝 0))
    (hac : ∀ i j, ContinuousAt (fun r => coefficientSize n (a r i j)) 0)
    (b : ℝ → ι → 𝓢(E,ℂ)) (L : ι → F →L[ℂ] F) (d : ι → E)
    (c : ℝ → κ → 𝓢(E,ℂ)) (K : κ → F →L[ℂ] F)
    (hb : ∀ i, ContinuousAt (fun r => coefficientSize n (b r i)) 0)
    (hc : ∀ i, ContinuousAt (fun r => coefficientSize n (c r i)) 0)
    (χ η : 𝓢(E,ℂ)) (hη : ∀ x ∈ tsupport χ, η =ᶠ[𝓝 x] fun _ => 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ r in 𝓝 (0:ℝ),
      ∀ (u : 𝓢'(E,F)) (f : H E F n) (v : H E F ((n:ℝ)+2)) (w : H E F ((n:ℝ)+1)),
      toDistribution E F ((n:ℝ)+2) v = smulLeftCLM F χ u →
      toDistribution E F ((n:ℝ)+1) w = smulLeftCLM F η u →
      smulLeftCLM F χ (perturbedHelmholtz (a r) u + matrixLowerOrder (b r) L d (c r) K u) =
        smulLeftCLM F χ (toDistribution E F n f) →
      ‖v‖ ≤ C * (‖f‖ + ‖w‖) := by
  obtain ⟨B,hB,hboundB⟩ := matrixLowerH_eventually_bounded n b L d c K hb hc
  obtain ⟨D,hD,hboundD⟩ := localizationErrorH_eventually_bounded (F := F) n a χ hac
  let P := ‖product (F := F) n χ‖
  have hP : 0 ≤ P := norm_nonneg _
  refine ⟨2*(P+P*B+D+1),by positivity,?_⟩
  have hhalf : ∀ᶠ r in 𝓝 (0:ℝ), ‖perturbation (F := F) n (a r)‖ < 1/2 :=
    ha.eventually (gt_mem_nhds (by norm_num))
  filter_upwards [hhalf,hboundB,hboundD] with r hr hrB hrD
  intro u f v w hv hw heq
  have h := small_principal_local_step n (a r) hr.le (b r) L d (c r) K χ η hη
    u f v w hv hw heq
  apply h.trans
  change 2*(P*‖f‖+(P*‖matrixLowerH n (b r) L d (c r) K‖+
    ‖localizationErrorH (F := F) n (a r) χ‖)*‖w‖) ≤ _
  calc
    _ ≤ 2*(P*‖f‖+(P*B+D)*‖w‖) := by gcongr
    _ ≤ 2*(P+P*B+D+1)*(‖f‖+‖w‖) := by
      have hpb : 0 ≤ P*B := mul_nonneg hP hB.le
      nlinarith [norm_nonneg f,norm_nonneg w,mul_nonneg (by positivity : 0 ≤ P*B+D+1)
        (norm_nonneg f),mul_nonneg (by positivity : 0 ≤ P+1) (norm_nonneg w)]
end TamingCompatibility.HilbertSobolev

end

end OAI
