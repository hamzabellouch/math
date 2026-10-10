import Mathlib
import OAI.Geometry.TamingCompatibility.Elliptic.CriticalRescaleH1
import OAI.Geometry.TamingCompatibility.DifferentialForms.ParameterInterior

namespace OAI

section
section
section

section

noncomputable section
namespace TamingCompatibility.HilbertSobolev
open MeasureTheory TemperedDistribution EuclideanSobolevOperators Filter
open scoped SchwartzMap LineDeriv Topology ContDiff ENNReal
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
variable {P : Type*} [TopologicalSpace P]
local instance : Fact ((1 : ENNReal) ≤ 4) := ⟨by norm_num⟩

theorem parameter_scaled_two_jet (p₀ : P) (hdim : Module.finrank ℝ E = 4)
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (a : P → basisIndex E → basisIndex E → 𝓢(E,ℂ))
    (ha : ∀ n ≤ 3, Tendsto (fun t => ‖perturbation (F := F) n (a t)‖) (𝓝 p₀) (𝓝 0))
    (hac : ∀ n ≤ 3, ∀ i j, ContinuousAt (fun r => coefficientSize n (a r i j)) p₀)
    (b : P → ι → 𝓢(E,ℂ)) (L : ι → F →L[ℂ] F) (d : ι → E)
    (c : P → κ → 𝓢(E,ℂ)) (K : κ → F →L[ℂ] F)
    (hb : ∀ n ≤ 3, ∀ i, ContinuousAt (fun r => coefficientSize n (b r i)) p₀)
    (hc : ∀ n ≤ 3, ∀ i, ContinuousAt (fun r => coefficientSize n (c r i)) p₀)
    (χ : ℕ → 𝓢(E,ℂ))
    (hχ : ∀ n ≤ 3, ∀ x ∈ tsupport (χ (n+1)), χ n =ᶠ[𝓝 x] fun _ => 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ t in 𝓝 p₀, ∀ (r : ℝ) (hr : 0 < r) (p : E)
      (u : 𝓢(E,F)) (f : H E F 3),
      (∀ n ≤ 3, smulLeftCLM F (χ (n+1))
        (perturbedHelmholtz (a t) (rescaleSchwartz p r hr.ne' u : 𝓢'(E,F)) +
          matrixLowerOrder (b t) L d (c t) K (rescaleSchwartz p r hr.ne' u : 𝓢'(E,F))) =
        smulLeftCLM F (χ (n+1)) (toDistribution E F 3 f)) →
      ∀ x : E, let w := SchwartzMap.smulLeftCLM F (χ 4) (rescaleSchwartz p r hr.ne' u)
        ‖w x‖ + ∑ i, ‖(∂_{stdOrthonormalBasis ℝ E i} w) x‖ +
          ∑ i, ∑ j, ‖(∂_{stdOrthonormalBasis ℝ E j} (∂_{stdOrthonormalBasis ℝ E i} w)) x‖ ≤
        C * (‖f‖ + r⁻¹ * (‖u.toLp 4 (volume : Measure E)‖ +
          ∑ i, ‖(∂_{stdOrthonormalBasis ℝ E i} u).toLp 2 (volume : Measure E)‖)) := by
  classical
  obtain ⟨B,hB,hbound⟩ := parameter_uniform_finite_bootstrap p₀ 3 a ha hac b L d c K hb hc χ hχ
  obtain ⟨T,hT,hscale⟩ := cutoff_rescale_H1 (F := F) hdim (χ 0)
  obtain ⟨J,hJ,hjet⟩ := schwartz_two_jet_bound (F := F) (stdOrthonormalBasis ℝ E) 5
    (by rw [hdim]; norm_num)
  refine ⟨J*B*(1+T),by positivity,?_⟩
  filter_upwards [hbound] with t hrbound
  intro r hr p u f heq x
  let v := fun n : ℕ => schwartzToH ((n:ℝ)+1)
    (SchwartzMap.smulLeftCLM F (χ n) (rescaleSchwartz p r hr.ne' u))
  have hv (n : ℕ) (_hn : n ≤ 3+1) : toDistribution E F ((n:ℝ)+1) (v n) =
      smulLeftCLM F (χ n) (rescaleSchwartz p r hr.ne' u : 𝓢'(E,F)) := by
    dsimp only [v]
    rw [schwartzToH_spec,ComplexMatrix.product_schwartz]
  have h := hrbound (rescaleSchwartz p r hr.ne' u : 𝓢'(E,F)) f v hv heq
  let S := ‖u.toLp 4 (volume : Measure E)‖ +
    ∑ i, ‖(∂_{stdOrthonormalBasis ℝ E i} u).toLp 2 (volume : Measure E)‖
  have hS : 0 ≤ S := add_nonneg (norm_nonneg _) (Finset.sum_nonneg (fun _ _ => norm_nonneg _))
  have hv0 : ‖v 0‖ ≤ T*r⁻¹*S := by
    have he : ((0:ℕ):ℝ)+1 = 1 := by norm_num
    dsimp only [v]
    rw [he]
    exact hscale p r hr u
  have hv4 : schwartzToH 5 (SchwartzMap.smulLeftCLM F (χ 4) (rescaleSchwartz p r hr.ne' u)) = v 4 := by
    have he : ((4:ℕ):ℝ)+1 = 5 := by norm_num
    dsimp only [v]
    rw [he]
  change _ ≤ J*B*(1+T) * (‖f‖ + r⁻¹*S)
  apply (hjet (SchwartzMap.smulLeftCLM F (χ 4) (rescaleSchwartz p r hr.ne' u)) x).trans
  rw [hv4]
  calc
    J*‖v 4‖ ≤ J*(B*(‖f‖+‖v 0‖)) := mul_le_mul_of_nonneg_left h hJ
    _ ≤ J*(B*(‖f‖+T*r⁻¹*S)) := by gcongr
    _ ≤ J*B*(1+T)*(‖f‖+r⁻¹*S) := by
      have h₀ : 0 ≤ T*‖f‖ := mul_nonneg hT (norm_nonneg f)
      have h₁ : 0 ≤ r⁻¹*S := mul_nonneg (inv_nonneg.mpr hr.le) hS
      nlinarith [mul_nonneg (mul_nonneg hJ hB.le) (add_nonneg h₀ h₁)]
end TamingCompatibility.HilbertSobolev

end
end

end
end
end

end OAI
