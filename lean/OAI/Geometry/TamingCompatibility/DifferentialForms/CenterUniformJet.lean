import Mathlib
import OAI.Geometry.TamingCompatibility.Functional.NormalizedJet
import OAI.Geometry.TamingCompatibility.Elliptic.MovingFrozenIdentity
import OAI.Geometry.TamingCompatibility.Functional.ParameterNormalizedJet

namespace OAI

section
section
section

section

noncomputable section
namespace TamingCompatibility.HilbertSobolev
open MeasureTheory TemperedDistribution EuclideanSobolevOperators Filter LineDeriv Set
open scoped SchwartzMap LineDeriv Topology ContDiff ENNReal
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
local instance : Fact ((1 : ENNReal) ≤ 4) := ⟨by norm_num⟩

omit [CompleteSpace F] in
lemma moving_local_scaled_frozen_equation
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (g : basisIndex E → basisIndex E → 𝓢(E,ℂ)) (p₀ p : E)
    (hgp : ∀ i j, g i j p₀ = if i=j then ((((2*Real.pi)^2)⁻¹ : ℝ) : ℂ) else 0)
    (b : ι → 𝓢(E,ℂ)) (L : ι → F →L[ℂ] F) (d : ι → E)
    (c : κ → 𝓢(E,ℂ)) (K : κ → F →L[ℂ] F)
    (ζ : 𝓢(E,ℂ)) (hζ : HasCompactSupport (ζ : E → ℂ))
    (r : ℝ) (hr : r ≠ 0) (ψ : 𝓢(E,ℂ)) (hψ : ∀ x ∈ tsupport ψ, ζ x = 1)
    (u f : 𝓢(E,F))
    (heq : smulLeftCLM F (affineSchwartz (-(r⁻¹ • p)) r⁻¹ (inv_ne_zero hr) ψ)
      (-directionalPrincipal (stdOrthonormalBasis ℝ E) g (u : 𝓢'(E,F)) +
        matrixLowerOrder b L d c K (u : 𝓢'(E,F))) =
      smulLeftCLM F (affineSchwartz (-(r⁻¹ • p)) r⁻¹ (inv_ne_zero hr) ψ) (f : 𝓢'(E,F))) :
    smulLeftCLM F ψ (perturbedHelmholtz
      (movingFrozenPrincipal ζ hζ (fun i j x => -g i j x) (fun i j => (g i j).smooth ⊤ |>.neg) p₀ (r,p))
        (rescaleSchwartz p r hr u : 𝓢'(E,F)) +
      matrixLowerOrder (fun i => scaledCoefficient 1 ζ hζ (b i) ((b i).smooth ⊤) p r) L d
        (Sum.elim (fun i => scaledCoefficient 2 ζ hζ (c i) ((c i).smooth ⊤) p r) (fun _ : Unit => -ζ))
        (Sum.elim K (fun _ : Unit => ContinuousLinearMap.id ℂ F))
        (rescaleSchwartz p r hr u : 𝓢'(E,F))) =
    smulLeftCLM F ψ (r^2 • (rescaleSchwartz p r hr f : 𝓢'(E,F))) := by
  rw [moving_local_frozen_system ζ hζ g p₀ p hgp r hr ψ hψ]
  rw [map_add, local_matrixLower_congr ψ _ (fun i => r • affineSchwartz p r hr (b i)) _
    (fun i => (r*r) • affineSchwartz p r hr (c i))
    (fun i y hy => by simpa only [pow_one] using scaledCoefficient_on_cutoff 1 ζ hζ (b i) p r hr y (hψ y hy))
    (fun i y hy => by simpa only [pow_two] using scaledCoefficient_on_cutoff 2 ζ hζ (c i) p r hr y (hψ y hy))]
  rw [← map_add]
  exact rescaled_local_schwartz_system p r hr (stdOrthonormalBasis ℝ E) g b L d c K u f ψ heq

theorem center_uniform_normalized_two_jet (hdim : Module.finrank ℝ E = 4)
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (g : basisIndex E → basisIndex E → 𝓢(E,ℂ)) (p₀ : E)
    (hgp : ∀ i j, g i j p₀ = if i=j then ((((2*Real.pi)^2)⁻¹ : ℝ) : ℂ) else 0)
    (b : ι → 𝓢(E,ℂ)) (L : ι → F →L[ℂ] F) (d : ι → E)
    (c : κ → 𝓢(E,ℂ)) (K : κ → F →L[ℂ] F)
    (ζ : 𝓢(E,ℂ)) (hζ : HasCompactSupport (ζ : E → ℂ))
    (χ : ℕ → 𝓢(E,ℂ))
    (hχ : ∀ n ≤ 3, ∀ x ∈ tsupport (χ (n+1)), χ n =ᶠ[𝓝 x] fun _ => 1)
    (hζχ : ∀ n ≤ 3, ∀ x ∈ tsupport (χ (n+1)), ζ x = 1)
    (R E₀ : ℝ) (hE : 0 ≤ E₀) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ t in 𝓝 (0,p₀), ∀ (hr : 0 < t.1), t.1 ≤ 1 →
      ∀ (u f : 𝓢(E,F)) (M : ℝ), 0 ≤ M →
      tsupport f ⊆ Metric.ball t.2 (t.1*R) →
      (∀ k ≤ 3, ∀ m : Fin k → E, (∀ i, ‖m i‖ ≤ 1) → ∀ x, ‖(∂^{m} f) x‖ ≤ M/t.1^k) →
      (‖u.toLp 4 (volume : Measure E)‖ + ∑ i,
        ‖(∂_{stdOrthonormalBasis ℝ E i} u).toLp 2 (volume : Measure E)‖ ≤ E₀*M*t.1^3) →
      (∀ n ≤ 3, smulLeftCLM F
        (affineSchwartz (-(t.1⁻¹ • t.2)) t.1⁻¹ (inv_ne_zero hr.ne') (χ (n+1)))
        (-directionalPrincipal (stdOrthonormalBasis ℝ E) g (u : 𝓢'(E,F)) +
          matrixLowerOrder b L d c K (u : 𝓢'(E,F))) =
        smulLeftCLM F (affineSchwartz (-(t.1⁻¹ • t.2)) t.1⁻¹ (inv_ne_zero hr.ne') (χ (n+1)))
          (f : 𝓢'(E,F))) →
      ∀ x : E, ((χ 4 : E → ℂ) =ᶠ[𝓝 x] fun _ => 1) →
        ‖u (t.1 • x+t.2)‖ + ∑ i, ‖(∂_{stdOrthonormalBasis ℝ E i} u) (t.1 • x+t.2)‖ +
          ∑ i, ∑ j, ‖(∂_{stdOrthonormalBasis ℝ E j} (∂_{stdOrthonormalBasis ℝ E i} u)) (t.1 • x+t.2)‖ ≤ C*M := by
  classical
  let a := movingFrozenPrincipal ζ hζ (fun i j x => -g i j x) (fun i j => (g i j).smooth ⊤ |>.neg) p₀
  let B := fun t : ℝ × E => fun i => scaledCoefficient 1 ζ hζ (b i) ((b i).smooth ⊤) t.2 t.1
  let D := fun t : ℝ × E => fun i => scaledCoefficient 2 ζ hζ (c i) ((c i).smooth ⊤) t.2 t.1
  let Cc := fun t => Sum.elim (D t) (fun _ : Unit => -ζ)
  let Ks := Sum.elim K (fun _ : Unit => ContinuousLinearMap.id ℂ F)
  have ha : ∀ n ≤ 3, Tendsto (fun t => ‖perturbation (F := F) n (a t)‖) (𝓝 (0,p₀)) (𝓝 0) :=
    fun n _ => moving_frozen_perturbation_norm_tendsto n ζ hζ _ _ p₀
  have hac : ∀ n ≤ 3, ∀ i j, ContinuousAt (fun t => coefficientSize n (a t i j)) (0,p₀) := by
    intro n _ i j
    exact (movingFrozenCoefficient_size_continuous n ζ hζ (fun x => -g i j x)
      ((g i j).smooth ⊤ |>.neg) p₀).continuousAt
  have hb : ∀ n ≤ 3, ∀ i, ContinuousAt (fun t => coefficientSize n (B t i)) (0,p₀) :=
    fun n _ i => (moving_scaledCoefficient_size_continuous n 1 ζ hζ (b i) ((b i).smooth ⊤)).continuousAt
  have hc : ∀ n ≤ 3, ∀ i, ContinuousAt (fun t => coefficientSize n (Cc t i)) (0,p₀) := by
    intro n _ i
    cases i with
    | inl i => exact (moving_scaledCoefficient_size_continuous n 2 ζ hζ (c i) ((c i).smooth ⊤)).continuousAt
    | inr i => exact continuousAt_const
  obtain ⟨A,hA,hest⟩ := parameter_normalized_two_jet (0,p₀) hdim a ha hac B L d Cc Ks hb hc χ hχ R E₀ hE
  refine ⟨A,hA,?_⟩
  filter_upwards [hest] with t hh
  intro hr hr1 u f M hM hs hf he heq x hx
  apply hh t.1 hr hr1 t.2 u f M hM hs hf he (fun n hn => ?_) x hx
  exact moving_local_scaled_frozen_equation g p₀ t.2 hgp b L d c K ζ hζ t.1 hr.ne'
    (χ (n+1)) (hζχ n hn) u f (heq n hn)

end TamingCompatibility.HilbertSobolev

end
end

end
end
end

end OAI
