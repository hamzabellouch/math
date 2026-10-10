import Mathlib
import OAI.Geometry.TamingCompatibility.DifferentialForms.ParameterEnergyJet
import OAI.Geometry.TamingCompatibility.Currents.LinearLocalDensity

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

theorem linear_center_energy_two_jet (hdim : Module.finrank ℝ E = 4)
    {ι κ τ : Type*} [Fintype ι] [Fintype κ] [Fintype τ]
    (d : ι → E) (g : ι → ι → 𝓢(E,ℂ)) (p₀ : E) (A : E ≃L[ℝ] E)
    (hgp : ∀ i j, principalInBasis (stdOrthonormalBasis ℝ E) (fun i => A (d i))
      (fun i j => SchwartzMap.compCLMOfContinuousLinearEquiv ℂ A.symm (g i j)) i j (A p₀) =
        if i=j then ((((2*Real.pi)^2)⁻¹ : ℝ) : ℂ) else 0)
    (b : κ → 𝓢(E,ℂ)) (L : κ → F →L[ℂ] F) (v : κ → E)
    (c : τ → 𝓢(E,ℂ)) (K : τ → F →L[ℂ] F)
    (ζ : 𝓢(E,ℂ)) (hζ : HasCompactSupport (ζ : E → ℂ))
    (χ : ℕ → 𝓢(E,ℂ))
    (hχ : ∀ n ≤ 3, ∀ x ∈ tsupport (χ (n+1)), χ n =ᶠ[𝓝 x] fun _ => 1)
    (hζχ : ∀ n ≤ 3, ∀ x ∈ tsupport (χ (n+1)), ζ x = 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ t in 𝓝 (0,p₀), ∀ (hr : 0 < t.1),
      ∀ (u f : 𝓢(E,F)) (M : ℝ), 0 ≤ M →
      (∀ k ≤ 3, ∀ m : Fin k → E, (∀ i, ‖m i‖ ≤ 1) → ∀ x,
        ‖(∂^{m} (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ A.symm f)) x‖ ≤ M/t.1^k) →
      (∀ n ≤ 3, smulLeftCLM F
        (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ A
          (affineSchwartz (-(t.1⁻¹ • A t.2)) t.1⁻¹ (inv_ne_zero hr.ne') (χ (n+1))))
        (-directionalPrincipal d g (u : 𝓢'(E,F)) + matrixLowerOrder b L v c K (u : 𝓢'(E,F))) =
        smulLeftCLM F (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ A
          (affineSchwartz (-(t.1⁻¹ • A t.2)) t.1⁻¹ (inv_ne_zero hr.ne') (χ (n+1))))
          (f : 𝓢'(E,F))) →
      let U := SchwartzMap.compCLMOfContinuousLinearEquiv ℂ A.symm u
      ∀ x : E, ((χ 4 : E → ℂ) =ᶠ[𝓝 x] fun _ => 1) →
        t.1*‖U (t.1 • x+A t.2)‖ + t.1^2*∑ i, ‖(∂_{stdOrthonormalBasis ℝ E i} U) (t.1 • x+A t.2)‖ +
          t.1^3*∑ i, ∑ j, ‖(∂_{stdOrthonormalBasis ℝ E j} (∂_{stdOrthonormalBasis ℝ E i} U)) (t.1 • x+A t.2)‖ ≤
        C*(M*t.1^3 + ‖U.toLp 4 (volume : Measure E)‖ +
          ∑ i, ‖(∂_{stdOrthonormalBasis ℝ E i} U).toLp 2 (volume : Measure E)‖) := by
  let G := principalInBasis (stdOrthonormalBasis ℝ E) (fun i => A (d i))
    (fun i j => SchwartzMap.compCLMOfContinuousLinearEquiv ℂ A.symm (g i j))
  let B := fun i => SchwartzMap.compCLMOfContinuousLinearEquiv ℂ A.symm (b i)
  let Cc := fun i => SchwartzMap.compCLMOfContinuousLinearEquiv ℂ A.symm (c i)
  obtain ⟨C,hC,hest⟩ := center_uniform_energy_two_jet hdim G (A p₀) hgp B L (fun i => A (v i)) Cc K
    ζ hζ χ hχ hζχ
  have ht : Tendsto (fun t : ℝ × E => (t.1,A t.2)) (𝓝 (0,p₀)) (𝓝 (0,A p₀)) :=
    (continuous_fst.prodMk (A.continuous.comp continuous_snd)).continuousAt
  refine ⟨C,hC,?_⟩
  filter_upwards [ht.eventually hest] with t hh
  intro hr u f M hM hf heq
  apply hh hr (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ A.symm u)
    (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ A.symm f) M hM hf
  intro n hn
  have he := linear_local_schwartz_system A d g b L v c K u f
    (affineSchwartz (-(t.1⁻¹ • A t.2)) t.1⁻¹ (inv_ne_zero hr.ne') (χ (n+1))) (heq n hn)
  rw [directionalPrincipal_basis (stdOrthonormalBasis ℝ E)] at he
  exact he
end TamingCompatibility.HilbertSobolev

end
end

section
noncomputable section
namespace TamingCompatibility.ComplexMatrix
open HilbertSobolev EuclideanSobolevOperators TemperedDistribution MeasureTheory LineDeriv
open LocalMatrixOperator EuclideanEnergy Set Filter
open scoped SchwartzMap LineDeriv Topology ContDiff ENNReal
variable {m : ℕ}
local instance : Fact ((1 : ENNReal) ≤ 4) := ⟨by norm_num⟩

theorem metric_square_center_energy_two_jet
    (p₀ : V) (metric : MetricModel.Metric V) (frame : Fin 4 → V)
    (hframe : ∀ i j, metric.bilinear (frame i) (frame j) = if i=j then 1 else 0)
    (a : Fin 4 → 𝓢(V,R 2 →L[ℝ] R m)) (b : 𝓢(V,R 2 →L[ℝ] R m))
    (ρ : 𝓢(V,ℝ)) (g : Fin 4 → Fin 4 → V → ℝ)
    (ha : ∀ i j x, (ρ x • a i x).adjoint ∘L a j x + (ρ x • a j x).adjoint ∘L a i x =
      (2*g i j x) • ContinuousLinearMap.id ℝ (R 2))
    (c : ℝ) (hc : 0 < c)
    (hgp : ∀ i j, g i j p₀ = c * ∑ t, frame t i * frame t j)
    (ζ : 𝓢(V,ℂ)) (hζ : HasCompactSupport (ζ : V → ℂ))
    (χ : ℕ → 𝓢(V,ℂ))
    (hχ : ∀ n ≤ 3, ∀ x ∈ tsupport (χ (n+1)), χ n =ᶠ[𝓝 x] fun _ => 1)
    (hζχ : ∀ n ≤ 3, ∀ x ∈ tsupport (χ (n+1)), ζ x = 1) :
    ∃ A : V ≃L[ℝ] V, ∃ C₀ : ℝ, 0 ≤ C₀ ∧ ∀ᶠ t in 𝓝 (0,p₀), ∀ (hr : 0 < t.1),
      ∀ (u f : 𝓢(V,C 2)) (M : ℝ), 0 ≤ M →
      (∀ k ≤ 3, ∀ q : Fin k → V, (∀ i, ‖q i‖ ≤ 1) → ∀ x,
        ‖(∂^{q} (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ A.symm f)) x‖ ≤ M/t.1^k) →
      (∀ n ≤ 3, smulLeftCLM (C 2)
        (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ A
          (affineSchwartz (-(t.1⁻¹ • A t.2)) t.1⁻¹ (inv_ne_zero hr.ne') (χ (n+1))))
        (square e a b ρ (u : 𝓢'(V,C 2))) =
        smulLeftCLM (C 2) (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ A
          (affineSchwartz (-(t.1⁻¹ • A t.2)) t.1⁻¹ (inv_ne_zero hr.ne') (χ (n+1))))
          (f : 𝓢'(V,C 2))) →
      let U := SchwartzMap.compCLMOfContinuousLinearEquiv ℂ A.symm u
      ∀ x : V, ((χ 4 : V → ℂ) =ᶠ[𝓝 x] fun _ => 1) →
        t.1*‖U (t.1 • x+A t.2)‖ + t.1^2*∑ i, ‖(∂_{stdOrthonormalBasis ℝ V i} U) (t.1 • x+A t.2)‖ +
          t.1^3*∑ i, ∑ j, ‖(∂_{stdOrthonormalBasis ℝ V j} (∂_{stdOrthonormalBasis ℝ V i} U)) (t.1 • x+A t.2)‖ ≤
        C₀*(M*t.1^3 + ‖U.toLp 4 (volume : Measure V)‖ +
          ∑ i, ‖(∂_{stdOrthonormalBasis ℝ V i} U).toLp 2 (volume : Measure V)‖) := by
  let G := principalScalar a ρ
  have hg : ∀ i j, G i j p₀ = (c * ∑ t, frame t i * frame t j : ℝ) := by
    intro i j
    rw [principalScalar_apply a ρ g ha,hgp]
  obtain ⟨A,hA⟩ := exists_principal_normalization metric frame hframe c ((2*Real.pi)^2)⁻¹ hc
    (by positivity) G p₀ hg
  let B := squareFirst e (fun i => coefficient (a i)) (coefficient b)
    (fun i => weightedAdj ρ (a i)) (weightedAdj ρ b)
  let Cc := squareZero e (coefficient b) (fun i => weightedAdj ρ (a i)) (weightedAdj ρ b)
  obtain ⟨C₀,hC,hest⟩ := linear_center_energy_two_jet (F := C 2) (by norm_num [V]) e G p₀ A hA
    (fun q : Fin 4 × Fin 2 × Fin 2 => B q.1 q.2.1 q.2.2)
    (fun q => unit 2 2 q.2.1 q.2.2) (fun q => e q.1)
    (fun q : Fin 2 × Fin 2 => Cc q.1 q.2) (fun q => unit 2 2 q.1 q.2) ζ hζ χ hχ hζχ
  refine ⟨A,C₀,hC,?_⟩
  filter_upwards [hest] with t hh
  intro hr u f M hM hf heq
  apply hh hr u f M hM hf
  intro n hn
  have he := heq n hn
  rw [square_scalar_expansion e a b ρ g ha,add_assoc,entries_lowerOrder] at he
  exact he
end TamingCompatibility.ComplexMatrix

end
end

end
end
end

end OAI
