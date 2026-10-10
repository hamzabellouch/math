import Mathlib
import OAI.Geometry.TamingCompatibility.Functional.CriticalNormalizedJet
import OAI.Geometry.TamingCompatibility.Currents.CriticalAffineDensity

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

omit [MeasurableSpace E] [BorelSpace E] [CompleteSpace F] [FiniteDimensional ℝ E] in
lemma local_matrixLower_congr {ι κ : Type*} [Fintype ι] [Fintype κ]
    (ψ : 𝓢(E,ℂ)) (b b' : ι → 𝓢(E,ℂ)) (c c' : κ → 𝓢(E,ℂ))
    (hb : ∀ i x, x ∈ tsupport ψ → b i x = b' i x)
    (hc : ∀ i x, x ∈ tsupport ψ → c i x = c' i x)
    (L : ι → F →L[ℂ] F) (d : ι → E) (K : κ → F →L[ℂ] F) (u : 𝓢'(E,F)) :
    smulLeftCLM F ψ (matrixLowerOrder b L d c K u) =
      smulLeftCLM F ψ (matrixLowerOrder b' L d c' K u) := by
  simp only [matrixLowerOrder,map_add,map_sum]
  congr 1
  · apply Finset.sum_congr rfl
    intro i _
    exact localized_coefficient_congr ψ (b i).hasTemperateGrowth (b' i).hasTemperateGrowth (hb i) _
  · apply Finset.sum_congr rfl
    intro i _
    exact localized_coefficient_congr ψ (c i).hasTemperateGrowth (c' i).hasTemperateGrowth (hc i) _

omit [MeasurableSpace E] [BorelSpace E] [CompleteSpace F] [FiniteDimensional ℝ E] in
lemma scaledCoefficient_on_cutoff (k : ℕ) (ζ : 𝓢(E,ℂ)) (hζ : HasCompactSupport (ζ : E → ℂ))
    (f : 𝓢(E,ℂ)) (p : E) (r : ℝ) (hr : r ≠ 0) (x : E) (h : ζ x = 1) :
    scaledCoefficient k ζ hζ f (f.smooth ⊤) p r x =
      (r^k • affineSchwartz p r hr f) x := by
  change ζ x * ((r:ℂ)^k * f (p+r•x)) = _
  simp only [h,one_mul,_root_.smul_apply,affineSchwartz_apply]
  rw [add_comm p (r•x),Complex.real_smul,Complex.ofReal_pow]

omit [CompleteSpace F] in
lemma local_scaled_frozen_equation
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (g : basisIndex E → basisIndex E → 𝓢(E,ℂ)) (p : E)
    (hgp : ∀ i j, g i j p = if i=j then ((((2*Real.pi)^2)⁻¹ : ℝ) : ℂ) else 0)
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
      (frozenPrincipal ζ hζ (fun i j x => -g i j x) (fun i j => (g i j).smooth ⊤ |>.neg) p r)
        (rescaleSchwartz p r hr u : 𝓢'(E,F)) +
      matrixLowerOrder (fun i => scaledCoefficient 1 ζ hζ (b i) ((b i).smooth ⊤) p r) L d
        (Sum.elim (fun i => scaledCoefficient 2 ζ hζ (c i) ((c i).smooth ⊤) p r) (fun _ : Unit => -ζ))
        (Sum.elim K (fun _ : Unit => ContinuousLinearMap.id ℂ F))
        (rescaleSchwartz p r hr u : 𝓢'(E,F))) =
    smulLeftCLM F ψ (r^2 • (rescaleSchwartz p r hr f : 𝓢'(E,F))) := by
  rw [local_frozen_system ζ hζ g p hgp r hr ψ hψ]
  rw [map_add, local_matrixLower_congr ψ _ (fun i => r • affineSchwartz p r hr (b i)) _
    (fun i => (r*r) • affineSchwartz p r hr (c i))
    (fun i y hy => by simpa only [pow_one] using scaledCoefficient_on_cutoff 1 ζ hζ (b i) p r hr y (hψ y hy))
    (fun i y hy => by simpa only [pow_two] using scaledCoefficient_on_cutoff 2 ζ hζ (c i) p r hr y (hψ y hy))]
  rw [← map_add]
  exact rescaled_local_schwartz_system p r hr (stdOrthonormalBasis ℝ E) g b L d c K u f ψ heq

theorem actual_normalized_two_jet (hdim : Module.finrank ℝ E = 4)
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (g : basisIndex E → basisIndex E → 𝓢(E,ℂ)) (p : E)
    (hgp : ∀ i j, g i j p = if i=j then ((((2*Real.pi)^2)⁻¹ : ℝ) : ℂ) else 0)
    (b : ι → 𝓢(E,ℂ)) (L : ι → F →L[ℂ] F) (d : ι → E)
    (c : κ → 𝓢(E,ℂ)) (K : κ → F →L[ℂ] F)
    (ζ : 𝓢(E,ℂ)) (hζ : HasCompactSupport (ζ : E → ℂ))
    (χ : ℕ → 𝓢(E,ℂ))
    (hχ : ∀ n ≤ 3, ∀ x ∈ tsupport (χ (n+1)), χ n =ᶠ[𝓝 x] fun _ => 1)
    (hζχ : ∀ n ≤ 3, ∀ x ∈ tsupport (χ (n+1)), ζ x = 1)
    (R E₀ : ℝ) (hE : 0 ≤ E₀) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ r in 𝓝 (0:ℝ), ∀ (hr : 0 < r), r ≤ 1 →
      ∀ (u f : 𝓢(E,F)) (M : ℝ), 0 ≤ M →
      tsupport f ⊆ Metric.ball p (r*R) →
      (∀ k ≤ 3, ∀ m : Fin k → E, (∀ i, ‖m i‖ ≤ 1) → ∀ x, ‖(∂^{m} f) x‖ ≤ M/r^k) →
      (‖u.toLp 4 (volume : Measure E)‖ + ∑ i,
        ‖(∂_{stdOrthonormalBasis ℝ E i} u).toLp 2 (volume : Measure E)‖ ≤ E₀*M*r^3) →
      (∀ n ≤ 3, smulLeftCLM F
        (affineSchwartz (-(r⁻¹ • p)) r⁻¹ (inv_ne_zero hr.ne') (χ (n+1)))
        (-directionalPrincipal (stdOrthonormalBasis ℝ E) g (u : 𝓢'(E,F)) +
          matrixLowerOrder b L d c K (u : 𝓢'(E,F))) =
        smulLeftCLM F (affineSchwartz (-(r⁻¹ • p)) r⁻¹ (inv_ne_zero hr.ne') (χ (n+1)))
          (f : 𝓢'(E,F))) →
      ∀ x : E, ((χ 4 : E → ℂ) =ᶠ[𝓝 x] fun _ => 1) →
        ‖u (r • x+p)‖ + ∑ i, ‖(∂_{stdOrthonormalBasis ℝ E i} u) (r • x+p)‖ +
          ∑ i, ∑ j, ‖(∂_{stdOrthonormalBasis ℝ E j} (∂_{stdOrthonormalBasis ℝ E i} u)) (r • x+p)‖ ≤ C*M := by
  classical
  let a := frozenPrincipal ζ hζ (fun i j x => -g i j x) (fun i j => (g i j).smooth ⊤ |>.neg) p
  let B := fun r i => scaledCoefficient 1 ζ hζ (b i) ((b i).smooth ⊤) p r
  let D := fun r i => scaledCoefficient 2 ζ hζ (c i) ((c i).smooth ⊤) p r
  let Cc := fun r => Sum.elim (D r) (fun _ : Unit => -ζ)
  let Ks := Sum.elim K (fun _ : Unit => ContinuousLinearMap.id ℂ F)
  have ha : ∀ n ≤ 3, Tendsto (fun r => ‖perturbation (F := F) n (a r)‖) (𝓝 0) (𝓝 0) :=
    fun n _ => frozen_perturbation_norm_tendsto n ζ hζ _ _ p
  have hac : ∀ n ≤ 3, ∀ i j, ContinuousAt (fun r => coefficientSize n (a r i j)) 0 := by
    intro n _ i j
    have h := frozenCoefficient_size_tendsto_zero n ζ hζ (fun x => -g i j x) ((g i j).smooth ⊤ |>.neg) p
    simpa only [ContinuousAt,a,frozenPrincipal,frozenCoefficient_zero,coefficientSize_zero] using h
  have hb : ∀ n ≤ 3, ∀ i, ContinuousAt (fun r => coefficientSize n (B r i)) 0 :=
    fun n _ i => (scaledCoefficient_size_continuous n 1 ζ hζ (b i) ((b i).smooth ⊤) p).continuousAt
  have hc : ∀ n ≤ 3, ∀ i, ContinuousAt (fun r => coefficientSize n (Cc r i)) 0 := by
    intro n _ i
    cases i with
    | inl i => exact (scaledCoefficient_size_continuous n 2 ζ hζ (c i) ((c i).smooth ⊤) p).continuousAt
    | inr i => exact continuousAt_const
  obtain ⟨A,hA,hest⟩ := normalized_interior_two_jet hdim a ha hac B L d Cc Ks hb hc χ hχ R E₀ hE
  refine ⟨A,hA,?_⟩
  filter_upwards [hest] with r hh
  intro hr hr1 u f M hM hs hf he heq x hx
  apply hh hr hr1 p u f M hM hs hf he (fun n hn => ?_) x hx
  exact local_scaled_frozen_equation g p hgp b L d c K ζ hζ r hr.ne'
    (χ (n+1)) (hζχ n hn) u f (heq n hn)

end TamingCompatibility.HilbertSobolev

end
end

end
end
end

end OAI
