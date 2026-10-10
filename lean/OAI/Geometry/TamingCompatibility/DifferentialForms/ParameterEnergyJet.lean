import Mathlib
import OAI.Geometry.TamingCompatibility.DifferentialForms.CenterUniformJet
import OAI.Geometry.TamingCompatibility.Charts.LocalizedHnat

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
variable {P : Type*} [TopologicalSpace P]
local instance : Fact ((1 : ENNReal) ≤ 4) := ⟨by norm_num⟩

theorem parameter_energy_two_jet (p₀ : P) (hdim : Module.finrank ℝ E = 4)
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (a : P → basisIndex E → basisIndex E → 𝓢(E,ℂ))
    (ha : ∀ n ≤ 3, Tendsto (fun r => ‖perturbation (F := F) n (a r)‖) (𝓝 p₀) (𝓝 0))
    (hac : ∀ n ≤ 3, ∀ i j, ContinuousAt (fun r => coefficientSize n (a r i j)) p₀)
    (b : P → ι → 𝓢(E,ℂ)) (L : ι → F →L[ℂ] F) (d : ι → E)
    (c : P → κ → 𝓢(E,ℂ)) (K : κ → F →L[ℂ] F)
    (hb : ∀ n ≤ 3, ∀ i, ContinuousAt (fun r => coefficientSize n (b r i)) p₀)
    (hc : ∀ n ≤ 3, ∀ i, ContinuousAt (fun r => coefficientSize n (c r i)) p₀)
    (χ : ℕ → 𝓢(E,ℂ))
    (hχ : ∀ n ≤ 3, ∀ x ∈ tsupport (χ (n+1)), χ n =ᶠ[𝓝 x] fun _ => 1)
    (ζ : 𝓢(E,ℂ)) (hζ : HasCompactSupport (ζ : E → ℂ))
    (hζχ : ∀ n ≤ 3, ∀ x ∈ tsupport (χ (n+1)), ζ x = 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ t in 𝓝 p₀, ∀ (r : ℝ) (hr : 0 < r)
      (p : E) (u f : 𝓢(E,F)) (M : ℝ), 0 ≤ M →
      (∀ k ≤ 3, ∀ m : Fin k → E, (∀ i, ‖m i‖ ≤ 1) → ∀ x, ‖(∂^{m} f) x‖ ≤ M/r^k) →
      (∀ n ≤ 3, smulLeftCLM F (χ (n+1))
        (perturbedHelmholtz (a t) (rescaleSchwartz p r hr.ne' u : 𝓢'(E,F)) +
          matrixLowerOrder (b t) L d (c t) K (rescaleSchwartz p r hr.ne' u : 𝓢'(E,F))) =
        smulLeftCLM F (χ (n+1)) (r^2 • rescaleSchwartz p r hr.ne' f : 𝓢'(E,F))) →
      ∀ x : E, ((χ 4 : E → ℂ) =ᶠ[𝓝 x] fun _ => 1) →
        r*‖u (r • x+p)‖ + r^2*∑ i, ‖(∂_{stdOrthonormalBasis ℝ E i} u) (r • x+p)‖ +
          r^3*∑ i, ∑ j, ‖(∂_{stdOrthonormalBasis ℝ E j} (∂_{stdOrthonormalBasis ℝ E i} u)) (r • x+p)‖ ≤
        C*(M*r^3 + ‖u.toLp 4 (volume : Measure E)‖ +
          ∑ i, ‖(∂_{stdOrthonormalBasis ℝ E i} u).toLp 2 (volume : Measure E)‖) := by
  classical
  obtain ⟨J,hJ,hjet⟩ := parameter_scaled_two_jet p₀ hdim a ha hac b L d c K hb hc χ hχ
  obtain ⟨N,hN,hsource⟩ := localized_normalized_source_Hnat (E := E) (F := F) 3 ζ hζ
  refine ⟨J*max N 1,mul_nonneg hJ (le_trans (by norm_num) (le_max_right N 1)),?_⟩
  filter_upwards [hjet] with t hj
  intro r hr p u f M hM hf heq x hx
  let fH := schwartzToH 3 (SchwartzMap.smulLeftCLM F ζ (r^2 • rescaleSchwartz p r hr.ne' f))
  have hfn : ‖fH‖ ≤ N*M*r^2 := hsource p r M hr hM f hf
  have h := hj r hr p u fH (fun n hn => by
    rw [show toDistribution E F 3 fH = (SchwartzMap.smulLeftCLM F ζ
      (r^2 • rescaleSchwartz p r hr.ne' f) : 𝓢'(E,F)) from schwartzToH_spec _ _]
    rw [← ComplexMatrix.product_schwartz,local_cutoff_one ζ (χ (n+1)) (hζχ n hn)]
    simpa only [ContinuousLinearMap.map_smul_of_tower] using heq n hn) x
  dsimp only at h
  rw [rescale_cutoff_two_jet (χ 4) p hr u x hx] at h
  let Q := ‖u.toLp 4 (volume : Measure E)‖ +
    ∑ i, ‖(∂_{stdOrthonormalBasis ℝ E i} u).toLp 2 (volume : Measure E)‖
  have hQ : 0 ≤ Q := add_nonneg (norm_nonneg _) (Finset.sum_nonneg (fun _ _ => norm_nonneg _))
  have h' := mul_le_mul_of_nonneg_left h hr.le
  calc
    _ ≤ r*(J*(N*M*r^2+r⁻¹*Q)) := by
      apply le_trans _ (mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left (add_le_add hfn (le_refl (r⁻¹*Q))) hJ) hr.le)
      convert h' using 1; ring
    _ = J*(N*(M*r^3)+Q) := by field_simp
    _ ≤ J*(max N 1*(M*r^3)+max N 1*Q) := by
      gcongr
      · exact le_max_left N 1
      · exact le_mul_of_one_le_left hQ (le_max_right N 1)
    _ = _ := by dsimp only [Q]; ring
end TamingCompatibility.HilbertSobolev

end
end

section

noncomputable section
namespace TamingCompatibility.HilbertSobolev
open MeasureTheory TemperedDistribution EuclideanSobolevOperators Filter LineDeriv Set
open scoped SchwartzMap LineDeriv Topology ContDiff ENNReal
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
local instance : Fact ((1 : ENNReal) ≤ 4) := ⟨by norm_num⟩

theorem center_uniform_energy_two_jet (hdim : Module.finrank ℝ E = 4)
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (g : basisIndex E → basisIndex E → 𝓢(E,ℂ)) (p₀ : E)
    (hgp : ∀ i j, g i j p₀ = if i=j then ((((2*Real.pi)^2)⁻¹ : ℝ) : ℂ) else 0)
    (b : ι → 𝓢(E,ℂ)) (L : ι → F →L[ℂ] F) (d : ι → E)
    (c : κ → 𝓢(E,ℂ)) (K : κ → F →L[ℂ] F)
    (ζ : 𝓢(E,ℂ)) (hζ : HasCompactSupport (ζ : E → ℂ))
    (χ : ℕ → 𝓢(E,ℂ))
    (hχ : ∀ n ≤ 3, ∀ x ∈ tsupport (χ (n+1)), χ n =ᶠ[𝓝 x] fun _ => 1)
    (hζχ : ∀ n ≤ 3, ∀ x ∈ tsupport (χ (n+1)), ζ x = 1)
    :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ t in 𝓝 (0,p₀), ∀ (hr : 0 < t.1),
      ∀ (u f : 𝓢(E,F)) (M : ℝ), 0 ≤ M →
      (∀ k ≤ 3, ∀ m : Fin k → E, (∀ i, ‖m i‖ ≤ 1) → ∀ x, ‖(∂^{m} f) x‖ ≤ M/t.1^k) →
      (∀ n ≤ 3, smulLeftCLM F
        (affineSchwartz (-(t.1⁻¹ • t.2)) t.1⁻¹ (inv_ne_zero hr.ne') (χ (n+1)))
        (-directionalPrincipal (stdOrthonormalBasis ℝ E) g (u : 𝓢'(E,F)) +
          matrixLowerOrder b L d c K (u : 𝓢'(E,F))) =
        smulLeftCLM F (affineSchwartz (-(t.1⁻¹ • t.2)) t.1⁻¹ (inv_ne_zero hr.ne') (χ (n+1)))
          (f : 𝓢'(E,F))) →
      ∀ x : E, ((χ 4 : E → ℂ) =ᶠ[𝓝 x] fun _ => 1) →
        t.1*‖u (t.1 • x+t.2)‖ + t.1^2*∑ i, ‖(∂_{stdOrthonormalBasis ℝ E i} u) (t.1 • x+t.2)‖ +
          t.1^3*∑ i, ∑ j, ‖(∂_{stdOrthonormalBasis ℝ E j} (∂_{stdOrthonormalBasis ℝ E i} u)) (t.1 • x+t.2)‖ ≤
        C*(M*t.1^3 + ‖u.toLp 4 (volume : Measure E)‖ +
          ∑ i, ‖(∂_{stdOrthonormalBasis ℝ E i} u).toLp 2 (volume : Measure E)‖) := by
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
  obtain ⟨A,hA,hest⟩ := parameter_energy_two_jet (0,p₀) hdim a ha hac B L d Cc Ks hb hc χ hχ ζ hζ hζχ
  refine ⟨A,hA,?_⟩
  filter_upwards [hest] with t hh
  intro hr u f M hM hf heq x hx
  apply hh t.1 hr t.2 u f M hM hf (fun n hn => ?_) x hx
  exact moving_local_scaled_frozen_equation g p₀ t.2 hgp b L d c K ζ hζ t.1 hr.ne'
    (χ (n+1)) (hζχ n hn) u f (heq n hn)

end TamingCompatibility.HilbertSobolev

end
end

end
end
end

end OAI
