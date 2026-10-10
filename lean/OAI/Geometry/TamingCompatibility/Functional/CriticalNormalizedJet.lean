import Mathlib
import OAI.Geometry.TamingCompatibility.Functional.CriticalNormalized
import OAI.Geometry.TamingCompatibility.Charts.CriticalLocalJet

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

theorem normalized_interior_two_jet (hdim : Module.finrank ℝ E = 4)
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (a : ℝ → basisIndex E → basisIndex E → 𝓢(E,ℂ))
    (ha : ∀ n ≤ 3, Tendsto (fun r => ‖perturbation (F := F) n (a r)‖) (𝓝 0) (𝓝 0))
    (hac : ∀ n ≤ 3, ∀ i j, ContinuousAt (fun r => coefficientSize n (a r i j)) 0)
    (b : ℝ → ι → 𝓢(E,ℂ)) (L : ι → F →L[ℂ] F) (d : ι → E)
    (c : ℝ → κ → 𝓢(E,ℂ)) (K : κ → F →L[ℂ] F)
    (hb : ∀ n ≤ 3, ∀ i, ContinuousAt (fun r => coefficientSize n (b r i)) 0)
    (hc : ∀ n ≤ 3, ∀ i, ContinuousAt (fun r => coefficientSize n (c r i)) 0)
    (χ : ℕ → 𝓢(E,ℂ))
    (hχ : ∀ n ≤ 3, ∀ x ∈ tsupport (χ (n+1)), χ n =ᶠ[𝓝 x] fun _ => 1)
    (R E₀ : ℝ) (hE : 0 ≤ E₀) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ r in 𝓝 (0:ℝ), ∀ (hr : 0 < r), r ≤ 1 →
      ∀ (p : E) (u f : 𝓢(E,F)) (M : ℝ), 0 ≤ M →
      tsupport f ⊆ Metric.ball p (r*R) →
      (∀ k ≤ 3, ∀ m : Fin k → E, (∀ i, ‖m i‖ ≤ 1) → ∀ x, ‖(∂^{m} f) x‖ ≤ M/r^k) →
      (‖u.toLp 4 (volume : Measure E)‖ + ∑ i,
        ‖(∂_{stdOrthonormalBasis ℝ E i} u).toLp 2 (volume : Measure E)‖ ≤ E₀*M*r^3) →
      (∀ n ≤ 3, smulLeftCLM F (χ (n+1))
        (perturbedHelmholtz (a r) (rescaleSchwartz p r hr.ne' u : 𝓢'(E,F)) +
          matrixLowerOrder (b r) L d (c r) K (rescaleSchwartz p r hr.ne' u : 𝓢'(E,F))) =
        smulLeftCLM F (χ (n+1)) (r^2 • rescaleSchwartz p r hr.ne' f : 𝓢'(E,F))) →
      ∀ x : E, ((χ 4 : E → ℂ) =ᶠ[𝓝 x] fun _ => 1) →
        ‖u (r • x+p)‖ + ∑ i, ‖(∂_{stdOrthonormalBasis ℝ E i} u) (r • x+p)‖ +
          ∑ i, ∑ j, ‖(∂_{stdOrthonormalBasis ℝ E j} (∂_{stdOrthonormalBasis ℝ E i} u)) (r • x+p)‖ ≤ C*M := by
  classical
  obtain ⟨J,hJ,hjet⟩ := uniform_scaled_two_jet hdim a ha hac b L d c K hb hc χ hχ
  obtain ⟨N,hN,hsource⟩ := normalized_source_Hnat (E := E) (F := F) 3 R
  refine ⟨J*(N+E₀),by positivity,?_⟩
  filter_upwards [hjet] with r hj
  intro hr hr1 p u f M hM hs hf he heq x hx
  let fH := schwartzToH 3 (r^2 • rescaleSchwartz p r hr.ne' f)
  have hfn : ‖fH‖ ≤ N*M*r^2 := hsource p r M hr hM f hs hf
  have h := hj hr p u fH (by simpa only [fH,schwartzToH_spec,ContinuousLinearMap.map_smul_of_tower] using heq) x
  dsimp only at h
  rw [rescale_cutoff_two_jet (χ 4) p hr u x hx] at h
  let A₀ := ‖u (r • x+p)‖
  let A₁ := ∑ i, ‖(∂_{stdOrthonormalBasis ℝ E i} u) (r • x+p)‖
  let A₂ := ∑ i, ∑ j, ‖(∂_{stdOrthonormalBasis ℝ E j} (∂_{stdOrthonormalBasis ℝ E i} u)) (r • x+p)‖
  have h0 : 0 ≤ A₀ := norm_nonneg _
  have h1 : 0 ≤ A₁ := Finset.sum_nonneg (fun _ _ => norm_nonneg _)
  have h2 : 0 ≤ A₂ := Finset.sum_nonneg (fun _ _ => Finset.sum_nonneg (fun _ _ => norm_nonneg _))
  have hbound : A₀ + r*A₁ + r^2*A₂ ≤ (J*(N+E₀)*M)*r^2 := by
    apply h.trans
    calc
      _ ≤ J*(N*M*r^2 + r⁻¹*(E₀*M*r^3)) := by gcongr
      _ = _ := by field_simp
  have hscaled : (A₀+A₁+A₂)*r^2 ≤ A₀+r*A₁+r^2*A₂ := by
    have hrr : r^2 ≤ r := by nlinarith
    have hr2 : r^2 ≤ 1 := hrr.trans hr1
    nlinarith [mul_nonneg h0 (sub_nonneg.mpr hr2),mul_nonneg h1 (sub_nonneg.mpr hrr)]
  exact (mul_le_mul_iff_left₀ (sq_pos_of_pos hr)).mp (hscaled.trans hbound)

end TamingCompatibility.HilbertSobolev

end
end

end
end
end

end OAI
