import OAI.MeasureTheory.Falconer.Shells.ShellTestConvergence
import OAI.MeasureTheory.Falconer.Measures.DistributionAbsoluteContinuity

namespace OAI

namespace PlanarFalconer
open MeasureTheory Set Filter
open scoped FourierTransform SchwartzMap Topology

 theorem shell_reconstruction_test_density (τ : FiniteMeasure ℝ) (hτ : HasShellApproximations τ) :
    ∃ a : Lp (α := ℝ) ℂ 1 volume, ∃ b : Lp (α := ℝ) ℂ 2 volume,
      ∀ φ : 𝓢(ℝ, ℂ), (∫ x, φ x * (a x+b x)) = ∫ x, φ x ∂(τ : Measure ℝ) := by
  obtain ⟨τN,_,_,h2,h1⟩ := shell_approximations_summable τ hτ
  let a : Lp (α := ℝ) ℂ 1 volume := sourceLowTerm τ + ∑' n, shellL1Error τ τN n
  let b : Lp (α := ℝ) ℂ 2 volume := ∑' n, shellL2Term τN n
  refine ⟨a,b,?_⟩
  intro φ
  have hlim := ((schwartzLpTest_sum_tendsto 1 φ _ h1).const_add
    (schwartzLpTest 1 φ (sourceLowTerm τ))).add (schwartzLpTest_sum_tendsto 2 φ _ h2)
  have he (N : ℕ) : (schwartzLpTest 1 φ (sourceLowTerm τ) +
      ∑ n ∈ Finset.range N, schwartzLpTest 1 φ (shellL1Error τ τN n)) +
      ∑ n ∈ Finset.range N, schwartzLpTest 2 φ (shellL2Term τN n) =
      schwartzLpTest 1 φ (sourceLowTerm τ) +
      ∑ n ∈ Finset.range N, ∫ x, φ x * kernelMeasureConvolution (sourceShellKernel n) τ x := by
    rw [add_assoc, ← Finset.sum_add_distrib]
    congr 1
    apply Finset.sum_congr rfl
    intro n _
    exact schwartzLpTest_shell_recombine τ τN φ n
  simp_rw [he] at hlim
  have hval : schwartzLpTest 1 φ a + schwartzLpTest 2 φ b =
      ∫ x, φ x ∂(τ : Measure ℝ) := by
    have hu := tendsto_nhds_unique hlim (sourceShell_spatial_test_tendsto τ φ)
    simpa only [a,b,map_add] using hu
  have ha := (φ.memLp_top volume).integrable_mul (Lp.memLp a)
  have hb := (φ.memLp 2 volume).integrable_mul (Lp.memLp b)
  change Integrable (fun x => φ x * a x) at ha
  change Integrable (fun x => φ x * b x) at hb
  rw [← hval, schwartzLpTest_apply, schwartzLpTest_apply]
  simp_rw [mul_add]
  exact integral_add ha hb

 theorem shell_reconstruction_locallyIntegrable (τ : FiniteMeasure ℝ)
    (hτ : HasShellApproximations τ) :
    ∃ f : ℝ → ℂ, LocallyIntegrable f volume ∧
      ∀ (g : ℝ → ℝ), ContDiff ℝ (⊤ : ℕ∞) g → HasCompactSupport g →
        (∫ x, (g x : ℂ) ∂(τ : Measure ℝ)) = ∫ x, g x • f x := by
  obtain ⟨a,b,ht⟩ := shell_reconstruction_test_density τ hτ
  refine ⟨fun x => a x+b x,
    ((Lp.memLp a).locallyIntegrable (by norm_num)).add
      ((Lp.memLp b).locallyIntegrable (by norm_num)), ?_⟩
  intro g hg hc
  let φ : 𝓢(ℝ, ℂ) := (hc.comp_left (map_zero Complex.ofRealCLM)).toSchwartzMap
    (Complex.ofRealCLM.contDiff.comp hg)
  exact (ht φ).symm

 theorem shell_criterion (τ : FiniteMeasure ℝ) (hτ : HasShellApproximations τ) :
    (τ : Measure ℝ) ≪ volume := by
  obtain ⟨f,hf,ht⟩ := shell_reconstruction_locallyIntegrable τ hτ
  exact absolutelyContinuous_of_smooth_test_density τ f hf ht

 theorem shellCriterionTarget_proved : ShellCriterionTarget := shell_criterion

end PlanarFalconer

end OAI
