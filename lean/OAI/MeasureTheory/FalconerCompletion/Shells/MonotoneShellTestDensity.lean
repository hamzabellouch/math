import Mathlib
import OAI.MeasureTheory.Falconer.Fourier.SchwartzLpTests
import OAI.MeasureTheory.Falconer.Measures.DistributionAbsoluteContinuity
import OAI.MeasureTheory.Falconer.Model
import OAI.MeasureTheory.Falconer.Shells.ShellKernels
import OAI.MeasureTheory.Falconer.Shells.ShellSummability
import OAI.MeasureTheory.FalconerCompletion.Graphs.ComplexOfPositiveFinite

namespace OAI

/-! Dyadic shells and prefix decompositions. -/

open _root_.OAI.PlanarFalconer

section
section
namespace CurrentFalconer.MonotoneShell
open MeasureTheory Set Filter PlanarFalconer
open scoped Topology ENNReal FourierTransform SchwartzMap
lemma monotone_shell_test_density
    (J : ℕ) (α : ℕ → FiniteMeasure ℝ) (αinf : FiniteMeasure ℝ)
    (τ : ℕ → ComplexMeasure ℝ)
    (hfinite : ∀ n, IsFiniteMeasure (τ n).variation)
    (hmono : Antitone (fun n => (α n : Measure ℝ)))
    (hlim : ∀ s, MeasurableSet s → Tendsto (fun N => (α N : Measure ℝ) s) atTop
      (𝓝 ((αinf : Measure ℝ) s)))
    (hTV : Summable (fun n => complexVariationError (α (n+1)) (τ n)))
    (henergy : Summable (fun n => Real.sqrt (complexShellEnergy (τ n) (n+J+1)))) :
    ∃ a : Lp (α:=ℝ) ℂ 1 volume, ∃ b : Lp (α:=ℝ) ℂ 2 volume,
      ∀ φ : 𝓢(ℝ,ℂ), (∫ x, φ x*(a x+b x)) = ∫ x, φ x ∂(αinf : Measure ℝ) := by
  let (n : ℕ) := hfinite n
  have (n : ℕ) : IsFiniteMeasure (complexOfPositive (α (n+1))-τ n).variation :=
    isFiniteMeasure_of_le ((complexOfPositive (α (n+1))).variation+(τ n).variation)
      VectorMeasure.variation_sub_le
  let e (n : ℕ) := complexBand1 (complexOfPositive (α (n+1))-τ n) (n+J)
  let g (n : ℕ) := complexBand2 (τ n) (n+J)
  have he : Summable e := by
    apply Summable.of_norm
    apply (hTV.mul_left (2 * ∫ x, ‖sourceShellKernel 0 x‖)).of_nonneg_of_le
      (fun n => norm_nonneg _) (fun n => ?_)
    have h := complexBand1_norm (complexOfPositive (α (n+1))-τ n) (n+J)
    simpa only [e,complexVariationError,mul_assoc,mul_left_comm,mul_comm] using h
  have hg : Summable g := by
    apply Summable.of_norm
    exact (henergy.mul_left (Real.sqrt ((2*Real.pi)⁻¹))).of_nonneg_of_le
      (fun n => norm_nonneg _) (fun n => complexBand2_norm (τ n) (n+J))
  obtain ⟨Z,hZ⟩ := monotone_correction_converges J α αinf hmono hlim
  let a := lowTerm J (αinf : Measure ℝ) + ∑' n, e n - Z
  let b := ∑' n, g n
  refine ⟨a,b,?_⟩
  intro φ
  have htZ := ((schwartzLpTest 1 φ).continuous.tendsto Z).comp hZ
  have ht := (((schwartzLpTest_sum_tendsto 1 φ e he).const_add
    (schwartzLpTest 1 φ (lowTerm J (αinf : Measure ℝ)))).sub htZ).add
    (schwartzLpTest_sum_tendsto 2 φ g hg)
  have hf (N : ℕ) :
      ((schwartzLpTest 1 φ (lowTerm J (αinf : Measure ℝ)) +
        ∑ n ∈ Finset.range N, schwartzLpTest 1 φ (e n)) -
        schwartzLpTest 1 φ (∑ n ∈ Finset.range N,
          bandTerm (n+J) ((α (n+1) : Measure ℝ)-(αinf : Measure ℝ)))) +
        ∑ n ∈ Finset.range N, schwartzLpTest 2 φ (g n) =
        schwartzLpTest 1 φ (lowTerm (N+J) (αinf : Measure ℝ)) := by
    rw [bandTerm_telescope J N,map_add,map_sum,map_sum]
    have hr (n : ℕ) : schwartzLpTest 1 φ (e n) + schwartzLpTest 2 φ (g n) -
        schwartzLpTest 1 φ (bandTerm (n+J) ((α (n+1) : Measure ℝ)-(αinf : Measure ℝ))) =
        schwartzLpTest 1 φ (bandTerm (n+J) (αinf : Measure ℝ)) := by
      rw [complex_band_recombine,bandTerm_sub_of_le _ _ _
        (monotone_limit_le α αinf hmono hlim (n+1)),map_sub]
      abel
    calc
      _ = schwartzLpTest 1 φ (lowTerm J (αinf : Measure ℝ)) +
          ∑ n ∈ Finset.range N, (schwartzLpTest 1 φ (e n) + schwartzLpTest 2 φ (g n) -
            schwartzLpTest 1 φ (bandTerm (n+J) ((α (n+1) : Measure ℝ)-(αinf : Measure ℝ)))) := by
              rw [Finset.sum_sub_distrib,Finset.sum_add_distrib]; abel
      _ = _ := by simp_rw [hr]
  simp only [Function.comp_def] at ht
  simp_rw [hf] at ht
  have hv := tendsto_nhds_unique ht (lowTerm_test_tendsto J αinf φ)
  have hval : schwartzLpTest 1 φ a+schwartzLpTest 2 φ b = ∫ x, φ x ∂(αinf : Measure ℝ) := by
    simpa only [a,b,map_sub,map_add] using hv
  have ha := (φ.memLp_top volume).integrable_mul (Lp.memLp a)
  have hb := (φ.memLp 2 volume).integrable_mul (Lp.memLp b)
  change Integrable (fun x => φ x*a x) at ha
  change Integrable (fun x => φ x*b x) at hb
  rw [←hval,schwartzLpTest_apply,schwartzLpTest_apply]
  simp_rw [mul_add]
  exact integral_add ha hb

end CurrentFalconer.MonotoneShell
end
end

section
section
namespace CurrentFalconer.MonotoneShell
open MeasureTheory Set Filter
open scoped Topology ENNReal

theorem monotone_measure_shell_criterion
    (K : ℕ) (α : ℕ → FiniteMeasure ℝ) (αinf : FiniteMeasure ℝ)
    (τ : ℕ → ComplexMeasure ℝ)
    (hfinite : ∀ N, IsFiniteMeasure (τ N).variation)
    (hmono : ∀ N ≥ K, (α (N+1) : Measure ℝ) ≤ (α N : Measure ℝ))
    (hlim : ∀ s, MeasurableSet s →
      Tendsto (fun N => (α N : Measure ℝ) s) atTop (𝓝 ((αinf : Measure ℝ) s)))
    (hTV : Summable (fun n => complexVariationError (α (n+K)) (τ (n+K))))
    (henergy : Summable (fun n => Real.sqrt (complexShellEnergy (τ (n+K)) (n+K)))) :
    (αinf : Measure ℝ) ≪ volume
    := by
  let μ (n : ℕ) := α (n+K)
  let ν (n : ℕ) := τ (n+1+K)
  have hm : Antitone (fun n => (μ n : Measure ℝ)) := by
    apply antitone_nat_of_succ_le
    intro n
    simpa only [μ,Nat.add_assoc,Nat.add_left_comm,Nat.add_comm] using hmono (n+K) (by omega)
  have hl : ∀ s, MeasurableSet s → Tendsto (fun n => (μ n : Measure ℝ) s) atTop
      (𝓝 ((αinf : Measure ℝ) s)) := by
    intro s hs
    exact (hlim s hs).comp (tendsto_add_atTop_nat K)
  have h1 : Summable (fun n => complexVariationError (μ (n+1)) (ν n)) := by
    exact (summable_nat_add_iff (f := fun n => complexVariationError (α (n+K)) (τ (n+K))) 1).mpr hTV
  have h2 : Summable (fun n => Real.sqrt (complexShellEnergy (ν n) (n+K+1))) := by
    have h := (summable_nat_add_iff (f := fun n => Real.sqrt (complexShellEnergy (τ (n+K)) (n+K))) 1).mpr henergy
    simpa only [ν,Nat.add_assoc,Nat.add_left_comm,Nat.add_comm] using h
  obtain ⟨a,b,ht⟩ := monotone_shell_test_density K μ αinf ν (fun n => hfinite (n+1+K)) hm hl h1 h2
  apply PlanarFalconer.absolutelyContinuous_of_smooth_test_density αinf (fun x => a x+b x)
  · exact ((MeasureTheory.Lp.memLp a).locallyIntegrable (by norm_num)).add
      ((MeasureTheory.Lp.memLp b).locallyIntegrable (by norm_num))
  · intro g hg hc
    let φ : SchwartzMap ℝ ℂ := (hc.comp_left (map_zero Complex.ofRealCLM)).toSchwartzMap
      (Complex.ofRealCLM.contDiff.comp hg)
    exact (ht φ).symm

end CurrentFalconer.MonotoneShell
end
end

section
section
namespace CurrentFalconer.MonotoneShell
open MeasureTheory Set Filter PlanarFalconer
open scoped Topology ENNReal
lemma complexVariationError_nonneg (μ : FiniteMeasure ℝ) (ν : ComplexMeasure ℝ) :
    0 ≤ complexVariationError μ ν := ENNReal.toReal_nonneg
lemma shell_sqrt_summable_of_decay (τ : ℕ → ComplexMeasure ℝ) {γ C : ℝ}
    (hγ : 0 < γ) (hC : 0 ≤ C) (N₀ : ℕ)
    (h : ∀ N ≥ N₀, complexShellEnergy (τ N) N ≤ C*(2:ℝ)^(-γ*(N:ℝ))) :
    Summable (fun N => Real.sqrt (complexShellEnergy (τ N) N)) := by
  have hs := (summable_dyadic_decay (half_pos hγ)).mul_left (Real.sqrt C)
  apply hs.of_norm_bounded_eventually_nat
  filter_upwards [eventually_ge_atTop N₀] with N hN
  rw [Real.norm_eq_abs,abs_of_nonneg (Real.sqrt_nonneg _)]
  apply (sq_le_sq₀ (Real.sqrt_nonneg _) (by positivity)).mp
  rw [Real.sq_sqrt (complexShellEnergy_nonneg _ _),mul_pow,Real.sq_sqrt hC,
    ←Real.rpow_natCast _ 2,←Real.rpow_mul (by norm_num)]
  convert h N hN using 1; congr 2; push_cast; ring

theorem monotone_measure_shell_criterion_of_decay
    (K : ℕ) (α : ℕ → FiniteMeasure ℝ) (αinf : FiniteMeasure ℝ)
    (τ : ℕ → ComplexMeasure ℝ)
    (hfinite : ∀ N, IsFiniteMeasure (τ N).variation)
    (hmono : ∀ N ≥ K, (α (N+1) : Measure ℝ) ≤ (α N : Measure ℝ))
    (hlim : ∀ s, MeasurableSet s → Tendsto (fun N => (α N : Measure ℝ) s) atTop
      (𝓝 ((αinf : Measure ℝ) s)))
    {η γ A B : ℝ} (hη : 0 < η) (hγ : 0 < γ) (hB : 0 ≤ B)
    (N₀ : ℕ) (hTV : ∀ N ≥ N₀, complexVariationError (α N) (τ N) ≤ A*(2:ℝ)^(-η*(N:ℝ)))
    (henergy : ∀ N ≥ N₀, complexShellEnergy (τ N) N ≤ B*(2:ℝ)^(-γ*(N:ℝ))) :
    (αinf : Measure ℝ) ≪ volume := by
  have h1 : Summable (fun N => complexVariationError (α N) (τ N)) := by
    apply ((summable_dyadic_decay hη).mul_left A).of_norm_bounded_eventually_nat
    filter_upwards [eventually_ge_atTop N₀] with N hN
    simpa only [Real.norm_eq_abs,abs_of_nonneg (complexVariationError_nonneg _ _)] using hTV N hN
  have h2 := shell_sqrt_summable_of_decay τ hγ hB N₀ henergy
  exact monotone_measure_shell_criterion K α αinf τ hfinite hmono hlim
    ((summable_nat_add_iff (f := fun N => complexVariationError (α N) (τ N)) K).mpr h1)
    ((summable_nat_add_iff (f := fun N => Real.sqrt (complexShellEnergy (τ N) N)) K).mpr h2)

end CurrentFalconer.MonotoneShell
end
end

section

namespace CurrentFalconer.AssemblyCompletion
open Set Metric Filter
open scoped Topology ContDiff
lemma shell_cutoff_exists : ∃ Ψ : ℝ → ℝ, ContDiff ℝ ∞ Ψ ∧
    tsupport Ψ⊆Ioo (1/4:ℝ) 4 ∧ (∀ r,0≤Ψ r) ∧ (∀ r∈Icc (1/2:ℝ) 2,1≤Ψ r) := by
  let f : ContDiffBump (5/4:ℝ) := ⟨4/5,9/10,by norm_num,by norm_num⟩
  refine ⟨f,f.contDiff,?_,f.nonneg',?_⟩
  · rw [f.tsupport_eq]
    intro r hr
    change |r-5/4|≤9/10 at hr
    obtain ⟨hl,hu⟩ := abs_le.mp hr
    constructor <;> linarith
  · intro r hr
    have hm : r∈closedBall (5/4:ℝ) f.rIn := by
      change |r-5/4|≤4/5
      rw [abs_le]
      constructor <;> linarith [hr.1,hr.2]
    rw [f.one_of_mem_closedBall hm]
lemma direction_cutoff_exists {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [FiniteDimensional ℝ V] (w₀ : V) (hw₀ : ‖w₀‖=1) :
    ∃ ψ : V → ℂ, ContDiff ℝ ∞ ψ ∧ (∀ w, ‖w‖=1 → ‖ψ w‖≤1) ∧
      ∀ w : V, ‖w-w₀‖≤1/100 →
        ψ =ᶠ[𝓝 w] (fun _ => 1) ∧ ψ =ᶠ[𝓝 (-w)] (fun _ => 0) := by
  let f : ContDiffBump w₀ := ⟨1/50,1/10,by norm_num,by norm_num⟩
  refine ⟨fun w => (f w:ℂ),Complex.ofRealCLM.contDiff.comp f.contDiff,?_,?_⟩
  · intro w _
    simpa only [Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg f.nonneg] using (f.le_one (x:=w))
  · intro w hw
    constructor
    · have h : w∈ball w₀ f.rIn := by
        rw [mem_ball,dist_eq_norm]
        change ‖w-w₀‖<1/50
        linarith
      filter_upwards [f.eventuallyEq_one_of_mem_ball h] with z hz
      simp only [Pi.one_apply] at hz
      simp [hz]
    · have hdist : f.rOut<dist (-w) w₀ := by
        have hh := norm_add_le (w+w₀) (w₀-w)
        have hadd : w+w₀+(w₀-w)= (2:ℝ) • w₀ := by module
        rw [hadd,norm_smul,hw₀] at hh
        have hn : ‖w₀-w‖=‖w-w₀‖ := norm_sub_rev _ _
        rw [hn] at hh
        have he : dist (-w) w₀=‖w+w₀‖ := by rw [dist_eq_norm,show -w-w₀=-(w+w₀) by module,norm_neg]
        rw [he]
        change (1:ℝ)/10<‖w+w₀‖
        norm_num at hh
        linarith
      have hev : ∀ᶠ z in 𝓝 (-w), f.rOut<dist z w₀ :=
        (continuous_id.dist continuous_const).continuousAt.eventually (lt_mem_nhds hdist)
      filter_upwards [hev] with z hz
      simp [f.zero_of_le_dist hz.le]
end CurrentFalconer.AssemblyCompletion
end

end OAI
