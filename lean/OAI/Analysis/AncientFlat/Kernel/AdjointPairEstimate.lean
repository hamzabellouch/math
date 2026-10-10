import OAI.Analysis.AncientFlat.Kernel.AdjointBounds
import OAI.Analysis.AncientFlat.Kernel.AdjointPairContinuity

namespace OAI
noncomputable section
open Set Filter MeasureTheory
open scoped Topology ContDiff SchwartzMap Laplacian ZeroAtInfty BoundedContinuousFunction
namespace FlatDuality
open BiharmonicKernel InnerProductSpace ParametrixUniqueness FlatSimilarity
variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
omit [MeasurableSpace V] [BorelSpace V] in
lemma adjointError_const (c : ℝ) (t : ℝ) (φ : SchwartzMap V ℂ) :
    adjointError c (fun _ => c^2) (fun _ => 0) t φ=0 := by
  have hd : movingDeviation c (fun _ : V => c^2) t=0 := by
    funext x
    dsimp [movingDeviation]
    ring
  have he : deviationTest c (fun _ : V => c^2) t φ=0 := by
    ext x
    unfold deviationTest
    rw [hd]
    change SchwartzMap.smulLeftCLM ℂ (fun _ : V => (0:ℝ)) φ x=0
    rw [SchwartzMap.smulLeftCLM_apply_apply (Function.HasTemperateGrowth.const (0:ℝ))]
    exact zero_smul _ _
  have hp : potentialTest (fun _ : V => 0) t φ=0 := by simp [potentialTest]
  simp only [adjointError,he,hp,←SchwartzMap.laplacianCLM_eq',map_zero,zero_add]
lemma adjoint_pair_uniform_estimate {c : ℝ} {Af Bf : V → ℝ} (h : SymbolBounds c Af Bf)
    (ε : ℝ) (hε : 0<ε) :
    ∃ C : ℝ, 0≤C ∧ ∀ (d : C₀(V,ℂ)) (u v : ℝ → C₀(V,ℂ)),
      MovesClassically Af Bf d u → MovesClassically (fun _ => c^2) (fun _ => 0) d v →
      ∀ z : V, ‖∫ x, kernel ε (x-z)*(u 1 x-v 1 x)‖≤C*decayWeight z*‖d‖ := by
  obtain ⟨L,B,hL,hBi,hBn,hBb⟩ := adjointError_uniform_majorant h ε hε
  obtain ⟨K,hK,hKb⟩ := h.uniform_moving_bound
  let J := ∫ x, (1+‖x‖)*B x
  have hJ : 0≤J := integral_nonneg (fun x => mul_nonneg (by positivity) (hBn x))
  refine ⟨L*J*K,by positivity,fun d u v hu hv z => ?_⟩
  let f := fun s => (∫ x, kernelTest (adjointTime c ε) adjointAmplitude z s x*u s x)-
      (∫ x, kernelTest (adjointTime c ε) adjointAmplitude z s x*v s x)
  obtain ⟨Kc,hKc,hKcb⟩ := (SymbolBounds.constant (V := V) h.1).uniform_moving_bound
  have hf : ContinuousOn f (Icc (0:ℝ) 1) :=
    (continuousOn_adjoint_pair c ε hε z u hu.2.1 (K*‖d‖) (by positivity) (hKb d u hu)).sub
      (continuousOn_adjoint_pair c ε hε z v hv.2.1 (Kc*‖d‖) (by positivity) (hKcb d v hv))
  have hd : ∀ s ∈ Ioo (0:ℝ) 1, ∃ w : ℂ, HasDerivAt f w s ∧ ‖w‖≤L*J*K*decayWeight z*‖d‖ := by
    intro s hs
    let φ := adjointSchwartz c ε s z (hε.trans_le (adjointTime_bounds c ε ⟨hs.1.le,hs.2.le⟩).1)
    have hd1 := hasDerivAt_adjoint_pair h hu ε hε z hs
    have hd2 := hasDerivAt_adjoint_pair (SymbolBounds.constant (V := V) h.1) hv ε hε z hs
    simp only [adjointError_const,zero_apply,zero_mul,integral_zero,neg_zero] at hd2
    refine ⟨-(∫ x, adjointError c Af Bf s φ x*u s x),by simpa only [sub_zero] using! hd1.sub hd2,?_⟩
    rw [norm_neg]
    calc
      _ ≤ ∫ x, (L*decayWeight z*((1+‖x-z‖)*B (x-z)))*(K*‖d‖) := by
        apply norm_integral_le_of_norm_le
          (((hBi.comp_sub_right z).const_mul (L*decayWeight z)).mul_const (K*‖d‖))
        filter_upwards with x
        rw [norm_mul]
        exact mul_le_mul (hBb s ⟨hs.1.le,hs.2.le⟩ z x) (hKb d u hu s ⟨hs.1.le,hs.2.le⟩ x)
          (norm_nonneg _) (mul_nonneg (mul_nonneg hL (decayWeight_pos z).le) (mul_nonneg (by positivity) (hBn _)))
      _ = L*J*K*decayWeight z*‖d‖ := by
        rw [integral_mul_const,integral_const_mul]
        have hi := integral_sub_right_eq_self (μ := volume) (fun x : V => (1+‖x‖)*B x) z
        rw [hi]
        dsimp [J]
        ring
  have he := norm_endpoints_le (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hL hJ) hK) (decayWeight_pos z).le) (norm_nonneg d)) hf hd
  have h0 : f 0=0 := by dsimp [f]; rw [hu.1,hv.1]; exact sub_self _
  have h1 : f 1=∫ x, kernel ε (x-z)*(u 1 x-v 1 x) := by
    have hk : Integrable (fun x : V => kernel ε (x-z)) := by
      rw [←heatKernel_eq_kernel ε hε]
      exact (heatKernel ε hε).integrable.comp_sub_right z
    have hc : Continuous (fun x : V => kernel ε (x-z)) := by
      rw [←heatKernel_eq_kernel ε hε]
      exact (heatKernel ε hε).continuous.comp (continuous_id.sub continuous_const)
    have hu1 : Bounded (fun x => u 1 x) := ⟨K*‖d‖,by positivity,hKb d u hu 1 ⟨zero_le_one,le_rfl⟩⟩
    have hv1 : Bounded (fun x => v 1 x) := ⟨Kc*‖d‖,by positivity,hKcb d v hv 1 ⟨zero_le_one,le_rfl⟩⟩
    dsimp [f,kernelTest,adjointTime,adjointAmplitude]
    simp only [sub_self,mul_zero,add_zero,zero_div,Real.exp_zero,Complex.ofReal_one,one_mul]
    have hiu : Integrable (fun x => kernel ε (x-z)*u 1 x) := integrable_mul_bounded hk (u 1).continuous hu1
    have hiv : Integrable (fun x => kernel ε (x-z)*v 1 x) := integrable_mul_bounded hk (v 1).continuous hv1
    rw [←integral_sub hiu hiv]
    apply integral_congr_ae
    filter_upwards with x
    ring
  rw [h0,sub_zero,h1] at he
  exact he
end FlatDuality

end

end OAI
