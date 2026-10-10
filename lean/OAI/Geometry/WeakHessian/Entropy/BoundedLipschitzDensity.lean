import Mathlib
import OAI.Geometry.WeakHessian.HeatFlow.HeatPositiveDerivative

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile141
noncomputable section
namespace WeakHessian
open Set Filter MeasureTheory WeakHessianFunctional
open scoped Topology ENNReal NNReal InnerProductSpace

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable [CompleteSpace X] [ProperSpace X] [TopologicalSpace.SeparableSpace X] {m : Measure X} [SigmaFinite m]

omit [CompleteSpace X] [SigmaFinite m] in
lemma bounded_lipschitz_L2_approx (hfin : FiniteOnBoundedSets m)
    (h : QuadraticCheegerEnergy m) (u : Lp ℝ 2 m) (n : ℕ) (hu : ∀ᵐ x ∂m,|u x| ≤ (n:ℝ)) :
    ∃ fs : ℕ → X → ℝ,(∀ k,GloballyLipschitz (fs k)) ∧
      (∀ k x,|fs k x| ≤ (n:ℝ)) ∧ ∃ hfs : ∀ k,MemLp (fs k) 2 m,
        Tendsto (fun k => (hfs k).toLp (fs k)) atTop (𝓝 u) := by
  let τ (k : ℕ) := 1/((k:ℝ)+1)
  have hτ (k : ℕ) : 0 < τ k := by dsimp [τ]; positivity
  let vs (k : ℕ) := cheegerHeat h (τ k) u
  have hvT : Tendsto vs atTop (𝓝 u) := by
    have H := (cheegerHeat_continuousOn hfin h u 0 (show (0:ℝ) ∈ Ici 0 by simp)).tendsto.comp
      (tendsto_nhdsWithin_iff.mpr ⟨tendsto_one_div_add_atTop_nhds_zero_nat,Eventually.of_forall fun k => (hτ k).le⟩)
    simpa only [cheegerHeat_zero,one_apply_eq_self,Function.comp_def,vs,τ] using H
  have hex (k : ℕ) : ∃ f : X → ℝ,GloballyLipschitz f ∧ ∃ hf : MemLp f 2 m,dist (hf.toLp f) (vs k) < τ k := by
    obtain ⟨A,hA,-⟩ := cheegerHeat_deriv_at_positive hfin h u (hτ k)
    obtain ⟨f,hf,hf2,hd,-⟩ := cheegerEnergy_lt_approx hA.1 (hτ k)
    exact ⟨f,hf,hf2,hd⟩
  choose gs hgs hgs2 hdist using hex
  have hgT : Tendsto (fun k => (hgs2 k).toLp (gs k)) atTop (𝓝 u) := by
    apply Filter.Tendsto.congr_dist hvT
    exact squeeze_zero (fun _ => dist_nonneg) (fun k => by simpa only [dist_comm] using (hdist k).le) tendsto_one_div_add_atTop_nhds_zero_nat
  let fs (k : ℕ) (x : X) := realClip n (gs k x)
  have hfs (k : ℕ) : MemLp (fs k) 2 m := (realClip_lipschitz n).comp_memLp (realClip_zero n) (hgs2 k)
  refine ⟨fs,fun k => ⟨(hgs k).choose,by simpa only [one_mul,Function.comp_def,fs] using (realClip_lipschitz n).comp (hgs k).choose_spec⟩,
    fun k x => realClip_abs_le n (gs k x),hfs,?_⟩
  let T := (realClip_lipschitz n).compLp (μ := m) (p := 2) (realClip_zero n)
  have hTe : T u = u := by
    apply Lp.ext
    filter_upwards [(realClip_lipschitz n).coeFn_compLp (realClip_zero n) u,hu] with x hx hb
    simpa only [Function.comp_apply,realClip,min_eq_left (abs_le.mp hb).2,max_eq_right (abs_le.mp hb).1] using hx
  have hTk (k : ℕ) : T ((hgs2 k).toLp (gs k)) = (hfs k).toLp (fs k) := by
    apply Lp.ext
    filter_upwards [(realClip_lipschitz n).coeFn_compLp (realClip_zero n) ((hgs2 k).toLp (gs k)),
      (hgs2 k).coeFn_toLp,(hfs k).coeFn_toLp] with x hx hy hz
    rw [hx,Function.comp_apply,hy,hz]
  have H := ((realClip_lipschitz n).lipschitzWith_compLp (μ := m) (p := 2) (realClip_zero n)).continuous.tendsto u |>.comp hgT
  change Tendsto (fun k => T ((hgs2 k).toLp (gs k))) atTop (𝓝 (T u)) at H
  simpa only [hTe,hTk] using H
end WeakHessian

end
end InlinedFile141

end OAI
