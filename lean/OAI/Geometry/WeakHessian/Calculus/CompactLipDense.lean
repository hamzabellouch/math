import Mathlib
import OAI.Geometry.WeakHessian.Model
import OAI.Geometry.WeakHessian.Calculus.CompactThickenedIndicator

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile155
noncomputable section
namespace WeakHessian
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal InnerProductSpace

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable [CompleteSpace X] [ProperSpace X] [TopologicalSpace.SeparableSpace X] {m : Measure X}

def compactLipLp (m : Measure X) : Submodule ℝ (Lp ℝ 2 m) where
  carrier := {u | ∃ f : X → ℝ,GloballyLipschitz f ∧ HasCompactSupport f ∧ f =ᵐ[m] u}
  zero_mem' := ⟨0,⟨0,LipschitzWith.const 0⟩,HasCompactSupport.zero,(Lp.coeFn_zero ℝ 2 m).symm⟩
  add_mem' := by
    rintro u v ⟨f,⟨L,hf⟩,hfc,hfe⟩ ⟨g,⟨T,hg⟩,hgc,hge⟩
    refine ⟨f+g,⟨L+T,hf.add hg⟩,hfc.add hgc,?_⟩
    filter_upwards [hfe,hge,Lp.coeFn_add u v] with x hx hy hz
    simpa only [Pi.add_apply,hx,hy] using hz.symm
  smul_mem' := by
    rintro a u ⟨f,⟨lip,hf⟩,hfc,hfe⟩
    have hmul : GloballyLipschitz (fun x => a*f x) := by
      refine ⟨‖a‖₊ * lip, LipschitzWith.of_dist_le_mul fun left right => ?_⟩
      simpa only [Real.dist_eq, ← mul_sub, abs_mul, NNReal.coe_mul, coe_nnnorm,
        Real.norm_eq_abs, mul_assoc] using
        mul_le_mul_of_nonneg_left (hf.dist_le_mul left right) (abs_nonneg a)
    refine ⟨fun x => a*f x,hmul,hfc.mul_left,?_⟩
    filter_upwards [hfe,Lp.coeFn_smul a u] with x hx hy
    simpa only [Pi.smul_apply,smul_eq_mul,hx] using hy.symm

lemma compactLipLp_dense (hfin : FiniteOnBoundedSets m) :
    (compactLipLp m).topologicalClosure = ⊤ := by
  let : IsLocallyFiniteMeasure m := ⟨fun x => ⟨Metric.ball x 1,Metric.ball_mem_nhds x zero_lt_one,
    hfin _ Metric.isBounded_ball⟩⟩
  apply Submodule.topologicalClosure_eq_top_iff.mpr
  apply le_antisymm _ bot_le
  intro H hH
  change H=0
  have he : (H:X → ℝ) =ᵐ[m] 0 := by
    apply WeakHessianCalculus.ae_eq_zero_of_integral_lipschitz_compact
      ((Lp.memLp H).locallyIntegrable (by norm_num))
    intro f hfc hf
    have hf2 : MemLp f 2 m := hf.choose_spec.continuous.memLp_of_hasCompactSupport hfc
    have hm : hf2.toLp f ∈ compactLipLp m := ⟨f,hf,hfc,hf2.coeFn_toLp.symm⟩
    have hz := Submodule.inner_left_of_mem_orthogonal hm hH
    rw [L2.inner_def] at hz
    convert hz using 1
    apply integral_congr_ae
    filter_upwards [hf2.coeFn_toLp] with x hx
    simp only [hx,RCLike.inner_apply,conj_trivial,mul_comm]
  apply Lp.ext
  exact he.trans (Lp.coeFn_zero ℝ 2 m).symm

lemma exists_compactLip_L2_approx (hfin : FiniteOnBoundedSets m) (u : Lp ℝ 2 m) :
    ∃ us : ℕ → Lp ℝ 2 m,(∀ n,us n ∈ compactLipLp m) ∧ Tendsto us atTop (𝓝 u) := by
  have hcl : u ∈ closure (compactLipLp m : Set (Lp ℝ 2 m)) := by
    change u ∈ (compactLipLp m).topologicalClosure
    rw [compactLipLp_dense hfin]
    trivial
  exact mem_closure_iff_seq_limit.mp hcl
end WeakHessian

end
end InlinedFile155

end OAI
