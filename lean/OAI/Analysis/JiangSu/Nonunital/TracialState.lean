import Mathlib
import OAI.Analysis.TracialSplitting.PreparedBlocks
import OAI.Analysis.JiangSu.Model

namespace OAI

noncomputable section
namespace NonunitalGamma
open Filter Topology
open scoped ComplexOrder InnerProductSpace

variable {A : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

@[simp] lemma unitizedFunctional_inr (f : A →ₚ[ℂ] ℂ)
    (hf : ‖positiveFunctionalCLM f‖ ≤ 1) (a : A) :
    unitizedFunctional f hf (Unitization.inr a)=f a := by
  change 0+f a=f a
  exact zero_add _

end NonunitalGamma

namespace NonunitalGamma
open Filter Topology
open scoped ComplexOrder

variable {A : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

lemma NormalizedTrace.exists_positive_trace_gt (τ : NormalizedTrace A)
    {c : ℝ} (hc0 : 0 < c) (hc1 : c < 1) :
    ∃ b : A, 0 ≤ b ∧ ‖b‖ < 1 ∧ c < (τ.functional b).re := by
  have hsc : Real.sqrt c < 1 := (Real.sqrt_lt' zero_lt_one).mpr (by simpa using hc1)
  obtain ⟨x,hx⟩ : ∃ x : A, Real.sqrt c * ‖x‖ < ‖τ.functional x‖ := by
    by_contra h
    push Not at h
    have hn := (positiveFunctionalCLM τ.functional).opNorm_le_bound (Real.sqrt_nonneg c) h
    rw [τ.norm_one] at hn
    linarith
  have hsc0 : 0 < Real.sqrt c := Real.sqrt_pos.mpr hc0
  have hratio : ‖x‖ < ‖τ.functional x‖ / Real.sqrt c := by
    exact (lt_div_iff₀ hsc0).mpr (by simpa only [mul_comm] using hx)
  obtain ⟨r,hrx,hrr⟩ := exists_between hratio
  have hr0 : 0 < r := (norm_nonneg x).trans_lt hrx
  let y : A := r⁻¹ • x
  have hyn : ‖y‖ < 1 := by
    dsimp [y]
    rw [norm_smul,Real.norm_of_nonneg (inv_nonneg.mpr hr0.le)]
    exact (inv_mul_lt_one₀ hr0).mpr hrx
  have hfy : Real.sqrt c < ‖τ.functional y‖ := by
    dsimp [y]
    rw [τ.functional.map_smul_of_tower,norm_smul,Real.norm_of_nonneg (inv_nonneg.mpr hr0.le)]
    have h : r * Real.sqrt c < ‖τ.functional x‖ := (lt_div_iff₀ hsc0).mp hrr
    exact (lt_inv_mul_iff₀ hr0).mpr h
  refine ⟨star y*y,star_mul_self_nonneg y,?_,?_⟩
  · rw [CStarRing.norm_star_mul_self]
    nlinarith [norm_nonneg y]
  · have h := positiveFunctional_norm_sq_le τ.functional τ.norm_one.le y
    nlinarith [Real.sq_sqrt hc0.le,Real.sqrt_nonneg c]

lemma NormalizedTrace.approximateUnit_value_re (τ : NormalizedTrace A) :
    Tendsto (fun e : A => (τ.functional e).re) (CStarAlgebra.approximateUnit A) (𝓝 1) := by
  apply tendsto_order.mpr
  constructor
  · intro a ha
    obtain ⟨c,hac,hc1⟩ := exists_between (max_lt ha (by norm_num : (0:ℝ)<1))
    have hc0 : 0 < c := (le_max_right a 0).trans_lt hac
    obtain ⟨b,hb,hbn,hbt⟩ := τ.exists_positive_trace_gt hc0 hc1
    apply (CStarAlgebra.hasBasis_approximateUnit A).eventually_iff.mpr
    refine ⟨b,⟨hb,hbn⟩,?_⟩
    intro e he
    have hbe := τ.functional.monotone he.1
    exact ((le_max_left a 0).trans_lt hac).trans (hbt.trans_le hbe.1)
  · intro a ha
    filter_upwards [(CStarAlgebra.increasingApproximateUnit A).eventually_norm] with e hen
    have h := (positiveFunctionalCLM τ.functional).le_opNorm e
    rw [τ.norm_one,one_mul] at h
    exact ((Complex.re_le_norm _).trans (h.trans hen)).trans_lt ha

lemma NormalizedTrace.approximateUnit_value (τ : NormalizedTrace A) :
    Tendsto τ.functional (CStarAlgebra.approximateUnit A) (𝓝 1) := by
  have h := Complex.continuous_ofReal.tendsto 1 |>.comp τ.approximateUnit_value_re
  have heq : τ.functional =ᶠ[CStarAlgebra.approximateUnit A]
      (fun e : A => ((τ.functional e).re : ℂ)) := by
    filter_upwards [(CStarAlgebra.increasingApproximateUnit A).eventually_nonneg] with e he
    apply Complex.ext
    · rfl
    · exact (Complex.nonneg_iff.mp (τ.functional.map_nonneg he)).2.symm
  exact Tendsto.congr' heq.symm (by simpa only [Function.comp_def,Complex.ofReal_one] using h)

end NonunitalGamma

end

end OAI
