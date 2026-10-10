import Mathlib
import OAI.Analysis.BiholderTransport.Contact.Subgradient

namespace OAI

noncomputable section

open Set MeasureTheory Manifold Bundle
open scoped ContDiff Manifold ENNReal NNReal Topology

open Set Filter
open scoped Topology NNReal

open Set Filter
open scoped Topology

namespace WeakMTWTransport
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma HasQuadraticExpansion.hasFDerivAt {f : E → ℝ} {p : E} {A : E →L[ℝ] E}
    (hexp : HasQuadraticExpansion f p A) : HasFDerivAt f ((innerSL ℝ) p) 0 := by
  obtain ⟨d,hd,hbound⟩ := hexp 1 zero_lt_one
  let K : ℝ := 1+‖A‖/2
  have hK : 0 < K := by dsimp [K]; positivity
  rw [hasFDerivAt_iff_isLittleO_nhds_zero,Asymptotics.isLittleO_iff]
  intro c hc
  have hpos : 0 < min d (c/K) := by positivity
  filter_upwards [Metric.ball_mem_nhds (0:E) hpos] with h hh
  have hn : ‖h‖ < min d (c/K) := by simpa only [Metric.mem_ball,dist_zero_right] using hh
  have hb := hbound h (lt_of_lt_of_le hn (min_le_left _ _))
  have hA : |inner ℝ (A h) h| ≤ ‖A‖*‖h‖^2 := by
    calc
      _ ≤ ‖A h‖*‖h‖ := abs_real_inner_le_norm _ _
      _ ≤ (‖A‖*‖h‖)*‖h‖ := mul_le_mul_of_nonneg_right (A.le_opNorm h) (norm_nonneg _)
      _ = _ := by ring
  have heq : f h-f 0-inner ℝ p h =
      (f h-quadraticTaylor (f 0) p A h)+inner ℝ (A h) h/2 := by
    simp only [quadraticTaylor]
    ring
  have hb' : |f h-f 0-inner ℝ p h| ≤ K*‖h‖^2 := by
    rw [heq]
    have ht := abs_add_le (f h-quadraticTaylor (f 0) p A h) (inner ℝ (A h) h/2)
    rw [abs_div,abs_of_pos (by norm_num : (0:ℝ)<2)] at ht
    dsimp [K]
    nlinarith
  have hmul : ‖h‖*K ≤ c := (le_div_iff₀ hK).mp (le_of_lt (lt_of_lt_of_le hn (min_le_right _ _)))
  have hbc : K*‖h‖^2 ≤ c*‖h‖ := by
    nlinarith [mul_le_mul_of_nonneg_right hmul (norm_nonneg h)]
  simpa only [zero_add,innerSL_apply_apply,Real.norm_eq_abs] using hb'.trans hbc

lemma HasQuadraticExpansion.hessian_le_of_upper_support {f : E → ℝ} {p : E}
    {A : E →L[ℝ] E} (hexp : HasQuadraticExpansion f p A) {eta R : ℝ}
    (hR : 0 < R)
    (hu : ∀ h : E, ‖h‖ < R →
      f h ≤ f 0+inner ℝ p h+eta/2*‖h‖^2) :
    ∀ e : E, inner ℝ (A e) e ≤ eta*‖e‖^2 := by
  intro e
  have hbound (eps : ℝ) (heps : 0 < eps) :
      inner ℝ (A e) e ≤ (eta+2*eps)*‖e‖^2 := by
    obtain ⟨d,hd,hrem⟩ := hexp eps heps
    let t : ℝ := min R d / (2*(‖e‖+1))
    have ht : 0 < t := by dsimp [t]; positivity
    have hteq : t*(2*(‖e‖+1)) = min R d :=
      div_mul_cancel₀ _ (by positivity)
    have htn : t*‖e‖ < min R d := by nlinarith [norm_nonneg e]
    have hnorm : ‖t • e‖ = t*‖e‖ := norm_smul_of_nonneg ht.le _
    have hi := hu (t • e) (by rw [hnorm]; exact lt_of_lt_of_le htn (min_le_left _ _))
    have hr := (abs_le.mp (hrem (t • e) (by
      rw [hnorm]; exact lt_of_lt_of_le htn (min_le_right _ _)))).1
    simp only [quadraticTaylor,map_smul,real_inner_smul_left,real_inner_smul_right,hnorm] at hr hi
    have hscale : t^2 * inner ℝ (A e) e ≤ t^2 * ((eta+2*eps)*‖e‖^2) := by
      nlinarith
    nlinarith [sq_pos_of_pos ht]
  have hcl : (0:ℝ) ∈ closure (Ioo 0 1) := by
    rw [closure_Ioo (by norm_num : (0:ℝ) ≠ 1)]
    exact ⟨le_rfl,zero_le_one⟩
  have hc : Continuous (fun eps : ℝ => (eta+2*eps)*‖e‖^2) := by fun_prop
  have hh := ContinuousWithinAt.closure_le hcl
    (continuousWithinAt_const (b := inner ℝ (A e) e)) hc.continuousWithinAt
    (fun eps heps => hbound eps heps.1)
  simpa only [mul_zero,add_zero] using hh

end WeakMTWTransport

end

end OAI
