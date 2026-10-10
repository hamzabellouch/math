import Mathlib

namespace OAI

section

noncomputable section
open Set Filter
open scoped Topology

namespace WeakMTWTransport
section RankOneCoercive
variable {E:Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma positive_bilinear_uniform_lower [FiniteDimensional ℝ E]
    {B:E →L[ℝ] E →L[ℝ] ℝ} (hB:∀d,d≠0 → 0 < B d d) :
    ∃c>0,∀d:E,c*‖d‖^2 ≤ B d d := by
  cases subsingleton_or_nontrivial E with
  | inl h =>
    let := h
    refine ⟨1,zero_lt_one,?_⟩
    intro d
    have :d=0:=Subsingleton.elim _ _
    simp [this]
  | inr h =>
    let := h
    have hs:(Metric.sphere (0:E) 1).Nonempty:=NormedSpace.sphere_nonempty.mpr (by norm_num)
    have hc:Continuous (fun d:E=>B d d):=B.continuous.clm_apply continuous_id
    obtain ⟨v,hv,hmin⟩:=(isCompact_sphere (0:E) 1).exists_isMinOn hs hc.continuousOn
    have hvn:‖v‖=1:=by simpa only [Metric.mem_sphere,dist_zero_right] using hv
    have hv0:v≠0:=by intro H; simp [H] at hvn
    refine ⟨B v v,hB v hv0,?_⟩
    intro d
    by_cases hd:d=0
    · simp [hd]
    have hn:0 < ‖d‖:=norm_pos_iff.mpr hd
    have hdmem:‖d‖⁻¹ • d∈Metric.sphere (0:E) 1:=by
      simp only [Metric.mem_sphere,dist_zero_right,norm_smul,Real.norm_eq_abs,
        abs_inv,abs_of_pos hn,inv_mul_cancel₀ hn.ne']
    have H:B v v ≤ B (‖d‖⁻¹ • d) (‖d‖⁻¹ • d):=hmin hdmem
    simp only [map_smul,_root_.smul_apply,smul_eq_mul] at H
    have H':B v v*‖d‖^2 ≤ (‖d‖⁻¹*(‖d‖⁻¹*B d d))*‖d‖^2:=
      mul_le_mul_of_nonneg_right H (sq_nonneg _)
    convert H' using 1; field_simp

end RankOneCoercive
end WeakMTWTransport

end
end

end OAI
