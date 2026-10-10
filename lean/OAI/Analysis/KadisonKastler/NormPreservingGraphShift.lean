import OAI.Analysis.KadisonKastler.IsometryGraphShift

namespace OAI

/-! # Remote graph shifts with exact preservation of the relevant vector norm -/

namespace KadisonKastler

open Filter
open scoped Topology

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {M : VonNeumannAlgebra H} {Ω : H}

namespace ModularConjugationData

variable (d : ModularConjugationData M Ω)

theorem exists_coisometry_test_shift (v : ℕ → Algebra M)
    (hv : ∀ n, v n*star (v n)=1)
    (ξ η : H) (t : ℂ)
    (hscale : Tendsto (fun n => (v n).val η-t • d.rightAction (v n) η) atTop (𝓝 0))
    (x : Algebra M) (T : H →L[ℂ] H)
    (hT : Tendsto (fun n => inner ℂ (d.rightAction (v n) (d.rightAction x ξ))
      (T (d.rightAction (v n) (d.rightAction x ξ)))) atTop
      (𝓝 (inner ℂ (d.rightAction x ξ) (T (d.rightAction x ξ)))))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ y : Algebra M,
      ‖y.val η-d.rightAction y ξ‖ < ‖t • x.val η-d.rightAction x ξ‖+ε ∧
      ‖d.rightAction y ξ‖=‖d.rightAction x ξ‖ ∧
      ‖inner ℂ (d.rightAction y ξ) (T (d.rightAction y ξ))-
        inner ℂ (d.rightAction x ξ) (T (d.rightAction x ξ))‖ < ε := by
  have herror : Tendsto (fun n => ‖x‖*‖(v n).val η-t • d.rightAction (v n) η‖)
      atTop (𝓝 0) := by
    simpa only [norm_zero,mul_zero] using hscale.norm.const_mul ‖x‖
  have htest := (hT.sub_const (inner ℂ (d.rightAction x ξ) (T (d.rightAction x ξ)))).norm
  simp only [sub_self,norm_zero] at htest
  obtain ⟨n,hn,hnt⟩ := ((herror.eventually (gt_mem_nhds hε)).and
    (htest.eventually (gt_mem_nhds hε))).exists
  refine ⟨x*v n,?_,?_,?_⟩
  · exact (d.coisometry_graph_shift_bound x (v n) (hv n) ξ η t).trans_lt (by linarith)
  · rw [d.rightAction_mul,mul_apply_eq_comp]
    exact d.rightAction_norm_map (v n) (hv n) _
  · simpa only [d.rightAction_mul,mul_apply_eq_comp] using hnt

theorem exists_isometry_test_shift (v : ℕ → Algebra M)
    (hv : ∀ n, v n*star (v n)=1)
    (ξ η : H) (t : ℂ)
    (hscale : Tendsto (fun n => t • (star (v n)).val ξ-d.rightAction (star (v n)) ξ)
      atTop (𝓝 0))
    (x : Algebra M) (T : H →L[ℂ] H)
    (hT : Tendsto (fun n => inner ℂ ((star (v n)).val (x.val η))
      (T ((star (v n)).val (x.val η)))) atTop
      (𝓝 (inner ℂ (x.val η) (T (x.val η)))))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ y : Algebra M,
      ‖y.val η-d.rightAction y ξ‖ < ‖x.val η-t • d.rightAction x ξ‖+ε ∧
      ‖y.val η‖=‖x.val η‖ ∧
      ‖inner ℂ (y.val η) (T (y.val η))-inner ℂ (x.val η) (T (x.val η))‖ < ε := by
  have herror : Tendsto (fun n => ‖x‖*‖t • (star (v n)).val ξ-
      d.rightAction (star (v n)) ξ‖) atTop (𝓝 0) := by
    simpa only [norm_zero,mul_zero] using hscale.norm.const_mul ‖x‖
  have htest := (hT.sub_const (inner ℂ (x.val η) (T (x.val η)))).norm
  simp only [sub_self,norm_zero] at htest
  obtain ⟨n,hn,hnt⟩ := ((herror.eventually (gt_mem_nhds hε)).and
    (htest.eventually (gt_mem_nhds hε))).exists
  refine ⟨star (v n)*x,?_,?_,?_⟩
  · exact (d.isometry_graph_shift_bound x (v n) (hv n) ξ η t).trans_lt (by linarith)
  · change ‖(star (v n)).val (x.val η)‖=_
    exact (coisometry_adjoint_isometry (v n) (hv n)).norm_map_of_map_zero (map_zero _) _
  · exact hnt

end ModularConjugationData

end

end KadisonKastler

end OAI
