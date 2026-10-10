import OAI.Analysis.KadisonKastler.CoisometryShiftConvergence

namespace OAI

/-! # The adjoint isometry step in the modular graph shift

The adjoints of the constructed coisometries supply the positive-eigenvalue
case of Marrakchi's Lemma 4.2.
-/

namespace KadisonKastler

open Filter
open scoped Topology

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H] {M : VonNeumannAlgebra H} {Ω : H}

theorem coisometry_adjoint_isometry (v : Algebra M) (hv : v*star v=1) :
    Isometry (star v.val : H →L[ℂ] H) := by
  apply (star v.val).isometry_iff_adjoint_comp_self.mpr
  change star (star v.val)*star v.val=1
  rw [star_star]
  exact congrArg (fun a : Algebra M => a.val) hv

namespace ModularConjugationData

variable (d : ModularConjugationData M Ω)

theorem isometry_graph_shift_identity (x v : Algebra M) (ξ η : H) (t : ℂ) :
    (star v*x).val η-d.rightAction (star v*x) ξ =
      (star v).val (x.val η-t • d.rightAction x ξ) +
        d.rightAction x (t • (star v).val ξ-d.rightAction (star v) ξ) := by
  rw [d.rightAction_mul]
  change (star v).val (x.val η)-d.rightAction x (d.rightAction (star v) ξ)=_
  have hc := congrArg (fun T : H →L[ℂ] H => T ξ) (d.rightAction_commute (star v) x)
  change (star v).val (d.rightAction x ξ)=d.rightAction x ((star v).val ξ) at hc
  rw [map_sub,map_smul,map_sub,map_smul,hc]
  abel

theorem isometry_graph_shift_bound (x v : Algebra M) (hv : v*star v=1)
    (ξ η : H) (t : ℂ) :
    ‖(star v*x).val η-d.rightAction (star v*x) ξ‖ ≤
      ‖x.val η-t • d.rightAction x ξ‖ +
        ‖x‖*‖t • (star v).val ξ-d.rightAction (star v) ξ‖ := by
  rw [d.isometry_graph_shift_identity]
  have hi := (coisometry_adjoint_isometry v hv).norm_map_of_map_zero (map_zero _)
    (x.val η-t • d.rightAction x ξ)
  exact (norm_add_le _ _).trans (add_le_add (le_of_eq hi)
    (((d.rightAction x).le_opNorm _).trans_eq (by rw [d.rightAction_norm])))

theorem isometry_coefficient_identity (v a b : Algebra M) (ζ : H) :
    inner ℂ ((star v).val ζ) ((a.val*d.rightAction b) ((star v).val ζ)) =
      inner ℂ ζ (((v*a*star v).val*d.rightAction b) ζ) := by
  rw [← ContinuousLinearMap.adjoint_inner_right]
  change inner ℂ ζ ((star (star v.val)*(a.val*d.rightAction b)*star v.val) ζ)=_
  rw [star_star]
  have hc := d.rightAction_commute (star v) b
  change star v.val*d.rightAction b=d.rightAction b*star v.val at hc
  have he : v.val*(a.val*d.rightAction b)*star v.val =
      (v*a*star v).val*d.rightAction b := by
    change v.val*(a.val*d.rightAction b)*star v.val =
      (v.val*a.val*star v.val)*d.rightAction b
    calc
      _ = v.val*a.val*(d.rightAction b*star v.val) := by simp only [mul_assoc]
      _ = v.val*a.val*(star v.val*d.rightAction b) :=
        congrArg (fun A : H →L[ℂ] H => v.val*a.val*A) hc.symm
      _ = _ := by simp only [mul_assoc]
  rw [he]

theorem isometry_coefficient_tendsto (v : ℕ → Algebra M)
    (hconv : ∀ (a : Algebra M) (η : H),
      Tendsto (fun n => (v n*a*star (v n)).val η) atTop (𝓝 (a.val η)))
    (a b : Algebra M) (ζ : H) :
    Tendsto (fun n => inner ℂ ((star (v n)).val ζ)
      ((a.val*d.rightAction b) ((star (v n)).val ζ))) atTop
      (𝓝 (inner ℂ ζ ((a.val*d.rightAction b) ζ))) := by
  have ht := hconv a (d.rightAction b ζ)
  have hi := (tendsto_const_nhds (x := ζ)).inner (𝕜 := ℂ) ht
  have heq : (fun n => inner ℂ ((star (v n)).val ζ)
      ((a.val*d.rightAction b) ((star (v n)).val ζ))) =
      (fun n => inner ℂ ζ (((v n*a*star (v n)).val*d.rightAction b) ζ)) :=
    funext (fun n => d.isometry_coefficient_identity (v n) a b ζ)
  rw [heq]
  simpa only [Function.comp_def,mul_apply_eq_comp] using hi

theorem exists_isometry_graph_shift (v : ℕ → Algebra M)
    (hv : ∀ n, v n*star (v n)=1)
    (hconv : ∀ (a : Algebra M) (η : H),
      Tendsto (fun n => (v n*a*star (v n)).val η) atTop (𝓝 (a.val η)))
    (ξ η : H) (t : ℂ)
    (hscale : Tendsto (fun n => t • (star (v n)).val ξ-d.rightAction (star (v n)) ξ)
      atTop (𝓝 0))
    (x : Algebra M) (F : Finset (Algebra M × Algebra M)) {ε : ℝ} (hε : 0 < ε) :
    ∃ y : Algebra M,
      ‖y.val η-d.rightAction y ξ‖ < ‖x.val η-t • d.rightAction x ξ‖+ε ∧
      ∀ p ∈ F,
        ‖inner ℂ (y.val η) ((p.1.val*d.rightAction p.2) (y.val η))-
          inner ℂ (x.val η) ((p.1.val*d.rightAction p.2) (x.val η))‖ < ε := by
  classical
  have herror : Tendsto (fun n => ‖x‖*‖t • (star (v n)).val ξ-
      d.rightAction (star (v n)) ξ‖) atTop (𝓝 0) := by
    simpa only [norm_zero,mul_zero] using hscale.norm.const_mul ‖x‖
  have hF : ∀ᶠ n in atTop, ∀ p ∈ F,
      ‖inner ℂ ((star (v n)).val (x.val η))
          ((p.1.val*d.rightAction p.2) ((star (v n)).val (x.val η)))-
        inner ℂ (x.val η) ((p.1.val*d.rightAction p.2) (x.val η))‖ < ε := by
    apply (eventually_all_finset F).mpr
    intro p hp
    have ht := ((d.isometry_coefficient_tendsto v hconv p.1 p.2 (x.val η)).sub_const
      (inner ℂ (x.val η) ((p.1.val*d.rightAction p.2) (x.val η)))).norm
    have ht' : Tendsto (fun n => ‖inner ℂ ((star (v n)).val (x.val η))
        ((p.1.val*d.rightAction p.2) ((star (v n)).val (x.val η)))-
      inner ℂ (x.val η) ((p.1.val*d.rightAction p.2) (x.val η))‖) atTop (𝓝 0) := by
      simpa only [sub_self,norm_zero] using ht
    exact ht'.eventually (gt_mem_nhds hε)
  obtain ⟨n,hn,hFn⟩ := ((herror.eventually (gt_mem_nhds hε)).and hF).exists
  refine ⟨star (v n)*x,?_,?_⟩
  · exact (d.isometry_graph_shift_bound x (v n) (hv n) ξ η t).trans_lt (by linarith)
  · intro p hp
    simpa only [MulMemClass.coe_mul,mul_apply_eq_comp] using hFn p hp

end ModularConjugationData

end

end KadisonKastler

end OAI
