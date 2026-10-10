import OAI.Analysis.KadisonKastler.ModularRightAction

namespace OAI

/-! # The coisometry step in the modular graph shift

These are the bounded identities underlying the negative-eigenvalue case
of Marrakchi, arXiv:1811.10253v2, Lemma 4.2. The identities require neither spectral approximation nor state decomposition.
-/

namespace KadisonKastler

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H] {M : VonNeumannAlgebra H} {Ω : H}

namespace ModularConjugationData

variable (d : ModularConjugationData M Ω)

theorem coisometry_graph_shift_identity (x v : Algebra M) (ξ η : H) (t : ℂ) :
    (x*v).val η-d.rightAction (x*v) ξ =
      x.val (v.val η-t • d.rightAction v η) +
        d.rightAction v (t • x.val η-d.rightAction x ξ) := by
  rw [d.rightAction_mul]
  change x.val (v.val η) - d.rightAction v (d.rightAction x ξ) = _
  have hc := congrArg (fun T : H →L[ℂ] H => T η) (d.rightAction_commute x v)
  change x.val (d.rightAction v η)=d.rightAction v (x.val η) at hc
  rw [map_sub,map_smul,map_sub,map_smul,hc]
  abel

theorem coisometry_graph_shift_bound (x v : Algebra M) (hv : v*star v=1)
    (ξ η : H) (t : ℂ) :
    ‖(x*v).val η-d.rightAction (x*v) ξ‖ ≤
      ‖x‖ * ‖v.val η-t • d.rightAction v η‖ +
        ‖t • x.val η-d.rightAction x ξ‖ := by
  rw [d.coisometry_graph_shift_identity]
  exact (norm_add_le _ _).trans (add_le_add (x.val.le_opNorm _)
    (le_of_eq (d.rightAction_norm_map v hv _)))

theorem coisometry_coefficient_identity (v a b : Algebra M) (ζ : H) :
    inner ℂ (d.rightAction v ζ) ((a.val*d.rightAction b) (d.rightAction v ζ)) =
      inner ℂ ζ ((a.val*d.rightAction (v*b*star v)) ζ) := by
  rw [← ContinuousLinearMap.adjoint_inner_right]
  change inner ℂ ζ ((star (d.rightAction v)*(a.val*d.rightAction b)*d.rightAction v) ζ) = _
  have he : star (d.rightAction v)*(a.val*d.rightAction b)*d.rightAction v =
      a.val*d.rightAction (v*b*star v) := by
    rw [d.rightAction_mul,d.rightAction_mul,d.rightAction_star]
    have hc := d.rightAction_commute a (star v)
    rw [d.rightAction_star] at hc
    calc
      _ = (star (d.rightAction v)*a.val)*(d.rightAction b*d.rightAction v) := by
        simp only [mul_assoc]
      _ = (a.val*star (d.rightAction v))*(d.rightAction b*d.rightAction v) := by rw [hc]
      _ = _ := by simp only [mul_assoc]
  rw [he]

end ModularConjugationData

end

end KadisonKastler

end OAI
