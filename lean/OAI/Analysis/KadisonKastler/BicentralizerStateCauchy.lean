import OAI.Analysis.KadisonKastler.StateVectorNormComparison
import OAI.Analysis.KadisonKastler.StateBicentralizerLocal

namespace OAI

/-! # Comparing faithful states gives Cauchy conjugates of bicentralizer elements

Norm convergence of the conjugated states yields the convergence used
in canonical state transport.
-/

namespace KadisonKastler

open Generator.Tracial Filter
open scoped Topology

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {M : VonNeumannAlgebra H}

theorem conjugates_vector_difference_sq_le (ξ η : H) (a : Algebra M)
    (u v : unitary (Algebra M)) :
    ‖(u.val*a*star u.val-v.val*a*star v.val).val η‖^2 ≤
      ‖(a*((star u)*v).val-((star u)*v).val*a).val ξ‖^2+
      ‖sandwichFunctional (vectorFunctional ξ) v.val-vectorFunctional η‖*(4*‖a‖^2) := by
  let w : unitary (Algebra M) := (star v)*u
  let d : Algebra M := w.val*a*star w.val-a
  have hw : v.val*w.val=u.val := by
    change v.val*(star v.val*u.val)=u.val
    rw [← mul_assoc,v.property.2,one_mul]
  have hws : star w.val*star v.val=star u.val := by
    simpa only [star_mul] using congrArg star hw
  have he : v.val*d*star v.val=u.val*a*star u.val-v.val*a*star v.val := by
    calc
      _ = (v.val*w.val)*a*(star w.val*star v.val)-v.val*a*star v.val := by
        dsimp only [d]
        noncomm_ring
      _ = _ := by rw [hw,hws]
  have hd : d=w.val*(a*star w.val-star w.val*a) := by
    dsimp only [d]
    rw [mul_sub,← mul_assoc w.val (star w.val),w.property.2,one_mul]
    simp only [mul_assoc]
  have hv : ‖d.val ξ‖=‖(a*star w.val-star w.val*a).val ξ‖ := by
    rw [hd]
    exact Unitary.norm_map (ambientAlgebraUnitary w) _
  have hnorm : ‖d‖ ≤ 2*‖a‖ := by
    calc
      _ ≤ ‖w.val*a*star w.val‖+‖a‖ := norm_sub_le _ _
      _ = 2*‖a‖ := by
        change ‖w.val*a*(star w).val‖+‖a‖=2*‖a‖
        rw [CStarRing.norm_mul_coe_unitary,CStarRing.norm_coe_unitary_mul]
        ring
  have hb := conjugate_vector_norm_sq_le_state_distance ξ η v d
  rw [he,hv] at hb
  have hwstar : star w.val=((star u)*v).val := by
    change star (star v.val*u.val)=star u.val*v.val
    rw [star_mul,star_star]
  rw [hwstar] at hb
  refine hb.trans (add_le_add le_rfl (mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)))
  nlinarith only [hnorm,norm_nonneg d,norm_nonneg a]

theorem stateBicentralizerMember.conjugates_cauchy (ξ η : H)
    (hsep : Function.Injective (algebraVectorMap M ξ))
    (a : Algebra M) (ha : stateBicentralizerMember ξ a)
    (u : ℕ → unitary (Algebra M))
    (hu : Tendsto (fun n =>
      ‖sandwichFunctional (vectorFunctional ξ) (u n).val-vectorFunctional η‖) atTop (𝓝 0)) :
    CauchySeq (fun n => ((u n).val*a*star (u n).val).val η) := by
  apply Metric.cauchySeq_iff.mpr
  intro ε hε
  obtain ⟨δ,hδ,hlocal⟩ := (stateBicentralizerMember_iff_local_reference ξ hsep a).mp ha
    (ε/2) (half_pos hε)
  let r := min (δ/3) (ε^2/(8*(4*‖a‖^2+1)))
  have hr : 0 < r := lt_min (by positivity) (by positivity)
  obtain ⟨N,hN⟩ := eventually_atTop.mp (hu.eventually (gt_mem_nhds hr))
  refine ⟨N,fun n hn m hm => ?_⟩
  let v : unitary (Algebra M) := (star (u n))*(u m)
  have hv : ‖vectorStateCommutator ξ v.val‖ < δ := by
    have hb := unitary_state_transition_defect ξ η (u m) (u n)
    have hnr := hN n hn
    have hmr := hN m hm
    have hrδ : r ≤ δ/3 := min_le_left _ _
    change ‖vectorStateCommutator ξ (((star (u n))*(u m)).val)‖ < δ
    linarith
  have hc := hlocal v hv
  have hb := conjugates_vector_difference_sq_le ξ η a (u n) (u m)
  have hrε : r ≤ ε^2/(8*(4*‖a‖^2+1)) := min_le_right _ _
  have herr : ‖sandwichFunctional (vectorFunctional ξ) (u m).val-vectorFunctional η‖*
      (4*‖a‖^2+1) < ε^2/8 := by
    have hd : 0 < 8*(4*‖a‖^2+1) := by positivity
    have hx := (lt_div_iff₀ hd).mp ((hN m hm).trans_le hrε)
    nlinarith only [hx]
  have hcomm : ‖(a*v.val-v.val*a).val ξ‖^2 < ε^2/4 := by
    nlinarith only [hc,norm_nonneg ((a*v.val-v.val*a).val ξ)]
  have hd : ‖(((u n).val*a*star (u n).val).val η)-
      (((u m).val*a*star (u m).val).val η)‖^2 < ε^2 := by
    change ‖((u n).val*a*star (u n).val-(u m).val*a*star (u m).val).val η‖^2 < ε^2
    have hn0 : 0 ≤ ‖sandwichFunctional (vectorFunctional ξ) (u m).val-vectorFunctional η‖ :=
      norm_nonneg _
    change ‖(a*v.val-v.val*a).val ξ‖^2 < ε^2/4 at hcomm
    nlinarith only [hb,herr,hcomm,hn0,sq_pos_of_pos hε]
  rw [dist_eq_norm]
  nlinarith only [hd,hε,norm_nonneg
    ((((u n).val*a*star (u n).val).val η)-(((u m).val*a*star (u m).val).val η))]

end

end KadisonKastler

end OAI
