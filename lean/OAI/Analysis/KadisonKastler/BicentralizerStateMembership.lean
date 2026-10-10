import OAI.Analysis.KadisonKastler.BicentralizerStateLimit
import OAI.Analysis.KadisonKastler.UnitaryStateCentrality

namespace OAI

/-! # The state-transport limit belongs to the target bicentralizer

A diagonal choice of comparing unitaries transfers each asymptotically
central unitary sequence to the source state. Faithfulness then extends
the reference-vector conclusion to the whole represented Hilbert space.
-/

namespace KadisonKastler

open Generator.Tracial Filter
open scoped Topology

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {M : VonNeumannAlgebra H}

theorem conjugate_commutator (a : Algebra M) (u v : unitary (Algebra M)) :
    (u.val*a*star u.val)*v.val-v.val*(u.val*a*star u.val)=
      u.val*(a*(star u.val*v.val*u.val)-(star u.val*v.val*u.val)*a)*star u.val := by
  let e := Unitary.conjStarAlgAut ℂ (Algebra M) u
  change e a*v.val-v.val*e a=e (a*e.symm v.val-e.symm v.val*a)
  rw [map_sub,map_mul,map_mul,e.apply_symm_apply]

theorem unitary_commutator_vector_difference_le (η : H) (a b : Algebra M)
    (v : unitary (Algebra M)) :
    ‖(a*v.val-v.val*a).val η‖ ≤ ‖(b*v.val-v.val*b).val η‖+
      ‖(a-b).val (v.val.val η)‖+‖(a-b).val η‖ := by
  have he : (a*v.val-v.val*a).val η=
      (b*v.val-v.val*b).val η+(a-b).val (v.val.val η)-v.val.val ((a-b).val η) := by
    simp only [AddSubgroupClass.coe_sub,MulMemClass.coe_mul,sub_apply,mul_apply_eq_comp]
    rw [map_sub]
    abel
  rw [he]
  calc
    _ ≤ ‖(b*v.val-v.val*b).val η+(a-b).val (v.val.val η)‖+
        ‖v.val.val ((a-b).val η)‖ := norm_sub_le _ _
    _ ≤ (‖(b*v.val-v.val*b).val η‖+‖(a-b).val (v.val.val η)‖)+
        ‖v.val.val ((a-b).val η)‖ := add_le_add (norm_add_le _ _) le_rfl
    _ = _ := by
      have hv := Unitary.norm_map (ambientAlgebraUnitary v) ((a-b).val η)
      change ‖v.val.val ((a-b).val η)‖=‖(a-b).val η‖ at hv
      rw [hv]

theorem stateBicentralizerMember_of_state_conjugate_limit (ξ η : H)
    (hη : Function.Injective (algebraVectorMap M η))
    (a b : Algebra M) (ha : stateBicentralizerMember ξ a)
    (u : ℕ → unitary (Algebra M))
    (hu : Tendsto (fun n =>
      ‖sandwichFunctional (vectorFunctional ξ) (u n).val-vectorFunctional η‖) atTop (𝓝 0))
    (hb : ∀ ζ : H, Tendsto (fun n => ((u n).val*a*star (u n).val).val ζ) atTop
      (𝓝 (b.val ζ))) : stateBicentralizerMember η b := by
  apply stateBicentralizerMember_of_unitary_reference_tests η hη b
  intro v hv
  let c (n : ℕ) : Algebra M := (u n).val*a*star (u n).val
  let r (n : ℕ) : ℝ := 1/((n : ℝ)+1)
  have hr : ∀ n, 0 < r n := fun n => by dsimp only [r]; positivity
  have hcz (ζ : H) : Tendsto (fun n => ‖(c n-b).val ζ‖) atTop (𝓝 0) := by
    change Tendsto (fun n => ‖(c n).val ζ-b.val ζ‖) atTop (𝓝 0)
    have h := (hb ζ).sub_const (b.val ζ) |>.norm
    simpa only [sub_self,norm_zero] using h
  have hchoice (n : ℕ) : ∃ k : ℕ,
      ‖sandwichFunctional (vectorFunctional ξ) (u k).val-vectorFunctional η‖ < r n ∧
      ‖(c k-b).val η‖ < r n ∧ ‖(c k-b).val ((v n).val.val η)‖ < r n := by
    exact ((hu.eventually (gt_mem_nhds (hr n))).and
      ((hcz η).eventually (gt_mem_nhds (hr n)) |>.and
        ((hcz ((v n).val.val η)).eventually (gt_mem_nhds (hr n))))).exists
  choose k hk using hchoice
  let w (n : ℕ) : unitary (Algebra M) := (star (u (k n)))*(v n)*(u (k n))
  have he : Tendsto (fun n =>
      ‖sandwichFunctional (vectorFunctional ξ) (u (k n)).val-vectorFunctional η‖)
      atTop (𝓝 0) :=
    squeeze_zero (fun _ => norm_nonneg _) (fun n => (hk n).1.le)
      tendsto_one_div_add_atTop_nhds_zero_nat
  have hw : Tendsto (fun n => ‖vectorStateCommutator ξ (w n).val‖) atTop (𝓝 0) := by
    apply squeeze_zero (fun _ => norm_nonneg _)
      (fun n => unitary_comparison_centrality ξ η (u (k n)) (v n))
    simpa only [mul_zero,add_zero] using hv.add (he.const_mul 2)
  have hc : Tendsto (fun n => ‖(a*(w n).val-(w n).val*a).val ξ‖) atTop (𝓝 0) := by
    simpa only [norm_zero] using
      ((stateBicentralizerMember_iff_unitary_tests ξ a).mp ha w hw ξ).norm
  have hbound (n : ℕ) : ‖a*(w n).val-(w n).val*a‖ ≤ 2*‖a‖ := by
    calc
      _ ≤ ‖a*(w n).val‖+‖(w n).val*a‖ := norm_sub_le _ _
      _ = 2*‖a‖ := by
        rw [CStarRing.norm_mul_coe_unitary,CStarRing.norm_coe_unitary_mul]
        ring
  have hsquare (n : ℕ) : ‖(c (k n)*(v n).val-(v n).val*c (k n)).val η‖^2 ≤
      ‖(a*(w n).val-(w n).val*a).val ξ‖^2+
      ‖sandwichFunctional (vectorFunctional ξ) (u (k n)).val-vectorFunctional η‖*(4*‖a‖^2) := by
    have h := conjugate_vector_norm_sq_le_state_distance ξ η (u (k n))
      (a*(w n).val-(w n).val*a)
    have heq := (conjugate_commutator a (u (k n)) (v n)).symm
    change (u (k n)).val*(a*(w n).val-(w n).val*a)*star (u (k n)).val=
      c (k n)*(v n).val-(v n).val*c (k n) at heq
    rw [heq] at h
    refine h.trans (add_le_add le_rfl (mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)))
    have hn := hbound n
    nlinarith only [hn,norm_nonneg (a*(w n).val-(w n).val*a),norm_nonneg a]
  have hs : Tendsto (fun n => ‖(c (k n)*(v n).val-(v n).val*c (k n)).val η‖^2)
      atTop (𝓝 0) := by
    apply squeeze_zero (fun _ => sq_nonneg _) hsquare
    simpa only [zero_pow (by decide : 2≠0),zero_mul,add_zero] using
      (hc.pow 2).add (he.mul_const (4*‖a‖^2))
  have hnorm : Tendsto (fun n => ‖(c (k n)*(v n).val-(v n).val*c (k n)).val η‖)
      atTop (𝓝 0) := by
    simpa only [Real.sqrt_sq (norm_nonneg _),Real.sqrt_zero] using hs.sqrt
  have hfinal (n : ℕ) : ‖(b*(v n).val-(v n).val*b).val η‖ ≤
      ‖(c (k n)*(v n).val-(v n).val*c (k n)).val η‖+2*r n := by
    have h := unitary_commutator_vector_difference_le η b (c (k n)) (v n)
    have he₁ : ‖(b-c (k n)).val η‖=‖(c (k n)-b).val η‖ := by
      change ‖b.val η-(c (k n)).val η‖=‖(c (k n)).val η-b.val η‖
      exact norm_sub_rev _ _
    have he₂ : ‖(b-c (k n)).val ((v n).val.val η)‖=
        ‖(c (k n)-b).val ((v n).val.val η)‖ := by
      change ‖b.val _-(c (k n)).val _‖=‖(c (k n)).val _-b.val _‖
      exact norm_sub_rev _ _
    rw [he₁,he₂] at h
    linarith [(hk n).2.1,(hk n).2.2]
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  apply squeeze_zero (fun _ => norm_nonneg _) hfinal
  simpa only [mul_zero,add_zero] using
    hnorm.add (tendsto_one_div_add_atTop_nhds_zero_nat.const_mul 2)

end

end KadisonKastler

end OAI
