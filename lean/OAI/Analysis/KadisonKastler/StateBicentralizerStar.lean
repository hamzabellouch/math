import OAI.Analysis.KadisonKastler.StateBicentralizerAdjoint

namespace OAI

/-! # The state bicentralizer is closed under adjoints -/

namespace KadisonKastler

open Generator.Tracial Filter
open scoped Topology

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {M : VonNeumannAlgebra H}

theorem stateBicentralizerMember_star (ξ : H)
    (hsep : Function.Injective (algebraVectorMap M ξ)) (a : Algebra M)
    (ha : stateBicentralizerMember ξ a) : stateBicentralizerMember ξ (star a) := by
  apply (stateBicentralizerMember_iff_unitary_tests _ _).mpr
  intro u hu η
  let b (n : ℕ) : Algebra M := star (u n).val*a*(u n).val
  have hnorm (ζ : H) :
      Tendsto (fun n => ‖(b n-a).val ζ‖) atTop (𝓝 0) := by
    have ht := ((stateBicentralizerMember_iff_unitary_tests _ _).mp ha u hu ζ).norm
    have he (n : ℕ) : ‖(b n-a).val ζ‖=‖(a*(u n).val-(u n).val*a).val ζ‖ := by
      change ‖(b n).val ζ-a.val ζ‖=_
      rw [← unitary_commutator_vector_norm_eq ζ a (u n)]
      change ‖(u n).val.val (a.val ζ)-a.val ((u n).val.val ζ)‖=
        ‖a.val ((u n).val.val ζ)-(u n).val.val (a.val ζ)‖
      exact norm_sub_rev _ _
    simpa only [he,norm_zero] using ht
  have hr : Tendsto (fun n => ‖vectorStateCommutator ξ (u n).val‖*‖a‖^2+
      2*‖ξ‖*‖(b n-a).val ((star a).val ξ)‖) atTop (𝓝 0) := by
    simpa only [zero_mul,mul_zero,add_zero] using
      (hu.mul_const (‖a‖^2)).add ((hnorm ((star a).val ξ)).const_mul (2*‖ξ‖))
  have hsq : Tendsto (fun n => ‖(star (b n)-star a).val ξ‖^2) atTop (𝓝 0) :=
    squeeze_zero (fun _ => sq_nonneg _)
      (fun n => stateConjugate_adjoint_difference_sq_le ξ a (u n)) hr
  have hs : Tendsto (fun n => ‖(star (b n)-star a).val ξ‖) atTop (𝓝 0) := by
    simpa only [Real.sqrt_sq (norm_nonneg _),Real.sqrt_zero] using hsq.sqrt
  let T (n : ℕ) : Algebra M := star a*(u n).val-(u n).val*star a
  have he (n : ℕ) : ‖(T n).val ξ‖=‖(star (b n)-star a).val ξ‖ := by
    calc
      _ = ‖((u n).val*star a-star a*(u n).val).val ξ‖ := by
        change ‖(star a).val ((u n).val.val ξ)-(u n).val.val ((star a).val ξ)‖=
          ‖(u n).val.val ((star a).val ξ)-(star a).val ((u n).val.val ξ)‖
        exact norm_sub_rev _ _
      _ = ‖(star (u n).val*star a*(u n).val).val ξ-(star a).val ξ‖ :=
        unitary_commutator_vector_norm_eq ξ (star a) (u n)
      _ = _ := by simp only [b,star_mul,star_star,mul_assoc]; rfl
  have hTξ : Tendsto (fun n => (T n).val ξ) atTop (𝓝 0) := by
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    simpa only [he] using hs
  have hT : ∀ n, ‖T n‖ ≤ 2*‖a‖ := by
    intro n
    have hun := norm_unitary_le_one (u n)
    calc
      _ ≤ ‖star a*(u n).val‖+‖(u n).val*star a‖ := norm_sub_le _ _
      _ ≤ ‖a‖*‖(u n).val‖+‖(u n).val‖*‖a‖ := by
        simpa only [norm_star] using add_le_add
          (norm_mul_le (star a) (u n).val) (norm_mul_le (u n).val (star a))
      _ ≤ 2*‖a‖ := by nlinarith only [hun,norm_nonneg a]
  exact algebra_strong_tendsto_of_reference ξ (commutant_cyclic_of_separating_reference ξ hsep)
    T (2*‖a‖) (by positivity) hT hTξ η

end

end KadisonKastler

end OAI
