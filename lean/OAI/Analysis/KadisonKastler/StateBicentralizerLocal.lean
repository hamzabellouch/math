import OAI.Analysis.KadisonKastler.StateBicentralizerAlgebra

namespace OAI

/-! # Uniform reference-vector tests for the state bicentralizer

Faithfulness allows the reference-vector test to extend to every vector.
The sequential condition is then equivalent to a uniform estimate for
unitaries with sufficiently small state commutator.
-/

namespace KadisonKastler

open Filter
open scoped Topology

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {M : VonNeumannAlgebra H}

theorem stateBicentralizerMember_of_unitary_reference_tests (ξ : H)
    (hsep : Function.Injective (algebraVectorMap M ξ)) (a : Algebra M)
    (ha : ∀ u : ℕ → unitary (Algebra M),
      Tendsto (fun n => ‖vectorStateCommutator ξ (u n).val‖) atTop (𝓝 0) →
      Tendsto (fun n => (a*(u n).val-(u n).val*a).val ξ) atTop (𝓝 0)) :
    stateBicentralizerMember ξ a := by
  apply (stateBicentralizerMember_iff_unitary_tests ξ a).mpr
  intro u hu η
  let T (n : ℕ) : Algebra M := a*(u n).val-(u n).val*a
  have hT : ∀ n, ‖T n‖ ≤ 2*‖a‖ := by
    intro n
    have hun := norm_unitary_le_one (u n)
    calc
      _ ≤ ‖a*(u n).val‖+‖(u n).val*a‖ := norm_sub_le _ _
      _ ≤ ‖a‖*‖(u n).val‖+‖(u n).val‖*‖a‖ :=
        add_le_add (norm_mul_le _ _) (norm_mul_le _ _)
      _ ≤ 2*‖a‖ := by nlinarith only [hun,norm_nonneg a]
  exact algebra_strong_tendsto_of_reference ξ
    (commutant_cyclic_of_separating_reference ξ hsep) T (2*‖a‖)
    (by positivity) hT (ha u hu) η

theorem stateBicentralizerMember_iff_local_reference (ξ : H)
    (hsep : Function.Injective (algebraVectorMap M ξ)) (a : Algebra M) :
    stateBicentralizerMember ξ a ↔
      ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
        ∀ u : unitary (Algebra M), ‖vectorStateCommutator ξ u.val‖ < δ →
          ‖(a*u.val-u.val*a).val ξ‖ < ε := by
  constructor
  · intro ha ε hε
    by_contra h
    push Not at h
    choose u hu using fun n : ℕ => h (1/((n : ℝ)+1)) (by positivity)
    have hc : Tendsto (fun n => ‖vectorStateCommutator ξ (u n).val‖)
        atTop (𝓝 0) :=
      squeeze_zero (fun _ => norm_nonneg _) (fun n => (hu n).1.le)
        tendsto_one_div_add_atTop_nhds_zero_nat
    have ht := ((stateBicentralizerMember_iff_unitary_tests ξ a).mp ha u hc ξ).norm
    rw [norm_zero] at ht
    obtain ⟨n,hn⟩ := eventually_atTop.mp (ht.eventually (gt_mem_nhds hε))
    exact (not_lt_of_ge (hu n).2) (hn n le_rfl)
  · intro ha
    apply stateBicentralizerMember_of_unitary_reference_tests ξ hsep a
    intro u hu
    apply Metric.tendsto_nhds.mpr
    intro ε hε
    obtain ⟨δ,hδ,hd⟩ := ha ε hε
    filter_upwards [hu.eventually (gt_mem_nhds hδ)] with n hn
    simpa only [dist_zero_right] using hd (u n) hn

end

end KadisonKastler

end OAI
