import OAI.Analysis.KadisonKastler.BicentralizerExpectation

namespace OAI

/-! # The bicentralizer retraction on the faithful Hilbert-space vector

It agrees with the orthogonal projection onto the bicentralizer orbit.
In particular it is contractive for the reference-vector norm as well as
the operator norm.
-/

namespace KadisonKastler

open Generator Generator.Tracial

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {M : VonNeumannAlgebra H}

theorem bicentralizerProjection_vector_eq (ξ : H)
    (hsep : Function.Injective (algebraVectorMap M ξ)) (a : Algebra M) :
    (bicentralizerProjectionCLM ξ hsep a).val ξ=
      (vectorOrbitClosure (stateBicentralizerVonNeumann ξ hsep).toStarSubalgebra ξ).starProjection
        (a.val ξ) := by
  let B := stateBicentralizerVonNeumann ξ hsep
  let C := vectorOrbitClosure B.toStarSubalgebra ξ
  let E := bicentralizerProjectionCLM ξ hsep
  have hEa : (E a).val ∈ B := (mem_stateBicentralizerVonNeumann ξ hsep _).mpr
    (bicentralizerProjection_mem ξ hsep a)
  have hm : (E a).val ξ ∈ C := Submodule.le_topologicalClosure _ ⟨⟨(E a).val,hEa⟩,rfl⟩
  have hz : ∀ w ∈ C, inner ℂ (a.val ξ-(E a).val ξ) w=0 := by
    have hclosed : IsClosed {w : H | inner ℂ (a.val ξ-(E a).val ξ) w=0} :=
      isClosed_eq (continuous_const.inner continuous_id) continuous_const
    have hsubset : (C : Set H) ⊆ {w | inner ℂ (a.val ξ-(E a).val ξ) w=0} := by
      apply closure_minimal ?_ hclosed
      rintro _ ⟨b,rfl⟩
      change inner ℂ (a.val ξ-(E a).val ξ) (b.val ξ)=0
      rw [inner_eq_zero_symm]
      change inner ℂ (b.val ξ) (a.val ξ-(E a).val ξ)=0
      let c : Algebra M := coordinateInclusion (stateBicentralizerVonNeumann_le ξ hsep) b
      have hc : stateBicentralizerMember ξ c :=
        (mem_stateBicentralizerVonNeumann ξ hsep c).mp b.property
      have hp := bicentralizerProjection_pairing ξ hsep a c hc
      change inner ℂ (b.val ξ) ((E a).val ξ)=inner ℂ (b.val ξ) (a.val ξ) at hp
      rw [inner_sub_right,hp,sub_self]
    exact fun w hw => hsubset hw
  exact (C.eq_starProjection_of_mem_of_inner_eq_zero hm hz).symm

theorem bicentralizerProjection_vector_norm_le (ξ : H)
    (hsep : Function.Injective (algebraVectorMap M ξ)) (a : Algebra M) :
    ‖(bicentralizerProjectionCLM ξ hsep a).val ξ‖ ≤ ‖a.val ξ‖ := by
  rw [bicentralizerProjection_vector_eq]
  exact Submodule.norm_starProjection_apply_le _ _

end

end KadisonKastler

end OAI
