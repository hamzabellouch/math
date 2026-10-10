import OAI.Analysis.KadisonKastler.BicentralizerOrbitPairing
import OAI.Analysis.KadisonKastler.StateOrbitMinimalCore

namespace OAI

/-! # A contractive state-preserving projection onto the bicentralizer

The compact asymptotic orbit hull supplies an element of the bicentralizer.
Its pairings with every bicentralizer vector are prescribed, which makes
the choice unique and proves linearity. The orbit norm bound gives the
contractive projection on the original algebra.
-/

namespace KadisonKastler

open Generator.Tracial

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {M : VonNeumannAlgebra H}

theorem exists_bicentralizer_orbit_point (ξ : H)
    (hsep : Function.Injective (algebraVectorMap M ξ)) (a : Algebra M) :
    ∃ b : Algebra M, stateBicentralizerMember ξ b ∧
      ContinuousLinearMapWOT.ofCLM b.val ∈ stateOrbitCore ξ a := by
  obtain ⟨b,hb,he⟩ := exists_singleton_stateOrbitCore ξ hsep a
  exact ⟨b,singleton_stateOrbitCore_stateBicentralizer ξ hsep b he,hb⟩

def bicentralizerProjection (ξ : H)
    (hsep : Function.Injective (algebraVectorMap M ξ)) (a : Algebra M) : Algebra M :=
  (exists_bicentralizer_orbit_point ξ hsep a).choose

theorem bicentralizerProjection_mem (ξ : H)
    (hsep : Function.Injective (algebraVectorMap M ξ)) (a : Algebra M) :
    stateBicentralizerMember ξ (bicentralizerProjection ξ hsep a) :=
  (exists_bicentralizer_orbit_point ξ hsep a).choose_spec.1

theorem bicentralizerProjection_orbit (ξ : H)
    (hsep : Function.Injective (algebraVectorMap M ξ)) (a : Algebra M) :
    ContinuousLinearMapWOT.ofCLM (bicentralizerProjection ξ hsep a).val ∈ stateOrbitCore ξ a :=
  (exists_bicentralizer_orbit_point ξ hsep a).choose_spec.2

theorem bicentralizerProjection_pairing (ξ : H)
    (hsep : Function.Injective (algebraVectorMap M ξ)) (a b : Algebra M)
    (hb : stateBicentralizerMember ξ b) :
    inner ℂ (b.val ξ) ((bicentralizerProjection ξ hsep a).val ξ)=
      inner ℂ (b.val ξ) (a.val ξ) :=
  stateOrbitCore_bicentralizer_pairing ξ hsep a b hb (bicentralizerProjection_orbit ξ hsep a)

theorem eq_of_bicentralizer_pairings (ξ : H)
    (hsep : Function.Injective (algebraVectorMap M ξ)) (a b : Algebra M)
    (ha : stateBicentralizerMember ξ a) (hb : stateBicentralizerMember ξ b)
    (h : ∀ c : Algebra M, stateBicentralizerMember ξ c →
      inner ℂ (c.val ξ) (a.val ξ)=inner ℂ (c.val ξ) (b.val ξ)) : a=b := by
  have hd : stateBicentralizerMember ξ (a-b) := by
    have hs := stateBicentralizerMember_smul ξ (-1) hb
    simpa only [neg_one_smul,sub_eq_add_neg] using stateBicentralizerMember_add ξ ha hs
  have he := h (a-b) hd
  have hz : inner ℂ ((a-b).val ξ) ((a-b).val ξ)=0 := by
    change inner ℂ ((a-b).val ξ) (a.val ξ-b.val ξ)=0
    rw [inner_sub_right,he,sub_self]
  have hv : (a-b).val ξ=0 := (inner_self_eq_zero).mp hz
  apply hsep
  change a.val ξ=b.val ξ
  exact sub_eq_zero.mp hv

theorem bicentralizerProjection_add (ξ : H)
    (hsep : Function.Injective (algebraVectorMap M ξ)) (a b : Algebra M) :
    bicentralizerProjection ξ hsep (a+b)=
      bicentralizerProjection ξ hsep a+bicentralizerProjection ξ hsep b := by
  apply eq_of_bicentralizer_pairings ξ hsep _ _ (bicentralizerProjection_mem ξ hsep _)
    (stateBicentralizerMember_add ξ (bicentralizerProjection_mem ξ hsep a)
      (bicentralizerProjection_mem ξ hsep b))
  intro c hc
  rw [bicentralizerProjection_pairing ξ hsep _ c hc]
  change inner ℂ (c.val ξ) (a.val ξ+b.val ξ)=
    inner ℂ (c.val ξ) ((bicentralizerProjection ξ hsep a).val ξ+
      (bicentralizerProjection ξ hsep b).val ξ)
  rw [inner_add_right,inner_add_right,bicentralizerProjection_pairing ξ hsep a c hc,
    bicentralizerProjection_pairing ξ hsep b c hc]

theorem bicentralizerProjection_smul (ξ : H)
    (hsep : Function.Injective (algebraVectorMap M ξ)) (r : ℂ) (a : Algebra M) :
    bicentralizerProjection ξ hsep (r • a)=r • bicentralizerProjection ξ hsep a := by
  apply eq_of_bicentralizer_pairings ξ hsep _ _ (bicentralizerProjection_mem ξ hsep _)
    (stateBicentralizerMember_smul ξ r (bicentralizerProjection_mem ξ hsep a))
  intro c hc
  rw [bicentralizerProjection_pairing ξ hsep _ c hc]
  change inner ℂ (c.val ξ) (r • a.val ξ)=
    inner ℂ (c.val ξ) (r • (bicentralizerProjection ξ hsep a).val ξ)
  rw [inner_smul_right,inner_smul_right,bicentralizerProjection_pairing ξ hsep a c hc]

theorem bicentralizerProjection_norm_le (ξ : H)
    (hsep : Function.Injective (algebraVectorMap M ξ)) (a : Algebra M) :
    ‖bicentralizerProjection ξ hsep a‖ ≤ ‖a‖ :=
  (stateOrbitCore_subset_ball ξ a (bicentralizerProjection_orbit ξ hsep a)).2

def bicentralizerProjectionCLM (ξ : H)
    (hsep : Function.Injective (algebraVectorMap M ξ)) : Algebra M →L[ℂ] Algebra M :=
  LinearMap.mkContinuous
    { toFun := bicentralizerProjection ξ hsep
      map_add' := bicentralizerProjection_add ξ hsep
      map_smul' := bicentralizerProjection_smul ξ hsep }
    1 (by
      intro a
      change ‖bicentralizerProjection ξ hsep a‖ ≤ 1*‖a‖
      simpa only [one_mul] using bicentralizerProjection_norm_le ξ hsep a)

theorem bicentralizerProjection_fixed (ξ : H)
    (hsep : Function.Injective (algebraVectorMap M ξ)) (a : Algebra M)
    (ha : stateBicentralizerMember ξ a) : bicentralizerProjectionCLM ξ hsep a=a := by
  apply eq_of_bicentralizer_pairings ξ hsep _ _ (bicentralizerProjection_mem ξ hsep a) ha
  exact fun c hc => bicentralizerProjection_pairing ξ hsep a c hc

theorem bicentralizerProjection_idempotent (ξ : H)
    (hsep : Function.Injective (algebraVectorMap M ξ)) (a : Algebra M) :
    bicentralizerProjectionCLM ξ hsep (bicentralizerProjectionCLM ξ hsep a)=
      bicentralizerProjectionCLM ξ hsep a :=
  bicentralizerProjection_fixed ξ hsep _ (bicentralizerProjection_mem ξ hsep a)

theorem bicentralizerProjection_state (ξ : H)
    (hsep : Function.Injective (algebraVectorMap M ξ)) (a : Algebra M) :
    vectorFunctional ξ (bicentralizerProjectionCLM ξ hsep a)=vectorFunctional ξ a := by
  have h := bicentralizerProjection_pairing ξ hsep a 1 (stateBicentralizerMember_one ξ)
  exact h

end

end KadisonKastler

end OAI
