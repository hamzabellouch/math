import OAI.Analysis.IrrationalRotation.Operators.TracialFiniteness
import OAI.Analysis.IrrationalRotation.Analysis.ClosedRangeTransport

namespace OAI

noncomputable section

namespace Invariant233

open InvariantRotation.ClosedRangeTransport

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H] {M : VonNeumannAlgebra H} {ξ : H}

theorem IsFaithfulTracialVector.surjective_of_left_inverse
    (hτ : IsFaithfulTracialVector M ξ)
    {a b : H →L[ℂ] H} (ham : a ∈ M) (hba : b * a = 1) :
    Function.Surjective a := by
  let : CompleteSpace (⊤ : Submodule ℂ H) := isClosed_univ.completeSpace_coe
  have hleft : Function.LeftInverse b a := by
    intro x
    exact congrArg (fun T : H →L[ℂ] H => T x) hba
  have hclosed : IsClosed (Set.range a) :=
    hleft.isClosed_range b.continuous a.continuous
  let f : (⊤ : Submodule ℂ H) →L[ℂ] H := a.comp (⊤ : Submodule ℂ H).subtypeL
  have hrange : f.range = a.range := by
    ext y
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨x.val, rfl⟩
    · rintro ⟨x, rfl⟩
      exact ⟨⟨x, Submodule.mem_top⟩, rfl⟩
  have hfclosed : IsClosed (Set.range f) := by
    change IsClosed (f.range : Set H)
    rw [hrange]
    exact hclosed
  let : IsClosed (f.range : Set H) := hfclosed
  have hfinj : Function.Injective f := by
    intro x y hxy
    apply Subtype.ext
    exact hleft.injective hxy
  have hforward : forward ⊤ f = a := by
    ext x
    change a ((⊤ : Submodule ℂ H).starProjection x) = a x
    rw [Submodule.starProjection_top']
    rfl
  have hfm : forward ⊤ f ∈ M := hforward ▸ ham
  have hqmem : f.range.starProjection ∈ M := by
    have hc : IsClosed (Set.range (forward ⊤ f)) := hforward ▸ hclosed
    simpa only [range_forward] using range_projection_mem M (forward ⊤ f) hfm hc
  have htrace : vectorTrace ξ 1 = vectorTrace ξ f.range.starProjection := by
    simpa only [Submodule.starProjection_top'] using
      trace_range_eq M ⊤ f hfinj hfclosed
        (by simpa only [Submodule.starProjection_top'] using (one_mem M)) hfm
        (vectorTrace ξ) (fun a ha b hb => hτ.2.1 a b ha hb)
  have hqone : f.range.starProjection = 1 :=
    hτ.projection_eq_of_trace_eq hqmem (one_mem M)
      isStarProjection_starProjection (IsStarProjection.one _) (mul_one _) htrace.symm
  intro y
  have hy : y ∈ f.range := by
    have h := f.range.starProjection_apply_mem y
    simpa only [hqone, one_apply_eq_self] using h
  rw [hrange] at hy
  exact hy

theorem IsFaithfulTracialVector.mul_eq_one_of_reverse
    (hτ : IsFaithfulTracialVector M ξ)
    {a b : H →L[ℂ] H} (ham : a ∈ M) (hba : b * a = 1) :
    a * b = 1 := by
  ext y
  obtain ⟨x, rfl⟩ := hτ.surjective_of_left_inverse ham hba y
  have hx := congrArg (fun T : H →L[ℂ] H => T x) hba
  change a (b (a x)) = a x
  exact congrArg a hx

theorem IsFaithfulTracialVector.isDedekindFiniteMonoid
    (hτ : IsFaithfulTracialVector M ξ) : IsDedekindFiniteMonoid M := by
  constructor
  intro a b hab
  apply Subtype.ext
  exact hτ.mul_eq_one_of_reverse b.property (congrArg Subtype.val hab)

end Invariant233

end

end OAI
