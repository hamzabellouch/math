import Mathlib
import OAI.Analysis.FreeWords.BicommutantTrace
import OAI.Analysis.FreeWords.GNSQuotient
import OAI.Analysis.FreeWords.TracialClipApprox

namespace OAI

noncomputable section

namespace KKUltraTrace

open scoped InnerProductSpace ComplexOrder Pointwise

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

attribute [local instance] KKUltraTrace.biOrder

attribute [local instance] KKUltraTrace.biLE

attribute [local instance] KKUltraTrace.biPreorder

attribute [local instance] KKUltraTrace.biSOR

end

end KKUltraTrace

namespace KKUltraTrace

open scoped ComplexOrder InnerProductSpace

noncomputable section

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

end

end KKUltraTrace

namespace KKUltraTrace

open scoped InnerProductSpace ComplexOrder

noncomputable section

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

attribute [local instance] biOrder biLE biPreorder biSOR

def gnsBiHom (τ : A →ₚ[ℂ] ℂ) : A →⋆ₐ[ℂ] bicommutantAlg τ.gnsStarAlgHom.range :=
  τ.gnsStarAlgHom.codRestrict _ (fun a => subset_bicommutantAlg _ ⟨a, rfl⟩)

@[simp] theorem gnsBiHom_coe (τ : A →ₚ[ℂ] ℂ) (a : A) :
    (gnsBiHom τ a).1 = τ.gnsStarAlgHom a := rfl

theorem gns_bicommutantState_tracial (τ : A →ₚ[ℂ] ℂ)
    (htr : ∀ x y : A, τ (x*y) = τ (y*x)) :
    ∀ x y, bicommutantState τ.gnsStarAlgHom.range (gnsVector τ 1) (x*y) =
      bicommutantState τ.gnsStarAlgHom.range (gnsVector τ 1) (y*x) := by
  apply bicommutantState_tracial
  rintro a ⟨a', rfl⟩ b ⟨b', rfl⟩
  change gnsExpectation τ (τ.gnsStarAlgHom a' * τ.gnsStarAlgHom b') =
    gnsExpectation τ (τ.gnsStarAlgHom b' * τ.gnsStarAlgHom a')
  rw [← map_mul, ← map_mul, gnsExpectation_image, gnsExpectation_image]
  exact htr a' b'

theorem bicommutantState_star_mul {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H]
    (S : StarSubalgebra ℂ (H →L[ℂ] H)) (Ω : H) (x : bicommutantAlg S) :
    bicommutantState S Ω (star x*x) = ⟪x.1 Ω, x.1 Ω⟫_ℂ := by
  change ⟪Ω, x.1.adjoint (x.1 Ω)⟫_ℂ = _
  exact ContinuousLinearMap.adjoint_inner_right _ _ _

theorem bicommutant_gns_norm {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H]
    (S : StarSubalgebra ℂ (H →L[ℂ] H)) (Ω : H) (x : bicommutantAlg S) :
    ‖gnsVector (bicommutantState S Ω) x‖ = ‖x.1 Ω‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [gnsVector_norm_sq, bicommutantState_star_mul, @norm_sq_eq_re_inner ℂ]
  rfl

theorem gns_bicommutantState_faithful (τ : A →ₚ[ℂ] ℂ)
    (htr : ∀ x y : A, τ (x*y) = τ (y*x)) (x : bicommutantAlg τ.gnsStarAlgHom.range)
    (hx : bicommutantState τ.gnsStarAlgHom.range (gnsVector τ 1) (star x*x) = 0) :
    x = 0 := by
  have hzero : ∀ b : bicommutantAlg τ.gnsStarAlgHom.range,
      x.1 (b.1 (gnsVector τ 1)) = 0 := by
    intro b
    have hab := tracial_null_right (bicommutantState τ.gnsStarAlgHom.range (gnsVector τ 1))
      (gns_bicommutantState_tracial τ htr) x hx b
    rw [bicommutantState_star_mul] at hab
    exact (inner_self_eq_zero (𝕜 := ℂ)).mp hab
  have hvec (a : A) : x.1 (gnsVector τ a) = 0 := by
    have hb := hzero (gnsBiHom τ a)
    simpa only [gnsBiHom_coe, gnsStarAlgHom_vector, mul_one] using hb
  apply Subtype.ext
  ext ξ
  induction ξ using UniformSpace.Completion.induction_on with
  | hp => exact isClosed_eq x.1.continuous continuous_const
  | ih a => exact hvec (τ.ofPreGNS a)

theorem gns_bicommutant_separating (τ : A →ₚ[ℂ] ℂ)
    (htr : ∀ x y : A, τ (x*y) = τ (y*x)) (x y : bicommutantAlg τ.gnsStarAlgHom.range)
    (hxy : x.1 (gnsVector τ 1) = y.1 (gnsVector τ 1)) : x = y := by
  apply sub_eq_zero.mp
  apply gns_bicommutantState_faithful τ htr
  rw [bicommutantState_star_mul]
  have he : (x-y).1 (gnsVector τ 1) = 0 := sub_eq_zero.mpr hxy
  rw [he, inner_zero_left]

theorem tracialGNS_bicommutant_of_closed_balls (τ : A →ₚ[ℂ] ℂ)
    (htr : ∀ x y : A, τ (x*y) = τ (y*x))
    (hclosed : ∀ b : ℝ, IsClosed (gnsVector τ '' Metric.closedBall (0 : A) b)) :
    Set.centralizer (Set.centralizer (τ.gnsStarAlgHom.range : Set (τ.GNS →L[ℂ] τ.GNS))) =
      τ.gnsStarAlgHom.range := by
  apply Set.Subset.antisymm _ Set.subset_centralizer_centralizer
  intro T hT
  let S := τ.gnsStarAlgHom.range
  let Ω := gnsVector τ 1
  let x : bicommutantAlg S := ⟨T, by change T ∈ (bicommutantAlg S : Set _); rwa [coe_bicommutantAlg]⟩
  let b : ℝ := 2*‖x‖+1
  have hb : 0 < b := by dsimp [b]; positivity
  have hx : 2*‖x‖ ≤ b := by dsimp [b]; linarith
  have happrox : T Ω ∈ closure (gnsVector τ '' Metric.closedBall (0:A) b) := by
    apply Metric.mem_closure_iff.mpr
    intro ε hε
    obtain ⟨a, ⟨a', rfl⟩, ha⟩ := UniversalStrongKK.bicommutant_strong_approximation
      S T hT 1 (fun _ => Ω) (ε/3) (by positivity)
    refine ⟨gnsVector τ (spectralClip b a'), ⟨spectralClip b a', ?_, rfl⟩, ?_⟩
    · simpa only [Metric.mem_closedBall, dist_zero_right] using norm_spectralClip_le hb a'
    · have hc := tracial_clip_approximation (bicommutantState S Ω)
        (gns_bicommutantState_tracial τ htr) hb (gnsBiHom τ a') x hx
      simp only [bicommutant_gns_norm, ← map_spectralClip (gnsBiHom τ) hb] at hc
      change ‖(τ.gnsStarAlgHom (spectralClip b a')) Ω-T Ω‖ ≤
        3*‖τ.gnsStarAlgHom a' Ω-T Ω‖ at hc
      have ha' : ‖τ.gnsStarAlgHom a' Ω-T Ω‖ < ε/3 := by
        have hh := ha 0
        change ‖(τ.gnsStarAlgHom a'-T) Ω‖ < ε/3 at hh
        simpa only [norm_sub_rev, sub_apply] using hh
      have he (a : A) : τ.gnsStarAlgHom a Ω = gnsVector τ a := by
        dsimp [Ω]; rw [gnsStarAlgHom_vector, mul_one]
      rw [he] at hc
      rw [dist_eq_norm, norm_sub_rev]
      linarith
  obtain ⟨a, ha, hae⟩ := (hclosed b).closure_subset happrox
  refine ⟨a, ?_⟩
  have heq : gnsBiHom τ a = x := by
    apply gns_bicommutant_separating τ htr
    simpa only [gnsBiHom_coe, gnsStarAlgHom_vector, mul_one] using hae
  exact congrArg Subtype.val heq

end

end KKUltraTrace
end

end OAI
