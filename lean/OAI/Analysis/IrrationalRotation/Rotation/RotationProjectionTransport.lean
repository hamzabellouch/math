import OAI.Analysis.IrrationalRotation.Rotation.RotationTransferTrace
import OAI.Analysis.IrrationalRotation.Spectral.RotationResolvent

namespace OAI

noncomputable section
open MeasureTheory

namespace Invariant233

theorem hasOnlyTrivialInvariantProjections_smul_iff
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (M : VonNeumannAlgebra H) (T : H →L[ℂ] H) (c : ℂ) (hc : c ≠ 0) :
    HasOnlyTrivialInvariantProjections M (c • T) ↔ HasOnlyTrivialInvariantProjections M T := by
  constructor
  · intro h p hp hpP hTp
    apply h p hp hpP
    simp only [mul_smul_comm, smul_mul_assoc, hTp, smul_zero]
  · intro h p hp hpP hTp
    apply h p hp hpP
    simpa only [mul_smul_comm, smul_mul_assoc, smul_eq_zero, hc, false_or] using hTp

namespace Rotation

theorem exponentialTransfer_projection_transport
    (θ : ℝ) {b : Circle → ℝ} (hb : Measurable b)
    (A B p : Hilbert →L[ℂ] Hilbert) (hp : p ∈ algebra θ) (hpP : IsStarProjection p)
    (hAp : (1 - p) * A * p = 0)
    (hD : ∀ ξ : (exponentialTransfer θ b).domain,
      A ξ.val ∈ (exponentialTransfer θ b).domain)
    (hI : ∀ ξ : (exponentialTransfer θ b).domain,
      exponentialTransfer θ b ⟨A ξ.val, hD ξ⟩ = B (exponentialTransfer θ b ξ)) :
    let P := (InvariantRotation.AffiliatedTransport.transported
      (exponentialTransfer θ b) p.range).starProjection
    P ∈ algebra θ ∧ IsStarProjection P ∧ (1 - P) * B * P = 0 ∧
      vectorTrace vacuum P = vectorTrace vacuum p := by
  dsimp only
  refine ⟨exponential_orbit_transported_projection_mem θ b hb p hp,
    isStarProjection_starProjection, ?_, exponentialTransfer_projection_trace θ hb p hp hpP⟩
  have hAp' : p * A * p = A * p := by
    rw [sub_mul, one_mul, sub_mul] at hAp
    exact (sub_eq_zero.mp hAp).symm
  have hrange : ∀ y ∈ p.range, A y ∈ p.range := by
    rintro y ⟨z, rfl⟩
    refine ⟨A (p z), ?_⟩
    exact congrArg (fun C : Hilbert →L[ℂ] Hilbert => C z) hAp'
  have hinv := InvariantRotation.AffiliatedTransport.transported_invariant
    (exponentialTransfer θ b) p.range A B hrange
    (fun x hx => hD ⟨x, hx⟩) hI
  let S := InvariantRotation.AffiliatedTransport.transported (exponentialTransfer θ b) p.range
  have hr : S.starProjection.range ∈ Module.End.invtSubmodule B := by
    rw [Submodule.range_starProjection]
    exact hinv
  have heq := (ContinuousLinearMap.IsIdempotentElem.range_mem_invtSubmodule_iff
    (isStarProjection_starProjection (U := S)).isIdempotentElem).mp hr
  change S.starProjection * B * S.starProjection = B * S.starProjection at heq
  change (1 - S.starProjection) * B * S.starProjection = 0
  rw [sub_mul, one_mul, sub_mul, heq, sub_self]

theorem hasOnlyTrivialInvariantProjections_of_exponentialTransfer
    (θ : ℝ) {b : Circle → ℝ} (hb : Measurable b)
    (A B : Hilbert →L[ℂ] Hilbert)
    (hD : ∀ ξ : (exponentialTransfer θ b).domain,
      A ξ.val ∈ (exponentialTransfer θ b).domain)
    (hI : ∀ ξ : (exponentialTransfer θ b).domain,
      exponentialTransfer θ b ⟨A ξ.val, hD ξ⟩ = B (exponentialTransfer θ b ξ))
    (hB : HasOnlyTrivialInvariantProjections (algebra θ) B) :
    HasOnlyTrivialInvariantProjections (algebra θ) A := by
  intro p hp hpP hAp
  obtain ⟨hPm, hPP, hPB, htrace⟩ :=
    exponentialTransfer_projection_transport θ hb A B p hp hpP hAp hD hI
  let P := (InvariantRotation.AffiliatedTransport.transported
    (exponentialTransfer θ b) p.range).starProjection
  have hfaith := (vacuum_faithfulTracial θ).2.2
  rcases hB P hPm hPP hPB with hP | hP
  · left
    apply hfaith p hp (ContinuousLinearMap.IsPositive.of_isStarProjection hpP)
    rw [← htrace]
    change vectorTrace vacuum P = 0
    rw [hP]
    simp [vectorTrace]
  · right
    have hc : vectorTrace vacuum (1 - p) = 0 := by
      have he : vectorTrace vacuum (1 - p) =
          vectorTrace vacuum 1 - vectorTrace vacuum p := by
        simp only [vectorTrace, sub_apply, inner_sub_right]
      rw [he, ← htrace]
      change vectorTrace vacuum 1 - vectorTrace vacuum P = 0
      rw [hP, sub_self]
    have hz := hfaith (1 - p) ((algebra θ).sub_mem (algebra θ).one_mem hp)
      (ContinuousLinearMap.IsPositive.of_isStarProjection hpP.one_sub) hc
    exact (sub_eq_zero.mp hz).symm

theorem hasOnlyTrivialInvariantProjections_of_scaled_exponentialTransfer
    (θ : ℝ) {b : Circle → ℝ} (hb : Measurable b)
    (A B : Hilbert →L[ℂ] Hilbert) (c : ℂ) (hc : c ≠ 0)
    (hD : ∀ ξ : (exponentialTransfer θ b).domain,
      A ξ.val ∈ (exponentialTransfer θ b).domain)
    (hI : ∀ ξ : (exponentialTransfer θ b).domain,
      exponentialTransfer θ b ⟨A ξ.val, hD ξ⟩ = c • B (exponentialTransfer θ b ξ))
    (hB : HasOnlyTrivialInvariantProjections (algebra θ) B) :
    HasOnlyTrivialInvariantProjections (algebra θ) A := by
  apply hasOnlyTrivialInvariantProjections_of_exponentialTransfer θ hb A (c • B) hD hI
  exact (hasOnlyTrivialInvariantProjections_smul_iff (algebra θ) B c hc).mpr hB

end Rotation
end Invariant233

end

end OAI
