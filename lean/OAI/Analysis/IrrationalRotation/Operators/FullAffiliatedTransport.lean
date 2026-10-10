import OAI.Analysis.IrrationalRotation.Spectral.AffiliatedPositiveResolvent
import OAI.Analysis.IrrationalRotation.Spectral.PartialResolventCalculus
import OAI.Analysis.IrrationalRotation.Operators.NormalTracialTransport

namespace OAI

noncomputable section
namespace Invariant233

theorem affiliated_transport_proof
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    (M : VonNeumannAlgebra E) (τ : TracialState M)
    (hτ : IsNormalFaithfulTracialState M τ)
    (H : E →ₗ.[ℂ] E) (hH : IsSelfAdjoint H) (hpos : IsPositivePartial H)
    (hinj : Function.Injective H) (haff : IsAffiliated M H)
    (A B : M)
    (hD : ∀ x : H.domain, (A : E →L[ℂ] E) (x : E) ∈ H.domain)
    (hinter : ∀ x : H.domain,
      H ⟨(A : E →L[ℂ] E) (x : E), hD x⟩ = (B : E →L[ℂ] E) (H x))
    (p : M) (hp : IsStarProjection (p : E →L[ℂ] E))
    (hinv : (1 - (p : E →L[ℂ] E)) * (A : E →L[ℂ] E) *
      (p : E →L[ℂ] E) = 0) :
    ∃ P : M,
      (P : E →L[ℂ] E) =
        (InvariantRotation.AffiliatedTransport.transported H
          (p : E →L[ℂ] E).range).starProjection ∧
      IsStarProjection (P : E →L[ℂ] E) ∧
      (1 - (P : E →L[ℂ] E)) * (B : E →L[ℂ] E) *
        (P : E →L[ℂ] E) = 0 ∧
      τ P = τ p := by
  obtain ⟨hPM, hPproj, hPinv⟩ := haff.transported_projection_invariant
    (A : E →L[ℂ] E) (B : E →L[ℂ] E) hD hinter p.property hp hinv
  refine ⟨⟨_, hPM⟩, rfl, hPproj, hPinv, ?_⟩
  obtain ⟨R, hRM, _hnorm, hRD, hHR, _hRH, _hrange⟩ :=
    PositivePartialResolvent.exists_affiliated_resolvent M H hH hpos haff
  have hHR' : ∀ x, H ⟨R x, hRD x⟩ = x - R x := fun x => hHR x (hRD x)
  have hformal : H.IsFormalAdjoint H := by
    simpa only [LinearPMap.isSelfAdjoint_def.mp hH] using
      (LinearPMap.adjoint_isFormalAdjoint hH.dense_domain)
  have hRinj := PartialResolvent.injective H R hRD hHR'
  have hSinj := PartialResolvent.injective_one_sub H R hRD hHR' hinj
  have hRsa := PartialResolvent.isSelfAdjoint H R hRD hHR' hformal
  have hSsa := PartialResolvent.one_sub_isSelfAdjoint H R hRD hHR' hformal
  change star R = R at hRsa
  change star (1 - R : E →L[ℂ] E) = 1 - R at hSsa
  have hRadj : Function.Injective R.adjoint := by
    rw [← ContinuousLinearMap.star_eq_adjoint, hRsa]
    exact hRinj
  have hSadj : Function.Injective (1 - R : E →L[ℂ] E).adjoint := by
    rw [← ContinuousLinearMap.star_eq_adjoint, hSsa]
    exact hSinj
  have hSM : (1 - R : E →L[ℂ] E) ∈ M := sub_mem (one_mem M) hRM
  let : CompleteSpace (p : E →L[ℂ] E).range :=
    (ContinuousLinearMap.IsIdempotentElem.isClosed_range hp.isIdempotentElem).completeSpace_coe
  have hpeq : (p : E →L[ℂ] E).range.starProjection = (p : E →L[ℂ] E) :=
    (isStarProjection_iff_eq_starProjection_range.mp hp).choose_spec.symm
  have hpM : (p : E →L[ℂ] E).range.starProjection ∈ M := by
    rw [hpeq]
    exact p.property
  have htrace := NormalTracialTransport.transported_trace_eq_of_normalizer
    M τ hτ H hformal (LinearMap.ker_eq_bot.mpr hinj) R (1 - R) hRM hSM
    hRinj hRadj hSinj hSadj hRD hHR' (p : E →L[ℂ] E).range hpM hPM
  convert htrace using 1
  congr 1
  exact Subtype.ext hpeq.symm

end Invariant233

end

end OAI
