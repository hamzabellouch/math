import OAI.Analysis.IrrationalRotation.Spectral.PositivePartialResolvent
import OAI.Analysis.IrrationalRotation.Operators.NormalAffiliatedTransport

namespace OAI

noncomputable section
namespace Invariant233.PositivePartialResolvent

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

omit [CompleteSpace E] in
theorem resolvent_unique (H : E →ₗ.[ℂ] E) (R S : E →L[ℂ] E)
    (hRD : ∀ y, S y ∈ H.domain)
    (hSH : ∀ y, ∀ hy : S y ∈ H.domain, H ⟨S y, hy⟩ = y - S y)
    (hRH : ∀ x : H.domain, R ((x : E) + H x) = (x : E)) :
    R = S := by
  ext y
  have h := hRH ⟨S y, hRD y⟩
  rw [hSH, add_sub_cancel] at h
  exact h

theorem commute_resolvent_of_affiliated
    (M : VonNeumannAlgebra E) (H : E →ₗ.[ℂ] E) (haff : IsAffiliated M H)
    (R : E →L[ℂ] E) (hD : ∀ y, R y ∈ H.domain)
    (hHR : ∀ y, ∀ hy : R y ∈ H.domain, H ⟨R y, hy⟩ = y - R y)
    (hRH : ∀ x : H.domain, R ((x : E) + H x) = (x : E))
    (W : E →L[ℂ] E) (hW : W ∈ M.commutant) : Commute W R := by
  obtain ⟨hWD, hWH⟩ := haff.commutes_of_mem_commutant hW
  change W * R = R * W
  ext y
  have h := hRH ⟨W (R y), hWD ⟨R y, hD y⟩⟩
  rw [hWH ⟨R y, hD y⟩, hHR, map_sub, add_sub_cancel] at h
  exact h.symm

theorem resolvent_mem_of_affiliated
    (M : VonNeumannAlgebra E) (H : E →ₗ.[ℂ] E) (haff : IsAffiliated M H)
    (R : E →L[ℂ] E) (hD : ∀ y, R y ∈ H.domain)
    (hHR : ∀ y, ∀ hy : R y ∈ H.domain, H ⟨R y, hy⟩ = y - R y)
    (hRH : ∀ x : H.domain, R ((x : E) + H x) = (x : E)) : R ∈ M := by
  rw [← M.commutant_commutant]
  exact VonNeumannAlgebra.mem_commutant_iff.mpr fun W hW =>
    (commute_resolvent_of_affiliated M H haff R hD hHR hRH W hW).eq

theorem exists_affiliated_resolvent
    (M : VonNeumannAlgebra E) (H : E →ₗ.[ℂ] E)
    (hH : IsSelfAdjoint H) (hpos : IsPositivePartial H) (haff : IsAffiliated M H) :
    ∃ R : E →L[ℂ] E, R ∈ M ∧
      ‖R‖ ≤ 1 ∧
      (∀ y, R y ∈ H.domain) ∧
      (∀ y, ∀ hy : R y ∈ H.domain, H ⟨R y, hy⟩ = y - R y) ∧
      (∀ x : H.domain, R ((x : E) + H x) = (x : E)) ∧
      R.range = H.domain := by
  obtain ⟨R, hnorm, hD, hHR, hRH, hrange⟩ := exists_resolvent H hH hpos
  exact ⟨R, resolvent_mem_of_affiliated M H haff R hD hHR hRH,
    hnorm, hD, hHR, hRH, hrange⟩

omit [CompleteSpace E] in
theorem domain_commutes_of_commute_resolvent
    (H : E →ₗ.[ℂ] E) (R : E →L[ℂ] E) (hD : ∀ y, R y ∈ H.domain)
    (hHR : ∀ y, ∀ hy : R y ∈ H.domain, H ⟨R y, hy⟩ = y - R y)
    (hRH : ∀ x : H.domain, R ((x : E) + H x) = (x : E))
    (W : E →L[ℂ] E) (hW : Commute W R) :
    ∃ hWD : ∀ x : H.domain, W (x : E) ∈ H.domain,
      ∀ x : H.domain, H ⟨W (x : E), hWD x⟩ = W (H x) := by
  have hRW (x : H.domain) : R (W ((x : E) + H x)) = W (x : E) := by
    have hc := congrArg (fun A : E →L[ℂ] E => A ((x : E) + H x)) hW.eq
    change W (R ((x : E) + H x)) = R (W ((x : E) + H x)) at hc
    rw [hRH x] at hc
    exact hc.symm
  let hWD : ∀ x : H.domain, W (x : E) ∈ H.domain :=
    fun x => hRW x ▸ hD (W ((x : E) + H x))
  refine ⟨hWD, fun x => ?_⟩
  calc
    H ⟨W (x : E), hWD x⟩ =
        H ⟨R (W ((x : E) + H x)), hD (W ((x : E) + H x))⟩ :=
      congrArg H (Subtype.ext (hRW x).symm)
    _ = W ((x : E) + H x) - R (W ((x : E) + H x)) := hHR _ _
    _ = W (H x) := by rw [hRW, map_add, add_sub_cancel_left]

theorem affiliated_of_resolvent_mem
    (M : VonNeumannAlgebra E) (H : E →ₗ.[ℂ] E)
    (R : E →L[ℂ] E) (hD : ∀ y, R y ∈ H.domain)
    (hHR : ∀ y, ∀ hy : R y ∈ H.domain, H ⟨R y, hy⟩ = y - R y)
    (hRH : ∀ x : H.domain, R ((x : E) + H x) = (x : E))
    (hRM : R ∈ M) : IsAffiliated M H := by
  intro U hU
  have hc : Commute (U : E →L[ℂ] E) R :=
    ((VonNeumannAlgebra.mem_commutant_iff.mp hU) R hRM).symm
  exact domain_commutes_of_commute_resolvent H R hD hHR hRH U hc

theorem affiliated_iff_resolvent_mem
    (M : VonNeumannAlgebra E) (H : E →ₗ.[ℂ] E)
    (R : E →L[ℂ] E) (hD : ∀ y, R y ∈ H.domain)
    (hHR : ∀ y, ∀ hy : R y ∈ H.domain, H ⟨R y, hy⟩ = y - R y)
    (hRH : ∀ x : H.domain, R ((x : E) + H x) = (x : E)) :
    IsAffiliated M H ↔ R ∈ M :=
  ⟨fun h => resolvent_mem_of_affiliated M H h R hD hHR hRH,
    affiliated_of_resolvent_mem M H R hD hHR hRH⟩

end Invariant233.PositivePartialResolvent

end

end OAI
