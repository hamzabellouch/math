import Mathlib.Analysis.InnerProductSpace.LinearPMap

namespace OAI

noncomputable section

namespace Invariant233.PartialResolvent

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
variable (H : E →ₗ.[ℂ] E) (R : E →L[ℂ] E)
variable (hD : ∀ x : E, R x ∈ H.domain)
variable (hHR : ∀ x : E, H ⟨R x, hD x⟩ = x - R x)
variable (hRH : ∀ x : H.domain, R ((x : E) + H x) = x)

include hD hHR hRH

theorem normalized_intertwining (A B : E →L[ℂ] E)
    (hA : ∀ x : H.domain, A (x : E) ∈ H.domain)
    (hI : ∀ x : H.domain, H ⟨A (x : E), hA x⟩ = B (H x)) :
    (1 - R) * A * R = R * B * (1 - R) := by
  ext x
  change A (R x) - R (A (R x)) = R (B (x - R x))
  have hi := hI ⟨R x, hD x⟩
  rw [hHR] at hi
  have hr := hRH ⟨A (R x), hA ⟨R x, hD x⟩⟩
  rw [hi, map_add] at hr
  exact sub_eq_iff_eq_add.mpr (by simpa only [add_comm] using hr.symm)

theorem domain_intertwining_of_normalized (A B : E →L[ℂ] E)
    (hI : (1 - R) * A * R = R * B * (1 - R)) :
    ∃ hA : ∀ x : H.domain, A (x : E) ∈ H.domain,
      ∀ x : H.domain, H ⟨A (x : E), hA x⟩ = B (H x) := by
  have hrep : ∀ x : H.domain, R (A (x : E) + B (H x)) = A (x : E) := by
    intro x
    have he := congrArg (fun T : E →L[ℂ] E => T ((x : E) + H x)) hI
    change A (R ((x : E) + H x)) - R (A (R ((x : E) + H x))) =
      R (B ((x : E) + H x - R ((x : E) + H x))) at he
    rw [hRH, add_sub_cancel_left] at he
    rw [map_add]
    exact (by simpa only [add_comm] using (sub_eq_iff_eq_add.mp he).symm)
  let hA : ∀ x : H.domain, A (x : E) ∈ H.domain :=
    fun x => hrep x ▸ hD (A (x : E) + B (H x))
  refine ⟨hA, fun x => ?_⟩
  have hx : (⟨R (A (x : E) + B (H x)), hD _⟩ : H.domain) =
      ⟨A (x : E), hA x⟩ := Subtype.ext (hrep x)
  have hh := hHR (A (x : E) + B (H x))
  rw [hx, hrep x, add_sub_cancel_left] at hh
  exact hh

theorem normalized_intertwining_iff (A B : E →L[ℂ] E) :
    (1 - R) * A * R = R * B * (1 - R) ↔
      ∃ hA : ∀ x : H.domain, A (x : E) ∈ H.domain,
        ∀ x : H.domain, H ⟨A (x : E), hA x⟩ = B (H x) := by
  constructor
  · exact domain_intertwining_of_normalized H R hD hHR hRH A B
  · rintro ⟨hA, hI⟩
    exact normalized_intertwining H R hD hHR hRH A B hA hI

end Invariant233.PartialResolvent

end

end OAI
