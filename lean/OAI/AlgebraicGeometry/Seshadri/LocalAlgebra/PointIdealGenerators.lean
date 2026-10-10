import Mathlib

namespace OAI

section
noncomputable section
                                              
section

namespace MaximalSeshadri.PointCoordinates
noncomputable section
open MvPolynomial

theorem ker_eq_span_centered {K R ι : Type*} [CommRing K] [CommRing R] [Algebra K R]
    (a : ι → R) (ha : Function.Surjective (MvPolynomial.aeval (R := K) a))
    (p : R →ₐ[K] K) :
    RingHom.ker p.toRingHom = Ideal.span (Set.range fun i => a i - algebraMap K R (p (a i))) := by
  let J : Ideal R := Ideal.span (Set.range fun i => a i - algebraMap K R (p (a i)))
  have hJ : J ≤ RingHom.ker p.toRingHom := by
    apply Ideal.span_le.mpr
    rintro _ ⟨i, rfl⟩
    simp
  have he : (Ideal.Quotient.mk J).comp (MvPolynomial.aeval (R := K) a).toRingHom =
      ((algebraMap K (R ⧸ J)).comp p.toRingHom).comp
        (MvPolynomial.aeval (R := K) a).toRingHom := by
    apply MvPolynomial.ringHom_ext
    · intro c
      simp
    · intro i
      simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe,
        RingHom.coe_coe, MvPolynomial.aeval_X]
      have hh : a i - algebraMap K R (p (a i)) ∈ J :=
        Ideal.subset_span (Set.mem_range_self i)
      have hz := Ideal.Quotient.eq_zero_iff_mem.mpr hh
      rw [map_sub, sub_eq_zero] at hz
      exact hz
  apply le_antisymm ?_ hJ
  intro r hr
  obtain ⟨f, rfl⟩ := ha r
  apply Ideal.Quotient.eq_zero_iff_mem.mp
  have hh := RingHom.congr_fun he f
  simpa only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
    (show p ((MvPolynomial.aeval a) f) = 0 from hr), map_zero] using hh

end
end MaximalSeshadri.PointCoordinates

end


end
end

end OAI
