import Mathlib

namespace OAI

section
noncomputable section
                                            
section

namespace MaximalSeshadri.NodalLocal
noncomputable section
open IsLocalRing
open scoped nonZeroDivisors

lemma principal_curve_dimension_le_one {R : Type*} [CommRing R] [IsDomain R]
    (hd : ringKrullDim R ≤ 2) (g : R) (hg : g ≠ 0) :
    ringKrullDim (R ⧸ Ideal.span {g}) ≤ 1 := by
  apply ENat.WithBot.add_le_add_one_right_iff.mp
  have H := (ringKrullDim_quotient_succ_le_of_nonZeroDivisor
    (mem_nonZeroDivisors_iff_ne_zero.mpr hg)).trans hd
  simpa only [one_add_one_eq_two] using H

theorem formal_branch_kernel {K R : Type*} [Field K] [CommRing R] [IsDomain R]
    (hd : ringKrullDim R ≤ 2) (g : R) (hg : g ≠ 0)
    [hgp : (Ideal.span {g}).IsPrime]
    (φ : R →+* PowerSeries K) (hφg : φ g = 0)
    (hbranch : ∃ a : R, PowerSeries.constantCoeff (φ a) = 0 ∧ φ a ≠ 0) :
    RingHom.ker φ = Ideal.span {g} := by
  have hI : Ideal.span {g} ≤ RingHom.ker φ := (Ideal.span_singleton_le_iff_mem _).mpr hφg
  let ψ := Ideal.Quotient.lift (Ideal.span {g}) φ hI
  have hcomp : ψ.comp (Ideal.Quotient.mk (Ideal.span {g})) = φ := by
    ext a
    rfl
  let : Ring.KrullDimLE 1 (R ⧸ Ideal.span {g}) :=
    Ring.krullDimLE_iff.mpr (principal_curve_dimension_le_one hd g hg)
  apply (Ideal.injective_lift_iff hI).mp
  apply (RingHom.injective_iff_ker_eq_bot _).mpr
  by_contra hne
  have hm : (RingHom.ker ψ).IsMaximal :=
    (RingHom.ker_isPrime ψ).isMaximal_of_ne_bot hne
  let := hm
  have hm' : (RingHom.ker φ).IsMaximal := by
    rw [← hcomp, ← RingHom.comap_ker]
    exact Ideal.comap_isMaximal_of_surjective _ Ideal.Quotient.mk_surjective
  have hle : RingHom.ker φ ≤ RingHom.ker (PowerSeries.constantCoeff.comp φ) := by
    intro a ha
    change PowerSeries.constantCoeff (φ a) = 0
    rw [ha, map_zero]
  have he := hm'.eq_of_le (RingHom.ker_isPrime (PowerSeries.constantCoeff.comp φ)).ne_top hle
  obtain ⟨a,ha,han⟩ := hbranch
  exact han (show a ∈ RingHom.ker φ from he ▸ ha)

end
end MaximalSeshadri.NodalLocal
end


end
end

end OAI
