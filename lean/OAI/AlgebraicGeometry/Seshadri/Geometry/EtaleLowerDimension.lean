import Mathlib

namespace OAI


                                             
section

namespace MaximalSeshadri.EtaleDimension
noncomputable section
open IsLocalRing

lemma polynomial_point_height (K : Type*) [Field K] (n : ℕ)
    (f : MvPolynomial (Fin n) K →ₐ[K] K) : (RingHom.ker f).height = n := by
  induction n with
  | zero =>
    have h := Ideal.height_le_ringKrullDim_of_ne_top (R := MvPolynomial (Fin 0) K)
      (RingHom.ker_ne_top f)
    simp only [MvPolynomial.ringKrullDim_of_isNoetherianRing,
      ringKrullDim_eq_zero_of_field, ENat.card_eq_coe_fintype_card, Fintype.card_fin,
      Nat.cast_zero, zero_add] at h
    have hh : (RingHom.ker f).height ≤ 0 := by exact_mod_cast h
    simpa only [Nat.cast_zero] using le_antisymm hh (bot_le : 0 ≤ (RingHom.ker f).height)
  | succ n ih =>
    let e := MvPolynomial.finSuccEquiv K n
    let g : Polynomial (MvPolynomial (Fin n) K) →ₐ[K] K := f.comp e.symm.toAlgHom
    let h : MvPolynomial (Fin n) K →ₐ[K] K := g.comp (Polynomial.CAlgHom (R := K))
    let : (RingHom.ker g).IsMaximal := RingHom.ker_isMaximal_of_surjective g
      (fun k => ⟨algebraMap K _ k,g.commutes k⟩)
    let : (RingHom.ker g).LiesOver (RingHom.ker h) := ⟨by rfl⟩
    have H := Polynomial.height_eq_height_add_one (RingHom.ker h) (RingHom.ker g)
    have he : (RingHom.ker g).height = (RingHom.ker f).height :=
      e.symm.toRingEquiv.height_comap (RingHom.ker f)
    rw [he,ih h] at H
    simpa only [Nat.cast_add,Nat.cast_one] using H

lemma polynomial_point_height_finite (K ι : Type*) [Field K] [Fintype ι]
    (f : MvPolynomial ι K →ₐ[K] K) : (RingHom.ker f).height = Fintype.card ι := by
  let e := MvPolynomial.renameEquiv K (Fintype.equivFin ι)
  have h := polynomial_point_height K (Fintype.card ι) (f.comp e.symm.toAlgHom)
  have he : (RingHom.ker (f.comp e.symm.toAlgHom)).height = (RingHom.ker f).height :=
    e.symm.toRingEquiv.height_comap (RingHom.ker f)
  rwa [he] at h

theorem etale_principal_dimension_lower (K S ι : Type*) [Field K] [CommRing S]
    [Fintype ι] [Algebra K S] [Algebra (MvPolynomial ι K) S]
    [IsScalarTower K (MvPolynomial ι K) S] [Algebra.Etale (MvPolynomial ι K) S]
    (f : S →ₐ[K] K) (r : S) (hr : f r = 0) :
    (Fintype.card ι : WithBot ℕ∞) ≤ ringKrullDim (S ⧸ Ideal.span {r}) + 1 := by
  let : IsNoetherianRing S := Algebra.FiniteType.isNoetherianRing (MvPolynomial ι K) S
  let g : MvPolynomial ι K →ₐ[K] S := IsScalarTower.toAlgHom K (MvPolynomial ι K) S
  let p := RingHom.ker (f.comp g)
  let P := RingHom.ker f
  let : p.IsPrime := RingHom.ker_isPrime (f.comp g)
  let : P.IsPrime := RingHom.ker_isPrime f
  let : P.LiesOver p := ⟨by rfl⟩
  have H := Ideal.height_eq_height_add_of_liesOver_of_hasGoingDown p P
  have hh : p.height ≤ P.height := H ▸ le_add_of_nonneg_right bot_le
  rw [show p.height = Fintype.card ι from polynomial_point_height_finite K ι (f.comp g)] at hh
  have hh' : (Fintype.card ι : WithBot ℕ∞) ≤ (P.height : WithBot ℕ∞) := by exact_mod_cast hh
  exact hh'.trans (Ideal.height_le_ringKrullDim_quotient_add_one hr)

end
end MaximalSeshadri.EtaleDimension

end


end OAI
