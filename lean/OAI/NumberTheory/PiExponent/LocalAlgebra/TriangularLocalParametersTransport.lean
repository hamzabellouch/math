import OAI.NumberTheory.PiExponent.LocalAlgebra.TriangularLocalParametersAssembly

namespace OAI

noncomputable section
namespace PiExponentSiegel.W10.TriangularLocalParameters

open RingTheory.Sequence

variable {R S : Type*} [CommRing R] [CommRing S]

theorem regular_map_ringEquiv (e : R ≃+* S) (xs : List R)
    (hxs : IsRegular R xs) : IsRegular S (xs.map e.toRingHom) := by
  apply (e.toAddEquiv.isRegular_congr ?_).mp hxs
  apply List.forall₂_map_right_iff.mpr
  apply List.forall₂_same.mpr
  intro a _ z
  exact e.map_mul a z

theorem regularParameters_transport [IsLocalRing R] [IsLocalRing S]
    (e : R ≃+* S) (n : ℕ)
    (h : ∃ xs : List R, xs.length = n ∧ IsRegular R xs ∧
      Ideal.ofList xs = IsLocalRing.maximalIdeal R) :
    ∃ ys : List S, ys.length = n ∧ IsRegular S ys ∧
      Ideal.ofList ys = IsLocalRing.maximalIdeal S := by
  obtain ⟨xs, hlen, hreg, hspan⟩ := h
  refine ⟨xs.map e.toRingHom, ?_, regular_map_ringEquiv e xs hreg, ?_⟩
  · simpa using hlen
  · rw [← Ideal.map_ofList, hspan]
    exact IsLocalRing.map_maximalIdeal_of_surjective e.toRingHom e.surjective

theorem polynomialMaximal_regularParameters_of_ringEquiv (n : ℕ) (K : Type*) [Field K]
    (m : Ideal (MvPolynomial (Fin n) K)) [m.IsMaximal]
    [IsLocalRing R] (e : R ≃+* Localization.AtPrime m) :
    ∃ xs : List R, xs.length = n ∧ IsRegular R xs ∧
      Ideal.ofList xs = IsLocalRing.maximalIdeal R :=
  regularParameters_transport e.symm n (polynomialMaximal_regularParameters n K m)

end PiExponentSiegel.W10.TriangularLocalParameters

end

end OAI
