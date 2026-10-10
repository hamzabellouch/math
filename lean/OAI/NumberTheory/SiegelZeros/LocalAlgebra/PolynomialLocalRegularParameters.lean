import Mathlib.Algebra.MvPolynomial.Equiv
import Mathlib.RingTheory.Jacobson.Ring
import Mathlib.RingTheory.KrullDimension.Polynomial
import OAI.NumberTheory.SiegelZeros.Selection.CoordinateBasisSplitting

namespace OAI

namespace SiegelZeros

section

noncomputable section
namespace SiegelZerosAwei.W09

variable (K : Type*) [Field K]

theorem polynomialMaximal_height (n : ℕ)
    (m : Ideal (MvPolynomial (Fin n) K)) [m.IsMaximal] :
    m.height = (n : ℕ∞) := by
  induction n with
  | zero =>
      let e := MvPolynomial.isEmptyAlgEquiv K (Fin 0)
      let p : Ideal K := m.comap e.symm.toRingHom
      let : p.IsMaximal := Ideal.comap_isMaximal_of_equiv e.symm
      have hp : p = ⊥ := p.eq_bot_or_top.resolve_right (Ideal.IsMaximal.ne_top (inferInstance : p.IsMaximal))
      calc
        m.height = p.height := (e.symm.toRingEquiv.height_comap m).symm
        _ = (0 : ℕ∞) := by rw [hp, Ideal.height_bot]
  | succ n ih =>
      let e := MvPolynomial.finSuccEquiv K n
      let P : Ideal (Polynomial (MvPolynomial (Fin n) K)) :=
        m.comap e.symm.toRingHom
      let : P.IsMaximal := Ideal.comap_isMaximal_of_equiv e.symm
      let p : Ideal (MvPolynomial (Fin n) K) := P.comap Polynomial.C
      let : p.IsMaximal := Polynomial.isMaximal_comap_C_of_isJacobsonRing P
      let : P.LiesOver p := ⟨rfl⟩
      calc
        m.height = P.height := (e.symm.toRingEquiv.height_comap m).symm
        _ = p.height + 1 := Polynomial.height_eq_height_add_one p P
        _ = ((n + 1 : ℕ) : ℕ∞) := by rw [ih p]; simp

theorem maximal_height_of_polynomial_equiv {A : Type*} [CommRing A]
    (n : ℕ) (e : A ≃+* MvPolynomial (Fin n) K)
    (m : Ideal A) [m.IsMaximal] : m.height = (n : ℕ∞) := by
  let : (m.map e).IsMaximal := Ideal.map_isMaximal_of_equiv e
  calc
    m.height = (m.map e).height := (e.height_map m).symm
    _ = (n : ℕ∞) := polynomialMaximal_height K n (m.map e)

theorem localized_maximal_comap_height {R A : Type*} [CommRing R] [CommRing A]
    [Algebra R A] (S : Submonoid R) [IsLocalization S A]
    (n : ℕ) (e : A ≃+* MvPolynomial (Fin n) K)
    (m : Ideal A) [m.IsMaximal] :
    (m.comap (algebraMap R A)).height = (n : ℕ∞) := by
  change (m.under R).height = (n : ℕ∞)
  rw [IsLocalization.height_under S m]
  exact maximal_height_of_polynomial_equiv K n e m

theorem prime_height_of_localized_polynomial_maximal {R A : Type*}
    [CommRing R] [CommRing A] [Algebra R A]
    (S : Submonoid R) [IsLocalization S A]
    (n : ℕ) (e : A ≃+* MvPolynomial (Fin n) K)
    (p : Ideal R) [p.IsPrime]
    (hdisj : Disjoint (S : Set R) (p : Set R))
    [(p.map (algebraMap R A)).IsMaximal] : p.height = (n : ℕ∞) := by
  calc
    p.height = (p.map (algebraMap R A)).height :=
      (IsLocalization.height_map_of_disjoint S p hdisj).symm
    _ = (n : ℕ∞) := maximal_height_of_polynomial_equiv K n e _

end SiegelZerosAwei.W09

end

end

section

noncomputable section
namespace WeightedTorusJets.PolynomialLocalResidueResolution

variable (K : Type*) [Field K] (n : ℕ)
variable (Q : Ideal (MvPolynomial (Fin n) K)) [Q.IsPrime]

theorem exists_regularParameters_actual_height :
    ∃ h : ℕ, Q.height = (h : ℕ∞) ∧
      ∃ xs : List (Localization.AtPrime Q),
        xs.length = h ∧ RingTheory.Sequence.IsRegular (Localization.AtPrime Q) xs ∧
        Ideal.ofList xs = IsLocalRing.maximalIdeal (Localization.AtPrime Q) := by
  classical
  obtain ⟨t, j, htfinite, hj, hcoord, ht⟩ := exists_coordinate_basis_indices K n Q
  let A := RemainingCoordinate j
  let F := SplitCoefficientField K t
  let Qs := coordinateSplitPrime K Q t j hj
  let hB := coordinateSplitPrime_basis K Q t j hj hcoord ht
  let m₀ := closedPolynomialIdeal K A t Qs hB
  let : m₀.IsMaximal := closedPolynomialIdeal_isMaximal K A t Qs hB
  let e₀ : Localization.AtPrime Q ≃+* Localization.AtPrime m₀ :=
    coordinateBasisClosedPointEquiv K Q t j hj hcoord ht
  let h := Fintype.card A
  let eFin : MvPolynomial A F ≃ₐ[F] MvPolynomial (Fin h) F :=
    MvPolynomial.renameEquiv F (Fintype.equivFin A)
  let m : Ideal (MvPolynomial (Fin h) F) := m₀.map eFin.toRingHom
  let : m.IsMaximal := (inferInstance : m₀.IsMaximal).map_bijective eFin.toRingHom eFin.bijective
  let e : Localization.AtPrime Q ≃+* Localization.AtPrime m :=
    e₀.trans (SiegelZeros.W23.atPrimeEquivOfRingEquiv eFin.toRingEquiv m₀)
  have hheight : Q.height = (h : ℕ∞) := by
    have he := ringKrullDim_eq_of_ringEquiv e
    rw [IsLocalization.AtPrime.ringKrullDim_eq_height Q (Localization.AtPrime Q),
      IsLocalization.AtPrime.ringKrullDim_eq_height m (Localization.AtPrime m),
      SiegelZerosAwei.W09.polynomialMaximal_height F h m] at he
    exact WithBot.coe_injective he
  refine ⟨h, hheight, ?_⟩
  exact SiegelZeros.W10.TriangularLocalParameters.polynomialMaximal_regularParameters_of_ringEquiv
    h F m e

end WeightedTorusJets.PolynomialLocalResidueResolution

end

end

end SiegelZeros

end OAI
