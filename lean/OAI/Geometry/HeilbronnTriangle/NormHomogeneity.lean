import OAI.Geometry.HeilbronnTriangle.NormDeterminant

namespace OAI

noncomputable section
namespace Problem355.NormHomogeneity
open scoped BigOperators
open MvPolynomial

lemma isWeightedHomogeneous_map {R S V M : Type*} [CommSemiring R] [CommSemiring S]
    [AddCommMonoid M] (f : R →+* S) {w : V → M} {P : MvPolynomial V R} {d : M}
    (hP : P.IsWeightedHomogeneous w d) : (P.map f).IsWeightedHomogeneous w d := by
  intro m hm
  apply hP
  intro hz
  apply hm
  simp [MvPolynomial.coeff_map, hz]

lemma isWeightedHomogeneous_of_map {R S V M : Type*} [CommSemiring R] [CommSemiring S]
    [AddCommMonoid M] (f : R →+* S) (hf : Function.Injective f)
    {w : V → M} {P : MvPolynomial V R} {d : M}
    (hP : (P.map f).IsWeightedHomogeneous w d) : P.IsWeightedHomogeneous w d := by
  intro m hm
  apply hP
  intro hz
  apply hm
  apply hf
  simpa only [MvPolynomial.coeff_map, map_zero] using hz

open NormDeterminant
variable {ι K : Type*} [Fintype ι] [Field K]

def groupWeight (g : Fin 3) (v : Variables ι) : ℕ := if v.1 = g then 1 else 0

lemma groupWeight_eq_sum (g : Fin 3) (m : Variables ι →₀ ℕ) :
    Finsupp.weight (groupWeight g) m = ∑ i : Fin 3, ∑ ν : ι, m (g, i, ν) := by
  classical
  rw [Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp)]
  simp [groupWeight, Fintype.sum_prod_type]
  rw [Finset.sum_eq_single g]
  · simp
  · intro j hj hjg
    simp [hjg]
  · simp

lemma coordinateForm_isWeightedHomogeneous (β : ι → K) (g j i : Fin 3) :
    (coordinateForm β j i).IsWeightedHomogeneous (groupWeight g)
      (if j = g then 1 else 0) := by
  classical
  apply IsWeightedHomogeneous.sum
  intro ν hν
  simpa only [groupWeight] using
    (isWeightedHomogeneous_X (R := K) (groupWeight g) (j, i, ν)).C_mul (β ν)

theorem determinantPolynomial_isWeightedHomogeneous (β : ι → K) (g : Fin 3) :
    (determinantPolynomial β).IsWeightedHomogeneous (groupWeight g) 1 := by
  classical
  rw [determinantPolynomial, Matrix.det_apply']
  apply IsWeightedHomogeneous.sum
  intro σ hσ
  have hp : (∏ j : Fin 3, coordinateForm β j (σ j)).IsWeightedHomogeneous
      (groupWeight g) 1 := by
    simpa using IsWeightedHomogeneous.prod Finset.univ
      (fun j : Fin 3 => coordinateForm β j (σ j))
      (fun j : Fin 3 => if j = g then 1 else 0)
      (fun j _ => coordinateForm_isWeightedHomogeneous β g j (σ j))
  simpa using hp.C_mul ((Equiv.Perm.sign σ : ℤ) : K)

variable {F : Type*} [Field F] [Algebra F K] [FiniteDimensional F K] [IsGalois F K]

theorem galoisProduct_isWeightedHomogeneous {V M : Type*} [AddCommMonoid M]
    {w : V → M} {P : MvPolynomial V K} {d : M}
    (hP : P.IsWeightedHomogeneous w d) :
    (NormPolynomial.galoisProduct (F := F) P).IsWeightedHomogeneous w
      (Module.finrank F K • d) := by
  classical
  have hcard : Fintype.card (K ≃ₐ[F] K) = Module.finrank F K := by
    simpa only [Nat.card_eq_fintype_card] using IsGalois.card_aut_eq_finrank F K
  unfold NormPolynomial.galoisProduct
  simpa only [Finset.sum_const, Finset.card_univ, hcard] using
    IsWeightedHomogeneous.prod Finset.univ
      (fun σ : K ≃ₐ[F] K => MvPolynomial.map σ.toRingHom P)
      (fun _ => d) (fun σ _ => isWeightedHomogeneous_map σ.toRingHom hP)

theorem normPolynomial_isWeightedHomogeneous {V M : Type*} [AddCommMonoid M]
    {w : V → M} {P : MvPolynomial V K} {d : M}
    (hP : P.IsWeightedHomogeneous w d) :
    (NormPolynomial.normPolynomial (F := F) P).IsWeightedHomogeneous w
      (Module.finrank F K • d) := by
  apply isWeightedHomogeneous_of_map (algebraMap F K) (algebraMap F K).injective
  rw [NormPolynomial.map_normPolynomial]
  exact galoisProduct_isWeightedHomogeneous hP

theorem normDeterminantPolynomial_isWeightedHomogeneous (β : ι → K) (g : Fin 3) :
    (normDeterminantPolynomial (F := F) β).IsWeightedHomogeneous
      (groupWeight g) (Module.finrank F K) := by
  simpa [normDeterminantPolynomial] using
    normPolynomial_isWeightedHomogeneous (F := F)
      (determinantPolynomial_isWeightedHomogeneous β g)

theorem normDeterminantPolynomial_support_degree (β : ι → K)
    (m : Variables ι →₀ ℕ)
    (hm : (normDeterminantPolynomial (F := F) β).coeff m ≠ 0) (g : Fin 3) :
    (∑ i : Fin 3, ∑ ν : ι, m (g, i, ν)) = Module.finrank F K := by
  rw [← groupWeight_eq_sum]
  exact normDeterminantPolynomial_isWeightedHomogeneous β g hm

end Problem355.NormHomogeneity

end

end OAI
