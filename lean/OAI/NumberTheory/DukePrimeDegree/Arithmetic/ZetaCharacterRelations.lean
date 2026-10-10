import OAI.NumberTheory.DukePrimeDegree.Arithmetic.ConjugateSubfields

namespace OAI

/-!
# Permutation character relations give zeta-order relations

The finite character identities used in Stark descent first give local
Euler determinant identities, then incomplete zeta identities in the
half-plane of convergence, and finally integer relations on zero orders.
-/

noncomputable section
open Module Filter Set
open scoped NumberField BigOperators Classical Topology

namespace DukePrimeDegree

open PrimeDegreePackets PrimeDegreePackets.GaloisIdealCharacter

variable {F E I : Type*} [Field F] [NumberField F] [Field E] [NumberField E]
variable [Algebra F E] [FiniteDimensional F E] [IsGalois F E] [Fintype I]
local instance : Fintype (E ≃ₐ[F] E) := Fintype.ofFinite _

theorem coset_euler_products_of_characters
    (L : I → IntermediateField F E) (p q : I → ℕ)
    (hχ : ∀ g,
      (∑ i, (p i : ℂ) * (Representation.ofMulAction ℂ (E ≃ₐ[F] E)
        ((E ≃ₐ[F] E) ⧸ (L i).fixingSubgroup)).character g) =
      ∑ i, (q i : ℂ) * (Representation.ofMulAction ℂ (E ≃ₐ[F] E)
        ((E ≃ₐ[F] E) ⧸ (L i).fixingSubgroup)).character g)
    (N : ℕ) (r : Nat.Primes) (s : ℂ) :
    (∏ i, cosetRationalEuler F E (L i) N r s ^ p i) =
      ∏ i, cosetRationalEuler F E (L i) N r s ^ q i := by
  by_cases hr : r.val ∣ N
  · simp only [cosetRationalEuler, ite_eq_left hr, one_pow, Finset.prod_const_one]
  simp only [cosetRationalEuler, ite_eq_right hr]
  simp_rw [← Finset.prod_pow]
  conv_lhs => rw [Finset.prod_comm]
  conv_rhs => rw [Finset.prod_comm]
  apply Finset.prod_congr rfl
  intro P _
  simp_rw [inv_pow]
  rw [Finset.prod_inv_distrib, Finset.prod_inv_distrib]
  congr 1
  simp_rw [← permutation_euler_det_eq]
  exact euler_det_products_eq_of_characters
    (V := fun i => MonoidAlgebra ℂ ((E ≃ₐ[F] E) ⧸ (L i).fixingSubgroup))
    (fun i => Representation.ofMulAction ℂ (E ≃ₐ[F] E)
      ((E ≃ₐ[F] E) ⧸ (L i).fixingSubgroup)) p q hχ _ _

theorem coset_products_of_characters
    (L : I → IntermediateField F E) [∀ i, NumberField.IsTotallyReal (L i)]
    (p q : I → ℕ)
    (hχ : ∀ g,
      (∑ i, (p i : ℂ) * (Representation.ofMulAction ℂ (E ≃ₐ[F] E)
        ((E ≃ₐ[F] E) ⧸ (L i).fixingSubgroup)).character g) =
      ∑ i, (q i : ℂ) * (Representation.ofMulAction ℂ (E ≃ₐ[F] E)
        ((E ≃ₐ[F] E) ⧸ (L i).fixingSubgroup)).character g)
    {N : ℕ} (hN : 0 < N) (hD : (NumberField.discr E).natAbs ∣ N)
    {s : ℂ} (hs : 1 < s.re) :
    (∏ i, cosetMeromorphic (canonicalRealEmbeddings (L i)) (degreePred_spec (L i)) N s ^ p i) =
      ∏ i, cosetMeromorphic (canonicalRealEmbeddings (L i)) (degreePred_spec (L i)) N s ^ q i := by
  have hp := hasProd_prod (s := Finset.univ) (fun i _ =>
    ((actual_coset_meromorphic_pairing F E (L i) (canonicalRealEmbeddings (L i))
      (degreePred_spec (L i)) N hN hD).2.1 s hs).pow (p i))
  have hq := hasProd_prod (s := Finset.univ) (fun i _ =>
    ((actual_coset_meromorphic_pairing F E (L i) (canonicalRealEmbeddings (L i))
      (degreePred_spec (L i)) N hN hD).2.1 s hs).pow (q i))
  exact hp.unique (hq.congr_fun (fun r => coset_euler_products_of_characters L p q hχ N r s))

theorem zeta_orders_of_characters
    (L : I → IntermediateField F E) [∀ i, NumberField.IsTotallyReal (L i)]
    (p q : I → ℕ)
    (hχ : ∀ g,
      (∑ i, (p i : ℂ) * (Representation.ofMulAction ℂ (E ≃ₐ[F] E)
        ((E ≃ₐ[F] E) ⧸ (L i).fixingSubgroup)).character g) =
      ∑ i, (q i : ℂ) * (Representation.ofMulAction ℂ (E ≃ₐ[F] E)
        ((E ≃ₐ[F] E) ⧸ (L i).fixingSubgroup)).character g)
    {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) :
    (∑ i, (p i : WithTop ℤ) * zetaZeroOrder (L i) β) =
      ∑ i, (q i : WithTop ℤ) * zetaZeroOrder (L i) β := by
  let N := (NumberField.discr E).natAbs
  have hN : 0 < N := Int.natAbs_pos.mpr (NumberField.discr_ne_zero E)
  have H := product_orders_eq_off_zero_one
    (fun i => cosetMeromorphic (canonicalRealEmbeddings (L i)) (degreePred_spec (L i)) N)
    (fun i => coset_analytic_off_zero_one _ _ N) p q
    (fun s hs => coset_products_of_characters L p q hχ hN (dvd_refl _) hs)
    (β : ℂ) (Complex.ofReal_ne_zero.mpr hβ0.ne') (by exact_mod_cast hβ1.ne)
  simpa only [← zetaZeroOrder_eq_coset_order _ _ N hβ0 hβ1] using H

theorem integer_zeta_orders_of_characters
    (L : I → IntermediateField F E) [∀ i, NumberField.IsTotallyReal (L i)]
    (c : I → ℤ)
    (hχ : ∀ g, (∑ i, (c i : ℂ) * (Representation.ofMulAction ℂ (E ≃ₐ[F] E)
      ((E ≃ₐ[F] E) ⧸ (L i).fixingSubgroup)).character g) = 0)
    {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1)
    (m : I → ℤ) (hm : ∀ i, zetaZeroOrder (L i) β = (m i : WithTop ℤ)) :
    (∑ i, c i * m i) = 0 := by
  have hc (i : I) : (c i : ℂ) = ((c i).toNat : ℂ) - ((-c i).toNat : ℂ) := by
    exact_mod_cast (Int.toNat_sub_toNat_neg (c i)).symm
  have hrel : ∀ g,
      (∑ i, ((c i).toNat : ℂ) * (Representation.ofMulAction ℂ (E ≃ₐ[F] E)
        ((E ≃ₐ[F] E) ⧸ (L i).fixingSubgroup)).character g) =
      ∑ i, ((-c i).toNat : ℂ) * (Representation.ofMulAction ℂ (E ≃ₐ[F] E)
        ((E ≃ₐ[F] E) ⧸ (L i).fixingSubgroup)).character g := by
    intro g
    have H := hχ g
    simpa only [hc, sub_mul, Finset.sum_sub_distrib, sub_eq_zero] using H
  have H := zeta_orders_of_characters L (fun i => (c i).toNat) (fun i => (-c i).toNat)
    hrel hβ0 hβ1
  simp only [hm] at H
  have H' : (∑ i, ((c i).toNat : ℤ) * m i) = ∑ i, ((-c i).toNat : ℤ) * m i := by
    exact_mod_cast H
  calc
    (∑ i, c i * m i) =
        (∑ i, ((c i).toNat : ℤ) * m i) - ∑ i, ((-c i).toNat : ℤ) * m i := by
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro i _
      rw [← sub_mul, Int.toNat_sub_toNat_neg]
    _ = 0 := sub_eq_zero.mpr H'

end DukePrimeDegree

end

end OAI
