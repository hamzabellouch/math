import OAI.LinearAlgebra.CirculantHadamard.AlternatingProducts
import OAI.LinearAlgebra.CirculantHadamard.AlternatingNorm

namespace OAI

universe uI uK uR

/-!
# Clearing the actual alternating fraction

The field formula for an integral alternating product is first converted to
an identity in its coefficient ring. Arbitrary complex homomorphisms are then
applied to that identity, without extending them to the field of fractions.
The only nonvanishing inputs are the individual character values.
-/

namespace CirculantHadamard

open scoped BigOperators

theorem oddSubsetProduct_ne_zero {I : Type uI} {K : Type uK} [Field K]
    (t : Finset I) (x : Finset I → K)
    (hx : ∀ S ⊆ t, x S ≠ 0) : oddSubsetProduct t x ≠ 0 := by
  classical
  apply Finset.prod_ne_zero_iff.mpr
  intro S hS
  exact hx S (Finset.mem_powerset.mp (Finset.mem_filter.mp hS).1)

/-- An equality in the fraction field genuinely clears to the coefficient
ring. The field embedding is used only to reflect this polynomial identity. -/
theorem cleared_alternatingProduct_identity {I : Type uI} {R : Type uR} {K : Type uK}
    [CommRing R] [Field K] (f : R →+* K) (hf : Function.Injective f)
    (t : Finset I) (x : Finset I → R) (z : R)
    (hx : ∀ S ⊆ t, f (x S) ≠ 0)
    (hz : f z = alternatingProduct t (fun S => f (x S))) :
    z * oddSubsetProduct t x = evenSubsetProduct t x := by
  have hodd : f (oddSubsetProduct t x) =
      oddSubsetProduct t (fun S => f (x S)) :=
    map_oddSubsetProduct f.toMonoidHom t x
  have heven : f (evenSubsetProduct t x) =
      evenSubsetProduct t (fun S => f (x S)) :=
    map_evenSubsetProduct f.toMonoidHom t x
  apply hf
  rw [map_mul, hodd, heven, hz, alternatingProduct_eq_even_div_odd]
  exact div_mul_cancel₀ _ (oddSubsetProduct_ne_zero t (fun S => f (x S)) hx)

/-- Once the actual alternating fraction belongs to the coefficient ring,
every complex homomorphism has modulus one if each character value has the
same positive modulus. Subset parity supplies the equal factor counts. -/
theorem norm_hom_integral_alternatingProduct {I : Type uI} {R : Type uR} {K : Type uK}
    [CommRing R] [Field K] (f : R →+* K) (hf : Function.Injective f)
    (t : Finset I) (ht : t.Nonempty) (x : Finset I → R) (z : R)
    (hx : ∀ S ⊆ t, f (x S) ≠ 0)
    (hz : f z = alternatingProduct t (fun S => f (x S)))
    (σ : R →+* ℂ) (c : ℝ) (hc : 0 < c)
    (hnorm : ∀ S ⊆ t, ‖σ (x S)‖ = c) : ‖σ z‖ = 1 := by
  classical
  apply AlternatingNorm.norm_eq_one_of_balanced_products σ x
    (t.powerset.filter (fun S => Even S.card))
    (t.powerset.filter (fun S => Odd S.card)) z c hc
    (card_even_subsets_eq_card_odd_subsets t ht)
  · intro S hS
    exact hnorm S (Finset.mem_powerset.mp (Finset.mem_filter.mp hS).1)
  · intro S hS
    exact hnorm S (Finset.mem_powerset.mp (Finset.mem_filter.mp hS).1)
  · exact cleared_alternatingProduct_identity f hf t x z hx hz

end CirculantHadamard

end OAI
