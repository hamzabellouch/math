import OAI.GroupTheory.PolycyclicRecognition.Algebra.ExteriorScalarDifference
import OAI.GroupTheory.PolycyclicRecognition.Algebra.PolynomialExteriorShiftOperators

namespace OAI

/-! # A high finite exterior power rules out a free polynomial orbit

The coefficient algebra is the actual acting group ring. Its finite algebra
presentation bounds the independent coordinates detected by the determinant.
-/

noncomputable section
namespace PolycyclicRecognition
open scoped MonoidAlgebra Polynomial IsMulCommutative
variable {K Q M : Type} [Field K] [CommGroup Q] [AddCommGroup M] [Module K M]

local instance higherExteriorEndRing (ρ : Representation K Q M) (n : ℕ) :
    Ring (Module.End K[Q] (higherExteriorRepresentation ρ n).asModule) :=
  Module.End.instRing (R := K[Q]) (N₁ := (higherExteriorRepresentation ρ n).asModule)

theorem higherExterior_free_orbit_bound
    (ρ : Representation K Q M) {r n : ℕ} (a : Fin r → K[Q])
    (ha : Algebra.adjoin K (Set.range a) = ⊤)
    [Module.Finite K[Q] (higherExteriorRepresentation ρ n).asModule]
    (c : Fin (n + 1) → K) (hc : Function.Injective c)
    (g : Q) (v : M) (hv : LinearIndependent K (fun i : ℕ => (ρ g ^ i) v)) : n ≤ r := by
  let S : Fin (n + 1) → Module.End K[Q] (higherExteriorRepresentation ρ n).asModule :=
    fun i => exteriorScalarDifferenceModule ρ n g (c i)
  have hS : ∀ i j, Commute (S i) (S j) :=
    fun i j => exteriorScalarDifferenceModule_commute ρ n g (c i) (c j)
  let := commuting_adjoin_isMulCommutative (R := K[Q]) S hS
  let C := Algebra.adjoin K[Q] (Set.range S)
  let := Module.End.isIntegral (R := K[Q])
    (M := (higherExteriorRepresentation ρ n).asModule)
  let := commuting_adjoin_finite (R := K[Q]) S hS
  let f : MvPolynomial (Fin (n + 1)) K →ₐ[K] C :=
    MvPolynomial.aeval (fun i => ⟨S i, Algebra.subset_adjoin (Set.mem_range_self i)⟩)
  let φ : C →ₐ[K] Module.End K (⋀[K]^n M) :=
    (representationEndForget (higherExteriorRepresentation ρ n)).comp (C.val.restrictScalars K)
  let α := φ.comp f
  let β₀ : MvPolynomial (Fin (n + 1)) K →ₐ[K] MvPolynomial (Fin n) K :=
    MvPolynomial.aeval (fun i => shiftProduct K n (c i))
  let E := exteriorPower.map n (polynomialOrbitMap (ρ g) v)
  have hE : Function.Injective E := polynomialOrbitExterior_injective (ρ g) v n hv
  have hα (i : Fin (n + 1)) : α (MvPolynomial.X i) = exteriorScalarDifference ρ n g (c i) := by
    change representationEndForget (higherExteriorRepresentation ρ n)
      ((MvPolynomial.aeval (fun j => (⟨S j, Algebra.subset_adjoin
        (Set.mem_range_self j)⟩ : C)) (MvPolynomial.X i)).val) = _
    rw [MvPolynomial.aeval_X]
    exact representationEndForget_difference ρ n g (c i)
  have hker : ∀ p, f p = 0 → β₀.rangeRestrict p = 0 := by
    intro p hp
    have hp' : α p = 0 := by
      change φ (f p) = 0
      rw [hp, map_zero]
    apply Subtype.ext
    change β₀ p = 0
    apply polynomialExterior_relation_detected K n (n + 1) c α E hE ?_ hp'
    intro i w
    rw [hα]
    exact LinearMap.congr_fun (polynomialOrbitExterior_scalarDifference (ρ g) v n (c i)) w
  have hB : β₀.range = shiftProductAlgebra K n c := MvPolynomial.aeval_range _
  have hx : ∃ x : Fin n → β₀.range, AlgebraicIndependent K x := by
    rw [hB]
    exact shiftProductAlgebra_independent K n c hc
  obtain ⟨x, hx⟩ := hx
  exact relation_quotient_independent_bound a ha f β₀.rangeRestrict
    β₀.rangeRestrict_surjective hker x hx

end PolycyclicRecognition

end

end OAI
