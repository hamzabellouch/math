import OAI.GroupTheory.PolycyclicRecognition.Algebra.AlgebraicIndependentPrimeQuotient
import Mathlib.RingTheory.AlgebraicIndependent.TranscendenceBasis
import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic

namespace OAI

/-! # A generator bound for independent coordinates in a finite algebra

The algebra may have zero divisors. Passing to a prime quotient that preserves
the chosen independent coordinates reduces the bound to the domain case.
-/

noncomputable section
namespace PolycyclicRecognition
open scoped Cardinal
variable {K C : Type} [Field K] [CommRing C] [Algebra K C]

theorem algebraicIndependent_card_le_of_finite_adjoin {r n : ℕ} (v : Fin r → C)
    [Module.Finite (Algebra.adjoin K (Set.range v)) C]
    (x : Fin n → C) (hx : AlgebraicIndependent K x) : n ≤ r := by
  obtain ⟨I, hI, hxI⟩ := algebraicIndependent_prime_quotient x hx
  let := hI
  let D := C ⧸ I
  let S := Algebra.adjoin K (Set.range v)
  let f : C →ₐ[K] D := Ideal.Quotient.mkₐ K I
  let T := S.map f
  let w : Fin r → D := f ∘ v
  have hT : T = Algebra.adjoin K (Set.range w) := by
    simp only [T, S, AlgHom.map_adjoin, ← Set.range_comp, w]
  let ψ : S →ₐ[K] T := (f.comp S.val).codRestrict T (fun a => ⟨a, a.property, rfl⟩)
  let : Algebra S T := ψ.toRingHom.toAlgebra
  let : IsScalarTower S T D := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  let : Module.Finite S D := Module.Finite.of_surjective
    (Ideal.Quotient.mkₐ S I).toLinearMap (Ideal.Quotient.mkₐ_surjective S I)
  let : Algebra.IsIntegral S D := Algebra.IsIntegral.of_finite S D
  have hTD : Algebra.IsIntegral T D := Algebra.IsIntegral.tower_top (R := S)
  have : Algebra.IsIntegral (Algebra.adjoin K (Set.range w)) D := hT ▸ hTD
  have hbound := Algebra.IsAlgebraic.trdeg_le_cardinalMk K (Set.range w)
  have hc : Cardinal.mk (Fin n) ≤ Cardinal.mk (Fin r) :=
    (hxI.cardinalMk_le_trdeg.trans hbound).trans Cardinal.mk_range_le
  simpa using hc

end PolycyclicRecognition

end

end OAI
