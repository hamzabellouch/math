import Mathlib

namespace OAI

/-! Primary Eisenstein elements, residue characters, Gauss sums and first-moment target definitions. -/

section

noncomputable section
open scoped BigOperators
open Module
attribute [local instance] Classical.propDecidable

namespace CubicFirstMoment

def omega : ℂ := Complex.exp (2 * (Real.pi : ℂ) * Complex.I / 3)

def eisensteinRing : Subalgebra ℤ ℂ := Algebra.adjoin ℤ {omega}
abbrev Eisenstein := eisensteinRing

def omegaE : Eisenstein :=
  ⟨omega, Algebra.subset_adjoin (Set.mem_singleton omega)⟩

def norm (a : Eisenstein) : ℝ := Complex.normSq (a : ℂ)

def normNat (a : Eisenstein) : ℕ := ⌊norm a⌋₊

def primary (a : Eisenstein) : Prop := (3 : Eisenstein) ∣ a - 1

def primaryPrime (a : Eisenstein) : Prop := primary a ∧ Prime a

def modulus (a : Eisenstein) : Ideal Eisenstein := Ideal.span {a}

abbrev Residues (a : Eisenstein) := Eisenstein ⧸ modulus a

def residueRepresentative (a : Eisenstein) (v : Residues a) : Eisenstein :=
  Classical.choose (Ideal.Quotient.mk_surjective v)

def cubicSymbolAtPrime (p v : Eisenstein) : ℂ :=
  if IsUnit (Ideal.Quotient.mk (modulus p) v) then
    if h : ∃ j : Fin 3,
        Ideal.Quotient.mk (modulus p) (v ^ ((normNat p - 1) / 3)) =
          Ideal.Quotient.mk (modulus p) (omegaE ^ (j : ℕ)) then
      omega ^ ((Classical.choose h : Fin 3) : ℕ)
    else 0
  else 0

def additivePhase (p v : Eisenstein) : ℂ :=
  let z : ℂ := (v : ℂ) / (p : ℂ)
  Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (z + star z))

def gaussAtPrime (p : Eisenstein) : ℂ :=
  (Real.sqrt (norm p) : ℂ)⁻¹ *
    ∑' v : Residues p,
      cubicSymbolAtPrime p (residueRepresentative p v) *
        additivePhase p (residueRepresentative p v)

def cStar : ℝ := (2 * Real.pi) ^ (2 / 3 : ℝ) / (3 * Real.Gamma (2 / 3))

def primeCutoffSum (f : Eisenstein → ℂ) (X : ℝ) : ℂ :=
  ∑' p : Eisenstein, if primaryPrime p ∧ norm p ≤ X then f p else 0

def firstMomentScale (X : ℝ) : ℝ := X ^ (5 / 6 : ℝ) / Real.log X

def FirstMomentStatement : Prop :=
  Asymptotics.IsLittleO Filter.atTop
    (fun X : ℝ => primeCutoffSum gaussAtPrime X -
      (((6 / 5 : ℝ) * cStar * firstMomentScale X : ℝ) : ℂ))
    firstMomentScale

def theta (ℓ : ℤ) (a : Eisenstein) : ℂ := ((a : ℂ) / (‖(a : ℂ)‖ : ℂ)) ^ ℓ

def AngularComparisonStatement : Prop :=
  ∀ ℓ : ℤ, Asymptotics.IsLittleO Filter.atTop
    (primeCutoffSum (fun p => theta ℓ p *
       (gaussAtPrime p - ((cStar * norm p ^ (-1 / 6 : ℝ) : ℝ) : ℂ))))
    firstMomentScale

def AngularCancellationStatement : Prop :=
  ∀ ℓ : ℤ, ℓ ≠ 0 → Asymptotics.IsLittleO Filter.atTop
    (primeCutoffSum (fun p => theta ℓ p * gaussAtPrime p)) firstMomentScale

/-- The sharp first moment over all primary Eisenstein primes. -/
theorem patterson_firstMoment : FirstMomentStatement := by
  sorry

/-- Model comparison in every fixed integer angular mode. -/
theorem patterson_angularComparison : AngularComparisonStatement := by
  sorry

/-- Cancellation at the first-moment scale for each nonzero angular mode. -/
theorem patterson_angularCancellation : AngularCancellationStatement := by
  sorry

end CubicFirstMoment
end
end

end OAI
