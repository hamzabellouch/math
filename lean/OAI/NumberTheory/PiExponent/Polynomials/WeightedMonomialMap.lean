import Mathlib.RingTheory.GradedAlgebra.Homogeneous.Maps
import OAI.NumberTheory.PiExponent.Geometry.ProjectiveCharts

namespace OAI

noncomputable section

namespace PiExponent.WeightedCompactification

open MvPolynomial

variable {R ι σ : Type*} [CommRing R]

attribute [local instance] MvPolynomial.gradedAlgebra

def affineMonomialMap (a : σ → ι →₀ ℕ) : MvPolynomial σ R →+* MvPolynomial ι R :=
  eval₂Hom C (fun s => monomial (a s) 1)

def homogeneousMonomialMap (a : σ → ι →₀ ℕ) :
    MvPolynomial σ R →+* MvPolynomial Unit (MvPolynomial ι R) :=
  eval₂Hom (C.comp C) (fun s => X () * C (monomial (a s) 1))

@[simp]
theorem homogeneousMonomialMap_X (a : σ → ι →₀ ℕ) (s : σ) :
    homogeneousMonomialMap (R := R) a (X s) = X () * C (monomial (a s) 1) := by
  simp [homogeneousMonomialMap]

theorem homogeneousMonomialMap_homogeneous (a : σ → ι →₀ ℕ)
    {p : MvPolynomial σ R} {n : ℕ} (hp : p.IsHomogeneous n) :
    (homogeneousMonomialMap a p).IsHomogeneous n := by
  have h : (homogeneousMonomialMap a p).IsHomogeneous (1 * n) :=
    hp.eval₂ (C.comp C) (fun s => X () * C (monomial (a s) 1))
      (fun r => isHomogeneous_C _ _) (fun s => by
        simpa only [mul_comm] using isHomogeneous_C_mul_X (monomial (a s) (1 : R)) ())
  rw [Nat.one_mul] at h
  exact h

def gradedMonomialMap (a : σ → ι →₀ ℕ) :
    homogeneousSubmodule σ R →+*ᵍ homogeneousSubmodule Unit (MvPolynomial ι R) where
  __ := homogeneousMonomialMap a
  map_mem := homogeneousMonomialMap_homogeneous a

def monomialHomogeneousIdeal (a : σ → ι →₀ ℕ) :
    HomogeneousIdeal (homogeneousSubmodule σ R) :=
  HomogeneousIdeal.comap (gradedMonomialMap a) ⊥

theorem monomialHomogeneousIdeal_eq_ker (a : σ → ι →₀ ℕ) :
    (monomialHomogeneousIdeal (R := R) a).toIdeal =
      RingHom.ker (homogeneousMonomialMap a) := by
  rfl

theorem homogeneousMonomialMap_formula (a : σ → ι →₀ ℕ)
    {p : MvPolynomial σ R} {n : ℕ} (hp : p.IsHomogeneous n) :
    homogeneousMonomialMap a p = X () ^ n * C (affineMonomialMap a p) := by
  have h := PiExponentSeshadri.Projective.homogeneous_eval₂_scale hp
    (C.comp C) (fun s => C (monomial (a s) 1)) (X ())
  have he : (C : MvPolynomial ι R →+* MvPolynomial Unit (MvPolynomial ι R)).comp
      (affineMonomialMap a) = eval₂Hom (C.comp C) (fun s => C (monomial (a s) 1)) := by
    apply MvPolynomial.ringHom_ext <;> intro r <;> simp [affineMonomialMap]
  change homogeneousMonomialMap a p = X () ^ n *
    (eval₂Hom (C.comp C) (fun s => C (monomial (a s) 1))) p at h
  rw [← he] at h
  exact h

end PiExponent.WeightedCompactification

end

end OAI
