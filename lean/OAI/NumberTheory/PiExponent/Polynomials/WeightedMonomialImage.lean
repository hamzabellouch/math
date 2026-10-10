import OAI.NumberTheory.PiExponent.Polynomials.GradedSubring
import OAI.NumberTheory.PiExponent.Polynomials.WeightedMonomialMap

namespace OAI

noncomputable section

namespace PiExponent.WeightedCompactification

open MvPolynomial DirectSum

variable {R ι σ : Type*} [CommRing R]

attribute [local instance] MvPolynomial.gradedAlgebra

abbrev monomialImage (a : σ → ι →₀ ℕ) := (homogeneousMonomialMap (R := R) a).range

abbrev ambientGrade (R ι : Type*) [CommRing R] (n : ℕ) :=
  (homogeneousSubmodule Unit (MvPolynomial ι R) n).restrictScalars ℤ

def gradedMonomialMapInt (a : σ → ι →₀ ℕ) :
    homogeneousSubmodule σ R →+*ᵍ ambientGrade R ι where
  __ := homogeneousMonomialMap a
  map_mem := homogeneousMonomialMap_homogeneous a

theorem monomialImage_homogeneous (a : σ → ι →₀ ℕ) (n : ℕ)
    (p : MvPolynomial Unit (MvPolynomial ι R)) (hp : p ∈ monomialImage a) :
    (decompose (ambientGrade R ι) p n : MvPolynomial Unit (MvPolynomial ι R)) ∈
      monomialImage a := by
  obtain ⟨q, rfl⟩ := hp
  refine ⟨decompose (homogeneousSubmodule σ R) q n, ?_⟩
  exact (gradedMonomialMapInt a).map_directSumDecompose

abbrev imageGrade (a : σ → ι →₀ ℕ) := subringGrade (ambientGrade R ι) (monomialImage a)

instance imageGradedAlgebra (a : σ → ι →₀ ℕ) : GradedAlgebra (imageGrade (R := R) a) :=
  subringGradedAlgebra _ _ (monomialImage_homogeneous a)

def gradedImageMap (a : σ → ι →₀ ℕ) :
    homogeneousSubmodule σ R →+*ᵍ imageGrade (R := R) a where
  __ := (homogeneousMonomialMap a).rangeRestrict
  map_mem := homogeneousMonomialMap_homogeneous a

theorem gradedImageMap_surjective (a : σ → ι →₀ ℕ) :
    Function.Surjective (gradedImageMap (R := R) a) :=
  (homogeneousMonomialMap a).rangeRestrict_surjective

def monomialQuotientEquivImage (a : σ → ι →₀ ℕ) :
    (MvPolynomial σ R ⧸ (monomialHomogeneousIdeal (R := R) a).toIdeal) ≃+* monomialImage (R := R) a :=
  RingHom.quotientKerEquivRange (homogeneousMonomialMap a)

instance monomialHomogeneousIdeal_isPrime [IsDomain R] (a : σ → ι →₀ ℕ) :
    (monomialHomogeneousIdeal (R := R) a).toIdeal.IsPrime :=
  RingHom.ker_isPrime (homogeneousMonomialMap a)

abbrev imageCoordinate (a : σ → ι →₀ ℕ) (s : σ) : monomialImage (R := R) a :=
  ⟨homogeneousMonomialMap a (X s), ⟨X s, rfl⟩⟩

theorem imageCoordinate_mem (a : σ → ι →₀ ℕ) (s : σ) :
    imageCoordinate (R := R) a s ∈ imageGrade a 1 :=
  homogeneousMonomialMap_homogeneous a (isHomogeneous_X R s)

def imageEvaluation (a : σ → ι →₀ ℕ) : monomialImage (R := R) a →+* MvPolynomial ι R :=
  (eval₂Hom (RingHom.id _) (fun _ : Unit => 1)).comp (monomialImage a).subtype

@[simp]
theorem imageEvaluation_coordinate (a : σ → ι →₀ ℕ) (s : σ) :
    imageEvaluation (R := R) a (imageCoordinate a s) = monomial (a s) 1 := by
  simp [imageEvaluation, imageCoordinate, homogeneousMonomialMap]

theorem unit_homogeneous_formula {p : MvPolynomial Unit R} {n : ℕ}
    (hp : p.IsHomogeneous n) :
    p = X () ^ n * C (eval (fun _ : Unit => 1) p) := by
  have he : eval₂Hom C (fun _ : Unit => X () * (1 : MvPolynomial Unit R)) =
      RingHom.id (MvPolynomial Unit R) := by
    apply MvPolynomial.ringHom_ext
    · intro r; simp
    · intro u; cases u; simp
  have hc : (C : R →+* MvPolynomial Unit R).comp (eval₂Hom (RingHom.id _) (fun _ : Unit => 1)) =
      eval₂Hom C (fun _ : Unit => (1 : MvPolynomial Unit R)) := by
    apply MvPolynomial.ringHom_ext <;> intro r <;> simp
  have h := PiExponentSeshadri.Projective.homogeneous_eval₂_scale hp C
    (fun _ : Unit => (1 : MvPolynomial Unit R)) (X ())
  change (eval₂Hom C (fun _ : Unit => X () * (1 : MvPolynomial Unit R))) p =
    X () ^ n * (eval₂Hom C (fun _ : Unit => (1 : MvPolynomial Unit R))) p at h
  rw [he, ← hc] at h
  exact h

theorem imageEvaluation_homogeneous_eq_zero (a : σ → ι →₀ ℕ)
    {p : monomialImage (R := R) a} {n : ℕ} (hp : p ∈ imageGrade a n)
    (he : imageEvaluation a p = 0) : p = 0 := by
  apply Subtype.ext
  have h := unit_homogeneous_formula hp
  change eval (fun _ : Unit => 1) p.1 = 0 at he
  change p.1 = X () ^ n * C (eval (fun _ : Unit => 1) p.1) at h
  rw [he, map_zero, mul_zero] at h
  exact h

end PiExponent.WeightedCompactification

end

end OAI
