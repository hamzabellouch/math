import OAI.RepresentationTheory.RestrictedTilting.FormalAssociatedAction

namespace OAI

namespace FiberFunctorProof
open CategoryTheory CategoryTheory.MonoidalCategory Matrix
open scoped TensorProduct BigOperators Pointwise
universe u
variable (k : Type u) [Field k] [Infinite k]
attribute [local instance 1100] HahnSeries.instAlgebra
variable (ι : Type u) [Fintype ι] [DecidableEq ι]
variable (ρ : Representation k (Multiplicative k) (ι → k))
variable (P : Matrix ι ι (Polynomial k))
variable (hP : ∀ t : k, polynomialMatrixEval P t = LinearMap.toMatrix' (ρ (Multiplicative.ofAdd t)))
variable (d : ℕ) (hd : ∀ i j, (P i j).natDegree ≤ d)
local notation "N" => associatedSectionsSubmodule k ι ρ
local notation "A" => MvPolynomial (Fin 2) k
local notation "I" => MvPolynomial.idealOfVars (Fin 2) k
local notation "H" => planeCompletion k
local notation "K" => LaurentSeries k
local notation "σ" => associatedSectionsRepresentation k ι ρ
local notation "hσ" => associatedSections_planeCompatible k ι ρ
local notation "W" => associatedNumeratorLinear k ι ρ P hP d hd
local notation "Z" => associatedDenominatorLinear k ι ρ P hP d hd
local notation "hx" => And.left (associatedSections_regular k ι ρ P hP)
local notation "hy" => And.right (associatedSections_regular k ι ρ P hP)
variable [Module.Finite k ((associatedSectionsSubmodule k ι ρ) ⧸
  planeJetRelation (M := associatedSectionsSubmodule k ι ρ) k 1)]
local notation "T" => planeJetFD k σ hσ 1

omit [Infinite k] in
lemma ofPowerSeriesAlg_apply_eq (f : PowerSeries k) :
    (HahnSeries.ofPowerSeriesAlg ℤ k) f = HahnSeries.ofPowerSeries ℤ k f := rfl

noncomputable def formalLineParameter : K :=
  HahnSeries.ofPowerSeries ℤ k PowerSeries.X

omit [Infinite k] in
lemma formalLineParameter_ne_zero : formalLineParameter k ≠ 0 := by
  intro hz
  apply PowerSeries.X_ne_zero (R := k)
  exact HahnSeries.ofPowerSeries_injective (hz.trans (map_zero _).symm)

noncomputable def associatedFieldTrivialization
    (s : (j : ℕ) → T ⟶ planeJetFD k σ hσ (j+1)) (hs0 : s 0 = 𝟙 _)
    (hs : ∀ j, s (j+1) ≫ planeJetTransitionHom k σ hσ (j+1) = s j) : (K ⊗[k] T) ≃ₗ[K] (ι → K) := by
  letI : Algebra H K := (formalLineFieldMap k).toRingHom.toAlgebra
  exact fieldCoordinateTrivialization (formalPlaneTrivialization k σ hσ s hs0 hs hx hy)
    (completedCoordinates I W) (completedDenominator I Z)
    (algebraMap A H ((MvPolynomial.X 0)^ (d+d)))
    (completedCoordinates_denominator I W Z _ (associatedNumerator_denominator k ι ρ P hP d hd))
    (completedDenominator_coordinates I W Z _ (associatedDenominator_numerator k ι ρ P hP d hd))
    (by
      change formalLineFieldMap k (algebraMap A H ((MvPolynomial.X 0)^(d+d))) ≠ 0
      rw [map_pow, map_pow]
      exact pow_ne_zero _ (formalLineFieldMap_X_ne_zero k))

lemma associatedFieldTrivialization_one
    (s : (j : ℕ) → T ⟶ planeJetFD k σ hσ (j+1)) (hs0 : s 0 = 𝟙 _)
    (hs : ∀ j, s (j+1) ≫ planeJetTransitionHom k σ hσ (j+1) = s j)
    (v : T) (i : ι) :
    associatedFieldTrivialization k ι ρ P hP d hd s hs0 hs (1 ⊗ₜ[k] v) i =
      HahnSeries.ofPowerSeries ℤ k
        (formalLineMap k (formalAssociatedCoordinates k ι ρ P hP d hd s hs v i)) := by
  let : Algebra H K := (formalLineFieldMap k).toRingHom.toAlgebra
  dsimp only [associatedFieldTrivialization]
  rw [fieldCoordinateTrivialization_one, formalPlaneTrivialization_one_tmul]
  rfl

lemma associatedFieldTrivialization_unipotent_one
    (s : (j : ℕ) → T ⟶ planeJetFD k σ hσ (j+1)) (hs0 : s 0 = 𝟙 _)
    (hs : ∀ j, s (j+1) ≫ planeJetTransitionHom k σ hσ (j+1) = s j)
    (t : k) (v : T) :
    associatedFieldTrivialization k ι ρ P hP d hd s hs0 hs
      (1 ⊗ₜ[k] ((planeJetFD k σ hσ 1).ρ (unipotent k t) v)) =
      polynomialMatrixEval P (algebraMap k K t / (formalLineParameter k)^2) *ᵥ
        associatedFieldTrivialization k ι ρ P hP d hd s hs0 hs (1 ⊗ₜ[k] v) := by
  apply funext
  intro i
  have he := congrArg (HahnSeries.ofPowerSeriesAlg ℤ k)
    (formalAssociatedCoordinates_unipotent k ι ρ P hP d hd s hs t v i)
  simp only [map_mul, map_pow, map_sum] at he
  have hc (j : ι) : (HahnSeries.ofPowerSeriesAlg ℤ k)
      (clearedPolynomial (P i j) (algebraMap k (PowerSeries k) t)
        ((PowerSeries.X : PowerSeries k)^2) d) =
      (formalLineParameter k)^(2*d) *
        Polynomial.aeval (algebraMap k K t / (formalLineParameter k)^2) (P i j) := by
    have hc := clearedPolynomial_eval (HahnSeries.ofPowerSeriesAlg ℤ k) (P i j)
      (algebraMap k (PowerSeries k) t) ((PowerSeries.X : PowerSeries k)^2) d (hd i j)
      (by
        rw [map_pow]
        exact pow_ne_zero 2 (formalLineParameter_ne_zero k))
    simpa only [map_pow, AlgHom.commutes, ofPowerSeriesAlg_apply_eq, formalLineParameter, ← pow_mul, div_eq_mul_inv] using hc
  simp only [hc, mul_assoc, ← Finset.mul_sum] at he
  apply mul_left_cancel₀ (pow_ne_zero (2*d) (formalLineParameter_ne_zero k))
  simpa only [associatedFieldTrivialization_one, Matrix.mulVec, dotProduct, polynomialMatrixEval,
    formalLineParameter, ofPowerSeriesAlg_apply_eq] using he
end FiberFunctorProof

end OAI
