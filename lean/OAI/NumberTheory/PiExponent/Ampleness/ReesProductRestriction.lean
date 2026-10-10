import OAI.NumberTheory.PiExponent.Ampleness.ReesProductPower

namespace OAI

namespace PiExponent.ReesProductRestriction
noncomputable section
open PiExponentSeshadri.ReesGrading
open PiExponent.ReesGradedModule PiExponent.ReesPolynomialPresentation
open PiExponent.GradedPolynomialLaurent PiExponent.GradedLocalizationExact PiExponent.GradedCech
open PiExponent.ReesLocalizedIntersections PiExponent.ReesProductChart PiExponent.ReesProductPower
attribute [local instance] MvPolynomial.weightedGradedAlgebra
variable {R J : Type*} [CommRing R] [Fintype J] [DecidableEq J]
variable (I : Ideal R) (a : J → I)

omit [Fintype J] in
theorem productGenerator_factor {s t : Finset J} (hst : s ⊆ t) :
    productGenerator I a t = productGenerator I a s * productGenerator I a (t \ s) := by
  simp only [productGenerator_eq_prod]
  exact (Finset.prod_sdiff hst).symm.trans (mul_comm _ _)

omit [Fintype J] in
theorem coefficientProduct_factor {s t : Finset J} (hst : s ⊆ t) :
    coefficientProduct I a t = coefficientProduct I a s * coefficientProduct I a (t \ s) := by
  exact (Finset.prod_sdiff hst).symm.trans (mul_comm _ _)

def chartRestriction {s t : Finset J} (hst : s ⊆ t) : Chart I a s →+* Chart I a t :=
  HomogeneousLocalization.awayMap (piece I) (productGenerator_mem I a (t \ s))
    (productGenerator_factor I a hst)

theorem chartRestriction_base {s t : Finset J} (hst : s ⊆ t) (r : R) :
    chartRestriction I a hst (ReesProductChart.chartBase I a s r) =
      ReesProductChart.chartBase I a t r :=
  HomogeneousLocalization.awayMap_fromZeroRingHom _ _ _ _

omit [Fintype J] [DecidableEq J] in
theorem chartMap_mk_homogeneous (s : Finset J) {d : ℕ}
    (hgen : productGenerator I a s ∈ piece I d) (k : ℕ) (m : reesAlgebra I)
    (hm : m ∈ piece I (k • d)) :
    ReesProductChart.chartMap I a s (HomogeneousLocalization.Away.mk (piece I) hgen k m hm) =
      IsLocalization.mk' (Localization.Away (coefficientProduct I a s)) (evaluation I m)
        (powerDenominator (coefficientProduct I a s) k) := by
  simp only [ReesProductChart.chartMap, RingHom.comp_apply,
    HomogeneousLocalization.algebraMap_apply, HomogeneousLocalization.Away.val_mk,
    Localization.mk_eq_mk', IsLocalization.map_mk']
  congr 1
  apply Subtype.ext
  simp only [map_pow, evaluation_productGenerator, powerDenominator_val]

omit [Fintype J] in
theorem coefficientRestriction_fraction {s t : Finset J} (hst : s ⊆ t) (r : R) (k : ℕ) :
    coefficientRestriction I a hst
      (IsLocalization.mk' (Localization.Away (coefficientProduct I a s)) r
        (powerDenominator (coefficientProduct I a s) k)) =
      IsLocalization.mk' (Localization.Away (coefficientProduct I a t))
        (r * coefficientProduct I a (t \ s) ^ k)
        (powerDenominator (coefficientProduct I a t) k) := by
  have hu : IsUnit (algebraMap R (Localization.Away (coefficientProduct I a t))
      (coefficientProduct I a s)) :=
    IsLocalization.Away.isUnit_of_dvd (coefficientProduct I a t)
      ⟨coefficientProduct I a (t \ s), coefficientProduct_factor I a hst⟩
  apply (hu.pow k).mul_right_injective
  calc
    _ = algebraMap R (Localization.Away (coefficientProduct I a t)) r := by
      have h := congrArg (coefficientRestriction I a hst)
        (IsLocalization.mk'_spec' (Localization.Away (coefficientProduct I a s)) r
          (powerDenominator (coefficientProduct I a s) k))
      simpa only [map_mul, coefficientRestriction_algebraMap, powerDenominator_val, map_pow] using h
    _ = _ := by
      rw [← map_pow]
      dsimp only
      rw [IsLocalization.mul_mk'_eq_mk'_of_mul]
      symm
      apply IsLocalization.mk'_eq_iff_eq_mul.mpr
      rw [← map_mul]
      congr 1
      change coefficientProduct I a s ^ k * (r * coefficientProduct I a (t \ s) ^ k) =
        r * coefficientProduct I a t ^ k
      rw [coefficientProduct_factor I a hst, mul_pow]
      ring

theorem chartMap_restriction {s t : Finset J} (hst : s ⊆ t) (q : Chart I a s) :
    ReesProductChart.chartMap I a t (chartRestriction I a hst q) =
      coefficientRestriction I a hst (ReesProductChart.chartMap I a s q) := by
  obtain ⟨k, m, hm, rfl⟩ := HomogeneousLocalization.Away.mk_surjective (piece I)
    (productGenerator_mem I a s) q
  rw [chartRestriction, HomogeneousLocalization.awayMap_mk, chartMap_mk_homogeneous,
    ReesProductChart.chartMap_mk, coefficientRestriction_fraction,
    map_mul, (evaluation I).map_pow, evaluation_productGenerator]

theorem chartRestriction_power_mem {s t : Finset J} (hst : s ⊆ t) (n : ℕ)
    (q : ↥((I ^ n).map (ReesProductChart.chartBase I a s))) :
    chartRestriction I a hst q.val ∈ (I ^ n).map (ReesProductChart.chartBase I a t) := by
  have hmap : ((I ^ n).map (ReesProductChart.chartBase I a s)).map (chartRestriction I a hst) =
      (I ^ n).map (ReesProductChart.chartBase I a t) := by
    rw [Ideal.map_map]
    congr 1
    apply RingHom.ext
    intro r
    exact chartRestriction_base I a hst r
  rw [← hmap]
  exact Ideal.mem_map_of_mem _ q.property

def chartPowerRestriction {s t : Finset J} (hst : s ⊆ t) (n : ℕ) :
    ↥((I ^ n).map (ReesProductChart.chartBase I a s)) →+
      ↥((I ^ n).map (ReesProductChart.chartBase I a t)) where
  toFun q := ⟨chartRestriction I a hst q.val, chartRestriction_power_mem I a hst n q⟩
  map_zero' := Subtype.ext (map_zero _)
  map_add' _ _ := Subtype.ext (map_add _ _ _)

theorem chartPowerMap_restriction {s t : Finset J} {j k : J}
    (hj : j ∈ s) (hk : k ∈ t) (hst : s ⊆ t) (n : ℕ) (z : Piece I a s n) :
    letI := presentationAlgebra I a
    letI := gradedScalarAction I a
    chartPowerMap I a hk n (setRestriction (grading (J := J) (R := R)) (integerPiece I)
      MvPolynomial.X variable_mem hst n z) =
      chartPowerRestriction I a hst n (chartPowerMap I a hj n z) := by
  let := presentationAlgebra I a
  let := gradedScalarAction I a
  apply Subtype.ext
  apply ReesProductChart.chartMap_injective I a t
  change ReesProductChart.chartMap I a t _ =
    ReesProductChart.chartMap I a t (chartRestriction I a hst (chartPowerMap I a hj n z).val)
  rw [chartPowerMap_evaluation I a hk, chartMap_restriction, chartPowerMap_evaluation I a hj,
    pieceEvaluation_restriction]

end
end PiExponent.ReesProductRestriction

end OAI
