import OAI.NumberTheory.PiExponent.Ampleness.ReesLocalizedIntersections

namespace OAI

namespace PiExponent.ReesProductChart
noncomputable section
open PiExponentSeshadri.ReesGrading
open PiExponent.ReesGradedModule PiExponent.ReesPolynomialPresentation
open PiExponent.GradedPolynomialLaurent PiExponent.GradedLocalizationExact PiExponent.GradedCech
open PiExponent.ReesLocalizedIntersections
attribute [local instance] MvPolynomial.weightedGradedAlgebra
variable {R J : Type*} [CommRing R] [Fintype J] [DecidableEq J]
variable (I : Ideal R) (a : J → I)

def productGenerator (s : Finset J) : reesAlgebra I :=
  presentation I a (coverProduct MvPolynomial.X s)

theorem productGenerator_mem (s : Finset J) : productGenerator I a s ∈ piece I s.card :=
  presentation_integer_mem I a
    (coverProduct_mem (grading (J := J) (R := R)) MvPolynomial.X variable_mem s)

omit [Fintype J] [DecidableEq J] in
theorem evaluation_productGenerator (s : Finset J) :
    evaluation I (productGenerator I a s) = coefficientProduct I a s :=
  evaluation_presentation_product I a s

omit [Fintype J] [DecidableEq J] in
theorem productGenerator_eq_prod (s : Finset J) :
    productGenerator I a s = ∏ j ∈ s, generator I (a j) := by
  simp only [productGenerator, coverProduct, map_prod, presentation_X]

abbrev Chart (s : Finset J) := HomogeneousLocalization.Away (piece I) (productGenerator I a s)

def chartMap (s : Finset J) : Chart I a s →+* Localization.Away (coefficientProduct I a s) :=
  (IsLocalization.map (M := Submonoid.powers (productGenerator I a s))
    (S := Localization.Away (productGenerator I a s))
    (T := Submonoid.powers (coefficientProduct I a s))
    (Localization.Away (coefficientProduct I a s)) (evaluation I)
    (by rintro _ ⟨k, rfl⟩; exact ⟨k, by simp only [map_pow, evaluation_productGenerator]⟩)).comp
      (algebraMap (Chart I a s) (Localization.Away (productGenerator I a s)))

theorem chartMap_mk (s : Finset J) (k : ℕ) (m : reesAlgebra I)
    (hm : m ∈ piece I (k • s.card)) :
    chartMap I a s (HomogeneousLocalization.Away.mk (piece I)
      (productGenerator_mem I a s) k m hm) =
      IsLocalization.mk' (Localization.Away (coefficientProduct I a s)) (evaluation I m)
        (powerDenominator (coefficientProduct I a s) k) := by
  simp only [chartMap, RingHom.comp_apply, HomogeneousLocalization.algebraMap_apply,
    HomogeneousLocalization.Away.val_mk, Localization.mk_eq_mk', IsLocalization.map_mk']
  congr 1
  apply Subtype.ext
  simp only [map_pow, evaluation_productGenerator, powerDenominator_val]

theorem chartMap_injective (s : Finset J) : Function.Injective (chartMap I a s) := by
  apply (RingHom.injective_iff_ker_eq_bot _).mpr
  apply bot_unique
  intro z hz
  change z = 0
  obtain ⟨k, m, hm, rfl⟩ := HomogeneousLocalization.Away.mk_surjective (piece I)
    (productGenerator_mem I a s) z
  have hzero := RingHom.mem_ker.mp hz
  rw [chartMap_mk] at hzero
  obtain ⟨⟨b, hb⟩, hbm⟩ := (IsLocalization.mk'_eq_zero_iff
    (M := Submonoid.powers (coefficientProduct I a s))
    (S := Localization.Away (coefficientProduct I a s)) _ _).mp hzero
  obtain ⟨l, rfl⟩ := hb
  apply HomogeneousLocalization.val_injective
  rw [HomogeneousLocalization.val_zero, HomogeneousLocalization.Away.val_mk,
    Localization.mk_eq_mk', IsLocalization.mk'_eq_zero_iff]
  refine ⟨⟨productGenerator I a s ^ l, ⟨l, rfl⟩⟩, ?_⟩
  apply Subtype.ext
  have he : evaluation I m = (m : Polynomial R).coeff (k • s.card) := evaluation_piece I ⟨m, hm⟩
  have hep : evaluation I (productGenerator I a s) =
      (productGenerator I a s : Polynomial R).coeff s.card :=
    evaluation_piece I ⟨_, productGenerator_mem I a s⟩
  change (productGenerator I a s : Polynomial R) ^ l * (m : Polynomial R) = 0
  rw [(mem_piece I (k • s.card) m).mp hm,
    (mem_piece I s.card _).mp (productGenerator_mem I a s),
    Polynomial.monomial_pow, Polynomial.monomial_mul_monomial,
    ← hep, evaluation_productGenerator]
  rw [he] at hbm
  simp only [hbm, map_zero]

def chartBase (s : Finset J) : R →+* Chart I a s :=
  (HomogeneousLocalization.fromZeroRingHom (piece I)
    (Submonoid.powers (productGenerator I a s))).comp (zeroEquiv I).toRingHom

theorem chartMap_base (s : Finset J) (r : R) :
    chartMap I a s (chartBase I a s r) =
      algebraMap R (Localization.Away (coefficientProduct I a s)) r := by
  have h0 : algebraMap R (reesAlgebra I) r ∈ piece I (0 • s.card) := by
    simp [mem_piece]
  refine (chartMap_mk I a s 0 (algebraMap R (reesAlgebra I) r) h0).trans ?_
  have he : evaluation I (algebraMap R (reesAlgebra I) r) = r := by simp [evaluation]
  rw [he, powerDenominator_zero, IsLocalization.mk'_one]

variable {s : Finset J} {j : J} (hj : j ∈ s)
include hj

omit [Fintype J] in
theorem coefficientProduct_eq_pivot :
    coefficientProduct I a s = (a j).val * coefficientProduct I a (s.erase j) := by
  exact (Finset.mul_prod_erase s (fun i => (a i).val) hj).symm

def ratio (b : I) : Chart I a s :=
  HomogeneousLocalization.Away.mk (piece I) (productGenerator_mem I a s) 1
    (generator I b * productGenerator I a (s.erase j)) (by
      have h := SetLike.mul_mem_graded (generator_mem I b)
        (productGenerator_mem I a (s.erase j))
      simpa only [one_nsmul, Nat.add_comm 1, Finset.card_erase_add_one hj] using h)

theorem chartMap_ratio (b : I) :
    chartMap I a s (ratio I a hj b) =
      IsLocalization.mk' (Localization.Away (coefficientProduct I a s))
        (b.val * coefficientProduct I a (s.erase j))
        (powerDenominator (coefficientProduct I a s) 1) := by
  rw [ratio, chartMap_mk, map_mul, evaluation_generator, evaluation_productGenerator]

theorem base_mul_ratio (b : I) :
    chartBase I a s (a j).val * ratio I a hj b = chartBase I a s b.val := by
  apply chartMap_injective I a s
  rw [map_mul, chartMap_base, chartMap_ratio, chartMap_base,
    IsLocalization.mul_mk'_eq_mk'_of_mul]
  apply IsLocalization.mk'_eq_iff_eq_mul.mpr
  rw [← map_mul]
  congr 1
  change (a j).val * (b.val * coefficientProduct I a (s.erase j)) =
    b.val * coefficientProduct I a s ^ 1
  rw [pow_one, coefficientProduct_eq_pivot I a hj]
  ring

theorem map_ideal_principal :
    I.map (chartBase I a s) = Ideal.span {chartBase I a s (a j).val} := by
  apply le_antisymm
  · rw [Ideal.map_le_iff_le_comap]
    intro b hb
    change chartBase I a s b ∈ Ideal.span {chartBase I a s (a j).val}
    rw [Ideal.mem_span_singleton]
    exact ⟨ratio I a hj ⟨b, hb⟩, (base_mul_ratio I a hj ⟨b, hb⟩).symm⟩
  · rw [Ideal.span_singleton_le_iff_mem]
    exact Ideal.mem_map_of_mem _ (a j).property

theorem chart_ordinaryPower_principal (n : ℕ) :
    (I ^ n).map (chartBase I a s) = Ideal.span {(chartBase I a s (a j).val) ^ n} := by
  rw [Ideal.map_pow, map_ideal_principal I a hj, Ideal.span_singleton_pow]

theorem chart_generator_regular : IsRegular (chartBase I a s (a j).val) := by
  have hu : IsUnit (chartMap I a s (chartBase I a s (a j).val)) := by
    rw [chartMap_base]
    exact IsLocalization.Away.isUnit_of_dvd (coefficientProduct I a s)
      ⟨coefficientProduct I a (s.erase j), coefficientProduct_eq_pivot I a hj⟩
  constructor
  · intro x y h
    apply chartMap_injective I a s
    apply hu.isRegular.left
    simpa only [map_mul] using congrArg (chartMap I a s) h
  · intro x y h
    apply chartMap_injective I a s
    apply hu.isRegular.right
    simpa only [map_mul] using congrArg (chartMap I a s) h

end
end PiExponent.ReesProductChart

end OAI
