import OAI.NumberTheory.PiExponent.Ampleness.ReesGradedModule
import OAI.NumberTheory.PiExponent.LocalAlgebra.LocalizedAlgebraEvaluation

namespace OAI

namespace PiExponent.ReesLocalizedChart
noncomputable section
open PiExponentSeshadri.ReesGrading
open PiExponent.ReesGradedModule PiExponent.ReesPolynomialPresentation
open PiExponent.GradedPolynomialLaurent PiExponent.GradedLocalizationExact
attribute [local instance] MvPolynomial.weightedGradedAlgebra
variable {R J : Type*} [CommRing R] [Fintype J]
variable (I : Ideal R) (a : J → I) (j : J)

abbrev LocalizationModule :=
  letI := presentationAlgebra I a
  LocalizedModule (Submonoid.powers (MvPolynomial.X j : MvPolynomial J R)) (reesAlgebra I)

def localizationEvaluation : LocalizationModule I a j →+ Localization.Away (a j).val := by
  letI := presentationAlgebra I a
  exact LocalizedAlgebraEvaluation.evaluation (Submonoid.powers (MvPolynomial.X j))
    (Submonoid.powers (a j).val) (evaluation I) (by
      rintro ⟨_, k, rfl⟩
      refine ⟨k, ?_⟩
      change (a j).val ^ k = evaluation I (presentation I a (MvPolynomial.X j ^ k))
      simp only [map_pow, presentation_X, evaluation_generator])

omit [Fintype J] in
theorem localizationEvaluation_fraction (m : reesAlgebra I) (k : ℕ) :
    letI := presentationAlgebra I a
    localizationEvaluation I a j (fraction (MvPolynomial.X j : MvPolynomial J R) m k) =
      IsLocalization.mk' (Localization.Away (a j).val) (evaluation I m)
        (powerDenominator (a j).val k) := by
  let := presentationAlgebra I a
  unfold localizationEvaluation fraction
  rw [LocalizedAlgebraEvaluation.evaluation_mk]
  congr 1
  apply Subtype.ext
  change evaluation I (presentation I a (MvPolynomial.X j ^ k)) = (a j).val ^ k
  simp only [map_pow, presentation_X, evaluation_generator]

abbrev Piece (n : ℕ) :=
  letI := presentationAlgebra I a
  letI := gradedScalarAction I a
  degreePiece (grading (J := J) (R := R)) (integerPiece I)
    (MvPolynomial.X j) 1 (variable_mem j) (n : ℤ)

def pieceEvaluation (n : ℕ) : Piece I a j n →+ Localization.Away (a j).val := by
  letI := presentationAlgebra I a
  letI := gradedScalarAction I a
  exact (localizationEvaluation I a j).comp (Piece I a j n).subtype

theorem pieceEvaluation_injective (n : ℕ) : Function.Injective (pieceEvaluation I a j n) := by
  let := presentationAlgebra I a
  let := gradedScalarAction I a
  apply (injective_iff_map_eq_zero _).mpr
  intro z hz
  obtain ⟨k, m, hm, hrep⟩ := z.property
  have hm' : m ∈ piece I (n + k) := by
    change m ∈ integerPiece I (↑(n + k))
    simpa only [Nat.cast_add, mul_one] using hm
  have heval : evaluation I m = (m : Polynomial R).coeff (n + k) := evaluation_piece I ⟨m, hm'⟩
  change localizationEvaluation I a j z.val = 0 at hz
  rw [hrep, localizationEvaluation_fraction] at hz
  obtain ⟨⟨b, hb⟩, hbm⟩ := (IsLocalization.mk'_eq_zero_iff
    (M := Submonoid.powers (a j).val) (S := Localization.Away (a j).val) _ _).mp hz
  obtain ⟨l, rfl⟩ := hb
  apply Subtype.ext
  change z.val = 0
  rw [hrep, fraction_eq_zero]
  refine ⟨l, ?_⟩
  change presentation I a (MvPolynomial.X j ^ l) * m = 0
  rw [map_pow, presentation_X]
  apply Subtype.ext
  change (generator I (a j) : Polynomial R) ^ l * (m : Polynomial R) = 0
  rw [(mem_piece I (n + k) m).mp hm', generator_val,
    Polynomial.monomial_pow, Polynomial.monomial_mul_monomial]
  rw [heval] at hbm
  simp only [hbm, map_zero]

theorem pieceEvaluation_mem_chartPower (n : ℕ) (z : Piece I a j n) :
    ∃ s : ↥((I ^ n).map (chartBase I (a j))),
      chartMap I (a j) s.val = pieceEvaluation I a j n z := by
  let := presentationAlgebra I a
  let := gradedScalarAction I a
  obtain ⟨k, m, hm, hrep⟩ := z.property
  have hm' : m ∈ piece I (n + k) := by
    change m ∈ integerPiece I (↑(n + k))
    simpa only [Nat.cast_add, mul_one] using hm
  let q : chart I (a j) := HomogeneousLocalization.Away.mk (piece I)
    (generator_mem I (a j)) (n + k) m (by simpa using hm')
  have hmem : (chartBase I (a j) (a j).val) ^ n * q ∈
      (I ^ n).map (chartBase I (a j)) := by
    rw [ReesPushdown.chart_ordinaryPower_principal]
    exact Ideal.mul_mem_right q _ (Ideal.subset_span (by simp))
  refine ⟨⟨(chartBase I (a j) (a j).val) ^ n * q, hmem⟩, ?_⟩
  change chartMap I (a j) ((chartBase I (a j) (a j).val) ^ n * q) =
    localizationEvaluation I a j z.val
  have hmap : chartMap I (a j) ((chartBase I (a j) (a j).val) ^ n) =
      algebraMap R (Localization.Away (a j).val) ((a j).val ^ n) := by
    calc
      _ = (chartMap I (a j) (chartBase I (a j) (a j).val)) ^ n :=
        (chartMap I (a j)).map_pow _ n
      _ = _ := by rw [chartMap_base, map_pow]
  rw [hrep, localizationEvaluation_fraction, map_mul, hmap]
  change (algebraMap R (Localization.Away (a j).val) ((a j).val ^ n)) *
    chartMap I (a j) (HomogeneousLocalization.Away.mk (piece I)
      (generator_mem I (a j)) (n + k) m _) = _
  rw [chartMap_mk, IsLocalization.mul_mk'_eq_mk'_of_mul]
  apply IsLocalization.mk'_eq_of_eq
  change (a j).val ^ (n + k) * evaluation I m =
    (a j).val ^ k * ((a j).val ^ n * evaluation I m)
  rw [pow_add]
  ring

theorem chartPower_mem_pieceEvaluation (n : ℕ)
    (s : ↥((I ^ n).map (chartBase I (a j)))) :
    ∃ z : Piece I a j n, pieceEvaluation I a j n z = chartMap I (a j) s.val := by
  let := presentationAlgebra I a
  let := gradedScalarAction I a
  obtain ⟨k, b, hb, hs⟩ := ReesPushdown.chart_ordinaryPower_fraction I (a j) n s.val s.property
  let m := ReesPushdown.ordinaryPowerEquivPiece I (n + k) ⟨b, hb⟩
  have hm : m.val ∈ integerPiece I ((n : ℤ) + (k : ℤ) * 1) := by
    have hm0 : m.val ∈ integerPiece I (↑(n + k)) := m.property
    simpa only [Nat.cast_add, mul_one] using hm0
  let z : Piece I a j n := ⟨fraction (MvPolynomial.X j : MvPolynomial J R) m.val k,
    k, m.val, hm, rfl⟩
  refine ⟨z, ?_⟩
  change localizationEvaluation I a j (fraction (MvPolynomial.X j : MvPolynomial J R) m.val k) = _
  rw [localizationEvaluation_fraction, hs]
  have heval : evaluation I m.val = b := by
    rw [evaluation_piece I m]
    exact ReesPushdown.ordinaryPowerEquivPiece_apply_coeff I (n + k) ⟨b, hb⟩
  rw [heval]
  rfl

def chartPowerMap (n : ℕ) : Piece I a j n →+ ↥((I ^ n).map (chartBase I (a j))) where
  toFun z := (pieceEvaluation_mem_chartPower I a j n z).choose
  map_zero' := by
    apply Subtype.ext
    apply chartMap_injective I (a j)
    rw [(pieceEvaluation_mem_chartPower I a j n 0).choose_spec, map_zero]
    change 0 = chartMap I (a j) 0
    exact (map_zero _).symm
  map_add' z w := by
    apply Subtype.ext
    apply chartMap_injective I (a j)
    change chartMap I (a j) _ = chartMap I (a j) (_ + _)
    rw [(pieceEvaluation_mem_chartPower I a j n (z+w)).choose_spec, map_add, map_add,
      (pieceEvaluation_mem_chartPower I a j n z).choose_spec,
      (pieceEvaluation_mem_chartPower I a j n w).choose_spec]

theorem chartPowerMap_evaluation (n : ℕ) (z : Piece I a j n) :
    chartMap I (a j) (chartPowerMap I a j n z).val = pieceEvaluation I a j n z :=
  (pieceEvaluation_mem_chartPower I a j n z).choose_spec

def chartPowerEquiv (n : ℕ) : Piece I a j n ≃+ ↥((I ^ n).map (chartBase I (a j))) :=
  AddEquiv.ofBijective (chartPowerMap I a j n) ⟨by
    intro z w hzw
    apply pieceEvaluation_injective I a j n
    rw [← chartPowerMap_evaluation, ← chartPowerMap_evaluation, hzw], by
    intro s
    obtain ⟨z, hz⟩ := chartPower_mem_pieceEvaluation I a j n s
    refine ⟨z, ?_⟩
    apply Subtype.ext
    apply chartMap_injective I (a j)
    rw [chartPowerMap_evaluation, hz]⟩

end
end PiExponent.ReesLocalizedChart

end OAI
