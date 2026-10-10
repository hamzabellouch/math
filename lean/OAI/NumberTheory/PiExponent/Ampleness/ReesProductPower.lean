import OAI.NumberTheory.PiExponent.Ampleness.ReesProductChart

namespace OAI

namespace PiExponent.ReesProductPower
noncomputable section
open PiExponentSeshadri.ReesGrading
open PiExponent.ReesGradedModule PiExponent.ReesPolynomialPresentation
open PiExponent.GradedPolynomialLaurent PiExponent.GradedLocalizationExact PiExponent.GradedCech
open PiExponent.ReesLocalizedIntersections PiExponent.ReesProductChart
attribute [local instance] MvPolynomial.weightedGradedAlgebra
variable {R J : Type*} [CommRing R] [Fintype J] [DecidableEq J]
variable (I : Ideal R) (a : J → I) {s : Finset J} {j : J} (hj : j ∈ s)
include hj

theorem pieceEvaluation_mem_chartPower (n : ℕ) (z : Piece I a s n) :
    ∃ q : ↥((I ^ n).map (ReesProductChart.chartBase I a s)),
      ReesProductChart.chartMap I a s q.val = pieceEvaluation I a s n z := by
  let := presentationAlgebra I a
  let := gradedScalarAction I a
  obtain ⟨k, m, hm, hrep⟩ := z.property
  have hm' : m ∈ piece I (n + k * s.card) := by
    change m ∈ integerPiece I (↑(n + k * s.card))
    simpa only [Nat.cast_add, Nat.cast_mul] using hm
  have hc : s.card = (s.erase j).card + 1 := (Finset.card_erase_add_one hj).symm
  have hdeg : (n + k * s.card) + n • (s.erase j).card = (n + k) • s.card := by
    rw [hc]
    simp only [nsmul_eq_mul, Nat.cast_id]
    ring
  have hnum : m * productGenerator I a (s.erase j) ^ n ∈ piece I ((n + k) • s.card) := by
    have h := SetLike.mul_mem_graded hm'
      (SetLike.pow_mem_graded n (productGenerator_mem I a (s.erase j)))
    simpa only [hdeg] using h
  let q : Chart I a s := HomogeneousLocalization.Away.mk (piece I)
    (productGenerator_mem I a s) (n + k) (m * productGenerator I a (s.erase j) ^ n) hnum
  have hmem : (ReesProductChart.chartBase I a s (a j).val) ^ n * q ∈
      (I ^ n).map (ReesProductChart.chartBase I a s) := by
    rw [chart_ordinaryPower_principal I a hj]
    exact Ideal.mul_mem_right q _ (Ideal.subset_span (by simp))
  refine ⟨⟨(ReesProductChart.chartBase I a s (a j).val) ^ n * q, hmem⟩, ?_⟩
  change ReesProductChart.chartMap I a s
    ((ReesProductChart.chartBase I a s (a j).val) ^ n * q) =
      localizationEvaluation I a s z.val
  have hmap : ReesProductChart.chartMap I a s
      ((ReesProductChart.chartBase I a s (a j).val) ^ n) =
      algebraMap R (Localization.Away (coefficientProduct I a s)) ((a j).val ^ n) := by
    calc
      _ = (ReesProductChart.chartMap I a s
        (ReesProductChart.chartBase I a s (a j).val)) ^ n :=
          (ReesProductChart.chartMap I a s).map_pow _ n
      _ = _ := by rw [ReesProductChart.chartMap_base, map_pow]
  rw [hrep, localizationEvaluation_fraction, map_mul, hmap]
  change algebraMap R (Localization.Away (coefficientProduct I a s)) ((a j).val ^ n) *
    ReesProductChart.chartMap I a s (HomogeneousLocalization.Away.mk (piece I)
      (productGenerator_mem I a s) (n + k) (m * productGenerator I a (s.erase j) ^ n) hnum) = _
  rw [ReesProductChart.chartMap_mk, map_mul, (evaluation I).map_pow, evaluation_productGenerator,
    IsLocalization.mul_mk'_eq_mk'_of_mul]
  apply IsLocalization.mk'_eq_of_eq
  change coefficientProduct I a s ^ (n + k) * evaluation I m =
    coefficientProduct I a s ^ k * ((a j).val ^ n *
      (evaluation I m * coefficientProduct I a (s.erase j) ^ n))
  rw [pow_add, coefficientProduct_eq_pivot I a hj, mul_pow]
  ring

theorem chartPower_mem_pieceEvaluation (n : ℕ)
    (q : ↥((I ^ n).map (ReesProductChart.chartBase I a s))) :
    ∃ z : Piece I a s n,
      pieceEvaluation I a s n z = ReesProductChart.chartMap I a s q.val := by
  let := presentationAlgebra I a
  let := gradedScalarAction I a
  have hq : q.val ∈ Ideal.span {(ReesProductChart.chartBase I a s (a j).val) ^ n} :=
    (congrArg (fun K : Ideal (Chart I a s) => q.val ∈ K)
      (chart_ordinaryPower_principal I a hj n)).mp q.property
  rw [Ideal.mem_span_singleton] at hq
  obtain ⟨r, hr⟩ := hq
  obtain ⟨k, p, hp, hrep⟩ := HomogeneousLocalization.Away.mk_surjective (piece I)
    (productGenerator_mem I a s) r
  let m : reesAlgebra I := generator I (a j) ^ n * p
  have hm' : m ∈ piece I (n + k * s.card) := by
    have h := SetLike.mul_mem_graded (SetLike.pow_mem_graded n (generator_mem I (a j))) hp
    simpa only [nsmul_eq_mul, mul_one, Nat.cast_id, m] using h
  have hm : m ∈ integerPiece I ((n : ℤ) + (k : ℤ) * (s.card : ℤ)) := by
    have h : m ∈ integerPiece I (↑(n + k * s.card)) := hm'
    simpa only [Nat.cast_add, Nat.cast_mul] using h
  let z : Piece I a s n := ⟨fraction
    (coverProduct (MvPolynomial.X : J → MvPolynomial J R) s) m k,
      k, m, hm, rfl⟩
  refine ⟨z, ?_⟩
  change localizationEvaluation I a s (fraction
    (coverProduct (MvPolynomial.X : J → MvPolynomial J R) s) m k) = _
  have hmap : ReesProductChart.chartMap I a s
      ((ReesProductChart.chartBase I a s (a j).val) ^ n) =
      algebraMap R (Localization.Away (coefficientProduct I a s)) ((a j).val ^ n) := by
    calc
      _ = (ReesProductChart.chartMap I a s
        (ReesProductChart.chartBase I a s (a j).val)) ^ n :=
          (ReesProductChart.chartMap I a s).map_pow _ n
      _ = _ := by rw [ReesProductChart.chartMap_base, map_pow]
  rw [localizationEvaluation_fraction, hr, (ReesProductChart.chartMap I a s).map_mul,
    hmap, ← hrep, ReesProductChart.chartMap_mk,
    IsLocalization.mul_mk'_eq_mk'_of_mul]
  congr 1
  change evaluation I (generator I (a j) ^ n * p) = (a j).val ^ n * evaluation I p
  rw [map_mul, map_pow, evaluation_generator]

def chartPowerMap (n : ℕ) : Piece I a s n →+
    ↥((I ^ n).map (ReesProductChart.chartBase I a s)) where
  toFun z := (pieceEvaluation_mem_chartPower I a hj n z).choose
  map_zero' := by
    apply Subtype.ext
    apply ReesProductChart.chartMap_injective I a s
    rw [(pieceEvaluation_mem_chartPower I a hj n 0).choose_spec, map_zero]
    change 0 = ReesProductChart.chartMap I a s 0
    exact (map_zero _).symm
  map_add' z w := by
    apply Subtype.ext
    apply ReesProductChart.chartMap_injective I a s
    change ReesProductChart.chartMap I a s _ = ReesProductChart.chartMap I a s (_ + _)
    rw [(pieceEvaluation_mem_chartPower I a hj n (z+w)).choose_spec, map_add, map_add,
      (pieceEvaluation_mem_chartPower I a hj n z).choose_spec,
      (pieceEvaluation_mem_chartPower I a hj n w).choose_spec]

theorem chartPowerMap_evaluation (n : ℕ) (z : Piece I a s n) :
    ReesProductChart.chartMap I a s (chartPowerMap I a hj n z).val = pieceEvaluation I a s n z :=
  (pieceEvaluation_mem_chartPower I a hj n z).choose_spec

def chartPowerEquiv (n : ℕ) : Piece I a s n ≃+
    ↥((I ^ n).map (ReesProductChart.chartBase I a s)) :=
  AddEquiv.ofBijective (chartPowerMap I a hj n) ⟨by
    intro z w hzw
    apply pieceEvaluation_injective I a s n
    rw [← chartPowerMap_evaluation I a hj n z, ← chartPowerMap_evaluation I a hj n w, hzw], by
    intro q
    obtain ⟨z, hz⟩ := chartPower_mem_pieceEvaluation I a hj n q
    refine ⟨z, ?_⟩
    apply Subtype.ext
    apply ReesProductChart.chartMap_injective I a s
    rw [chartPowerMap_evaluation I a hj n z, hz]⟩

end
end PiExponent.ReesProductPower

end OAI
