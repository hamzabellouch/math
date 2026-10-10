import OAI.NumberTheory.DirichletL.Detector.PhysicalCRT
import OAI.NumberTheory.DirichletL.CubicSieve.Gauss
import OAI.NumberTheory.DirichletL.Detector.PairPhase

namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.ProbePhysical
open ActualEisensteinCubic CanonicalRowCompletion CanonicalQuadraticSieve
open CompletedGauss ConcreteTraceCRT CubicEisenstein GaussianShiftedPartition
open CenteredMomentCommonSupport CenteredMomentCorrelation CenteredMomentFourier CenteredMomentFirstPoisson
local notation "O" => ActualEisensteinCubic.O

lemma gaussTwo_eq_elementFourier (I : Ideal O) (hI : CubicSieve.Admissible I) :
    gaussTwo I hI.2 =
      elementFourier (primaryGenerator I) hI.2 (CubicSieve.cubicRow I) 1 /
        (‖eisEmbedding (primaryGenerator I)‖:ℂ) := by
  let := finite_quotient_span hI.2
  let : Fintype (Residue (primaryGenerator I)) := Fintype.ofFinite _
  rw [CubicSieve.gaussTwo_eq_gaussSum I hI]
  unfold gaussSum elementFourier
  rw [tsum_fintype]
  congr 1
  apply Finset.sum_congr rfl
  intro x hx
  have hc := CubicSieve.principalCubicCharacter_mk I hI (representative (primaryGenerator I) x)
  rw [representative_spec] at hc
  rw [hc]
  simp only [map_one, one_mul]
  rfl

lemma residueGauss_principalCubicCharacter (I : Ideal O) (hI : CubicSieve.Admissible I)
    [Fintype (Residue (primaryGenerator I))] :
    residueGauss (primaryGenerator I) hI.2 (CubicSieve.principalCubicCharacter I hI) 1 =
      elementFourier (primaryGenerator I) hI.2 (CubicSieve.cubicRow I) 1 := by
  simp only [residueGauss, elementFourier, tsum_fintype, map_one, one_mul]
  apply Finset.sum_congr rfl
  intro x hx
  have hc := CubicSieve.principalCubicCharacter_mk I hI (representative (primaryGenerator I) x)
  rw [representative_spec] at hc
  rw [hc]

theorem gaussTwo_coprime_product (I J : Ideal O)
    (hI : CubicSieve.Admissible I) (hJ : CubicSieve.Admissible J)
    (hIJ : CubicSieve.Admissible (I*J)) (hcop : IsCoprime I J) :
    gaussTwo (I*J) hIJ.2 =
      (CubicSieve.cubicRow I (primaryGenerator J) * CubicSieve.cubicRow J (primaryGenerator I)) *
      gaussTwo I hI.2 * gaussTwo J hJ.2 := by
  let a := primaryGenerator I
  let b := primaryGenerator J
  have hc : IsCoprime a b := by
    rw [← Ideal.isCoprime_span_singleton_iff]
    simpa only [a,b,(primaryGenerator_spec I hI.2).1,(primaryGenerator_spec J hJ.2).1] using hcop
  let := finite_quotient_span hI.2
  let := finite_quotient_span hJ.2
  let := finite_quotient_span (mul_ne_zero hI.2 hJ.2)
  let : Fintype (Residue a) := Fintype.ofFinite _
  let : Fintype (Residue b) := Fintype.ofFinite _
  let : Fintype (Residue (a*b)) := Fintype.ofFinite _
  have he := coprime_character_fourier a b hI.2 hJ.2 hc
    (CubicSieve.principalCubicCharacter I hI) (CubicSieve.principalCubicCharacter J hJ) 1
  simp only [map_one] at he
  have hfour : elementFourier (a*b) (mul_ne_zero hI.2 hJ.2)
      (CubicSieve.cubicRow (I*J)) 1 =
      (CubicSieve.cubicRow I b * CubicSieve.cubicRow J a) *
        elementFourier a hI.2 (CubicSieve.cubicRow I) 1 *
        elementFourier b hJ.2 (CubicSieve.cubicRow J) 1 := by
    unfold elementFourier
    rw [tsum_fintype, tsum_fintype, tsum_fintype]
    calc
      _ = _ := by
        apply Finset.sum_congr rfl
        intro x hx
        obtain ⟨m,rfl⟩ := Ideal.Quotient.mk_surjective x
        rw [CubicSieve.cubicRow_mul]
        have hi : CubicSieve.cubicRow I (representative (a*b) (Ideal.Quotient.mk _ m)) =
            CubicSieve.cubicRow I m := by
          rw [← CubicSieve.principalCubicCharacter_mk I hI, ← CubicSieve.principalCubicCharacter_mk I hI]
          congr 1
          apply Ideal.Quotient.eq.mpr
          have hx := Ideal.Quotient.eq.mp (representative_spec (a*b) (Ideal.Quotient.mk _ m))
          exact Ideal.mem_span_singleton.mpr ((dvd_mul_right a b).trans (Ideal.mem_span_singleton.mp hx))
        have hj : CubicSieve.cubicRow J (representative (a*b) (Ideal.Quotient.mk _ m)) =
            CubicSieve.cubicRow J m := by
          rw [← CubicSieve.principalCubicCharacter_mk J hJ, ← CubicSieve.principalCubicCharacter_mk J hJ]
          congr 1
          apply Ideal.Quotient.eq.mpr
          have hx := Ideal.Quotient.eq.mp (representative_spec (a*b) (Ideal.Quotient.mk _ m))
          exact Ideal.mem_span_singleton.mpr ((dvd_mul_left b a).trans (Ideal.mem_span_singleton.mp hx))
        rw [hi,hj]
        simp only [frequencyReduction_mk, map_one, one_mul]
        rw [CubicSieve.principalCubicCharacter_mk I hI m, CubicSieve.principalCubicCharacter_mk J hJ m]
      _ = _ := he
      _ = _ := by
        rw [CubicSieve.principalCubicCharacter_mk I hI b,
          CubicSieve.principalCubicCharacter_mk J hJ a,
          residueGauss_principalCubicCharacter I hI, residueGauss_principalCubicCharacter J hJ]
        simp only [elementFourier, tsum_fintype]
        rfl
  rw [gaussTwo_eq_elementFourier (I*J) hIJ, gaussTwo_eq_elementFourier I hI,
    gaussTwo_eq_elementFourier J hJ]
  have hgen : primaryGenerator (I*J)=a*b := primaryGenerator_mul I J
  rw [elementFourier_congr _ (a*b) hIJ.2 (mul_ne_zero hI.2 hJ.2) _ 1 hgen, hfour]
  rw [hgen, map_mul, norm_mul, Complex.ofReal_mul]
  ring

theorem gaussTwo_coprime_product_sextic (I J : Ideal O)
    (hI : CubicSieve.Admissible I) (hJ : CubicSieve.Admissible J)
    (hIJ : CubicSieve.Admissible (I*J)) (hcop : IsCoprime I J) :
    gaussTwo (I*J) hIJ.2 =
      ProbePhase.sexticPair (primaryGenerator I) (primaryGenerator J)^2 *
        gaussTwo I hI.2 * gaussTwo J hJ.2 := by
  rw [gaussTwo_coprime_product I J hI hJ hIJ hcop]
  simp only [CubicSieve.cubicRow, ← idealRowHom_square, ProbePhase.sexticPair,
    (primaryGenerator_spec I hI.2).1, (primaryGenerator_spec J hJ.2).1, mul_pow]

end SevenEighths.ProbePhysical
end

end OAI
