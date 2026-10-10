import OAI.NumberTheory.DirichletL.Moments.ReflectedAnnuli
import OAI.NumberTheory.DirichletL.Moments.ReflectionDeletion

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap
namespace SevenEighths.CenteredMomentReflectedSeries
open HeckeFamily CenteredMomentSectorLocalization CenteredMomentReflectedAnnuli
open CenteredMomentComparisonReflection CenteredMomentReflectionDeletion
open EisensteinSchwartzPoisson
local notation "NI" => UnrestrictedIdealReindex.NonzeroIdeal

def dyadicIdealTerm (η : Character) (F : ℝ→ℂ) (Y : ℝ) (I : NI) (n : ℤ) : ℂ :=
  idealCoeff η I.val*(dyadicWeight n ((I.val.absNorm:ℝ)/Y):ℂ)*F ((I.val.absNorm:ℝ)/Y)

lemma dyadicIdealTerm_norm (η : Character) (F : ℝ→ℂ) (Y : ℝ) (I : NI) (n : ℤ) :
    ‖dyadicIdealTerm η F Y I n‖=
      dyadicWeight n ((I.val.absNorm:ℝ)/Y)*‖idealCoeff η I.val*F ((I.val.absNorm:ℝ)/Y)‖ := by
  unfold dyadicIdealTerm
  rw [norm_mul,norm_mul,Complex.norm_real,Real.norm_of_nonneg (dyadicWeight_bounds _ _).1,norm_mul]
  ring

lemma dyadic_ideal_absolute (η : Character) (F : ℝ→ℂ) (hF : DecayTwo F)
    (Y : ℝ) (hY : 0<Y) :
    Summable (fun p : NI×ℤ=>‖dyadicIdealTerm η F Y p.1 p.2‖) := by
  apply (summable_prod_of_nonneg (fun _=>norm_nonneg _)).mpr
  simp_rw [dyadicIdealTerm_norm]
  constructor
  · intro I
    exact (dyadicWeight_summable _).mul_right _
  · simp_rw [tsum_mul_right]
    have he (I : NI) : (∑'n : ℤ,dyadicWeight n ((I.val.absNorm:ℝ)/Y))=1 :=
      dyadicWeight_partition _ (div_pos (HeckeDyadic.norm_pos I) hY)
    simp_rw [he,one_mul]
    exact (plain_summable η F hF Y hY).norm

lemma dyadic_ideal_partition (η : Character) (F : ℝ→ℂ) (Y : ℝ) (hY : 0<Y) (I : NI) :
    (∑'n : ℤ,dyadicIdealTerm η F Y I n)=idealCoeff η I.val*F ((I.val.absNorm:ℝ)/Y) := by
  have he (n : ℤ) : dyadicIdealTerm η F Y I n=
      (dyadicWeight n ((I.val.absNorm:ℝ)/Y):ℂ)*(idealCoeff η I.val*F ((I.val.absNorm:ℝ)/Y)) := by
    unfold dyadicIdealTerm
    ring
  simp_rw [he]
  have hp : 0<(I.val.absNorm:ℝ)/Y := div_pos (HeckeDyadic.norm_pos I) hY
  rw [tsum_mul_right,←Complex.ofReal_tsum,dyadicWeight_partition _ hp]
  simp

theorem normalized_annular_series (η : Character) (F : ℝ→ℂ) (hF : DecayTwo F)
    (Y : ℝ) (hY : 0<Y) :
    Summable (fun n : ℤ=>(Real.sqrt (dyadicScale n):ℂ)*
      HeckeDyadic.polynomial η false (annularProfile F (dyadicScale n)) (dyadicScale n*Y) 0 0) ∧
    HeckeDyadic.polynomial η false F Y 0 0=
      ∑'n : ℤ,(Real.sqrt (dyadicScale n):ℂ)*
        HeckeDyadic.polynomial η false (annularProfile F (dyadicScale n)) (dyadicScale n*Y) 0 0 := by
  have habs := dyadic_ideal_absolute η F hF Y hY
  have hs := habs.of_norm
  have he (n : ℤ) : (Real.sqrt (dyadicScale n):ℂ)*
      HeckeDyadic.polynomial η false (annularProfile F (dyadicScale n)) (dyadicScale n*Y) 0 0=
      (Real.sqrt Y:ℂ)⁻¹*∑'I : NI,dyadicIdealTerm η F Y I n := by
    rw [←normalized_annular_term η F (dyadicScale n) Y (dyadicScale_pos n) hY,
      polynomial_plain _ _ _ hY]
    congr 1
    apply tsum_congr
    intro I
    simp only [dyadicIdealTerm,dyadicWeight]
    ring
  simp_rw [he]
  refine ⟨hs.prod_symm.prod.mul_left _,?_⟩
  rw [tsum_mul_left,polynomial_plain η F Y hY]
  congr 1
  rw [hs.tsum_comm]
  exact tsum_congr (fun I=>(dyadic_ideal_partition η F Y hY I).symm)

theorem actual_reflected_annular_series (η : Character) (W : 𝓢(ℝ,ℂ))
    (Y : ℝ) (hY : 0<Y) :
    Summable (fun n : ℤ=>(Real.sqrt (dyadicScale n):ℂ)*
      HeckeDyadic.polynomial η false (annularProfile (paperRadialFourier W) (dyadicScale n))
        (dyadicScale n*Y) 0 0) ∧
    HeckeDyadic.polynomial η false (paperRadialFourier W) Y 0 0=
      ∑'n : ℤ,(Real.sqrt (dyadicScale n):ℂ)*
        HeckeDyadic.polynomial η false (annularProfile (paperRadialFourier W) (dyadicScale n))
          (dyadicScale n*Y) 0 0 := by
  exact normalized_annular_series η _ (reflected_decayTwo W) Y hY

end SevenEighths.CenteredMomentReflectedSeries

end

end OAI
