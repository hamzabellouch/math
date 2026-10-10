import OAI.NumberTheory.DirichletL.Detector.SpectralCompensation

namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.ProbePhysical
open ActualEisensteinCubic ProbeEuler ProbeLocal
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O

lemma initialPrime_denominators (η : HeckeFamily.Character) (P : PrimeIdeal) (x w z : ℂ)
    (hx : 0<x.re) (hw : 0<w.re) (hz : 0<z.re) :
    let Q : ℝ := Ideal.absNorm P.val
    (1-coordV Q z≠0) ∧ (1-coordW Q 1 w≠0) ∧
      (1-coordD Q (HeckeFamily.idealCoeff η P.val) 1 x≠0) := by
  dsimp only
  have hQ : (1:ℝ)<Ideal.absNorm P.val := by
    have hh := SmoothMobiusCorrection.prime_norm_two_le P
    exact_mod_cast (by omega : 1<Ideal.absNorm P.val)
  have hQ0 : (0:ℝ)<Ideal.absNorm P.val := by linarith
  constructor
  · apply one_sub_ne_zero_of_norm_lt_one
    rw [coordV_norm _ hQ0]
    exact Real.rpow_lt_one_of_one_lt_of_neg hQ (by linarith)
  constructor
  · apply one_sub_ne_zero_of_norm_lt_one
    apply (coordW_norm_le _ hQ0 1 w (by simp)).trans_lt
    exact Real.rpow_lt_one_of_one_lt_of_neg hQ (by linarith)
  · apply one_sub_ne_zero_of_norm_lt_one
    apply (coordD_norm_le _ hQ0 _ 1 x (HeckeFamily.idealCoeff_norm_le_one η P.val) (by simp)).trans_lt
    exact Real.rpow_lt_one_of_one_lt_of_neg hQ (by linarith)

lemma idealClosedCorrection_eq_continued (η : HeckeFamily.Character) (P : PrimeIdeal) (x w z : ℂ) :
    let Q : ℝ := Ideal.absNorm P.val
    idealClosedCorrection η P x w z=continuedCorrection (coordV Q z) (coordW Q 1 w)
      (coordD Q (HeckeFamily.idealCoeff η P.val) 1 x) (idealMarkedClosed η P x w z) := rfl

lemma standardFactor_times_continued (V W D M : ℂ)
    (hV : 1-V≠0) (hW : 1-W≠0) (hD : 1-D≠0) :
    (1-D)/((1-V)*(1-W))*continuedCorrection V W D M=localFactor V W M := by
  unfold continuedCorrection localFactor
  field_simp
  ring

lemma idealHighLocalFactor_eq_raw (η : HeckeFamily.Character) (P : PrimeIdeal)
    (hs : CanonicalQuadraticSieve.Supported P.val) (x w z : ℂ)
    (hx : 3/2<x.re) (hw : 2<w.re) (hz : 1/6<z.re) :
    let Q : ℝ := Ideal.absNorm P.val
    idealHighLocalFactor η P.val x w z=
      localFactor (coordV Q z) (coordW Q 1 w) (idealMarkedClosed η P x w z) := by
  have hd := initialPrime_denominators η P x w z (by linarith) (by linarith) (by linarith)
  have he := idealHighLocalFactor_rational η P hs x w z hx hw hz
  have hc := standardFactor_times_continued (coordV (Ideal.absNorm P.val) z)
    (coordW (Ideal.absNorm P.val) 1 w) (coordD (Ideal.absNorm P.val) (HeckeFamily.idealCoeff η P.val) 1 x)
    (idealMarkedClosed η P x w z) hd.1 hd.2.1 hd.2.2
  rw [←idealClosedCorrection_eq_continued] at hc
  dsimp only at he hc ⊢
  rw [he]
  simpa only [coordV,coordW,coordD,star_one,mul_one,one_mul] using hc

theorem idealCompensatedRatio_eq_continued (S : Finset Id) (hS : SourceExclusions S)
    (η : HeckeFamily.Character) (P : PrimeIdeal) (hP : P.val∉S) (x w z B q : ℂ)
    (hx : 3/2<x.re) (hw : 2<w.re) (hz : 1/6<z.re) :
    let Q : ℝ := Ideal.absNorm P.val
    B*idealMarkedLocalFactor η P x w z/idealHighLocalFactor η P.val x w z-q=
      compensatedReplacement (coordV Q z) (coordW Q 1 w)
        (coordD Q (HeckeFamily.idealCoeff η P.val) 1 x) (idealMarkedClosed η P x w z) B q /
          idealClosedCorrection η P x w z := by
  have hs := outside_prime_supported S hS.bad P hP
  have hd := initialPrime_denominators η P x w z (by linarith) (by linarith) (by linarith)
  have hraw := idealHighLocalFactor_eq_raw η P hs x w z hx hw hz
  have hn := source_idealHighLocalFactor_ne_zero S hS η P hP x w z hx hw hz
  rw [hraw] at hn
  have hH : idealClosedCorrection η P x w z≠0 :=
    factor_ne_zero_of_defect _ ((idealClosedCorrection_bound η P (hS.tail.norm_four P hP)
      x w z (by linarith) (by linarith) (by linarith)).trans (hS.tail.half ⟨P,hP⟩))
  have he := compensatedReplacement_eq_raw (coordV (Ideal.absNorm P.val) z)
    (coordW (Ideal.absNorm P.val) 1 w) (coordD (Ideal.absNorm P.val) (HeckeFamily.idealCoeff η P.val) 1 x)
    (idealMarkedClosed η P x w z) B q hd.1 hd.2.1 hd.2.2 hn
  rw [←continuedCorrection_eq_raw _ _ _ _ hd.1 hd.2.1 hd.2.2,
    ←idealClosedCorrection_eq_continued] at he
  dsimp only at hraw he ⊢
  rw [idealMarkedLocalFactor_rational η P hs x w z hx hz,hraw,he]
  exact (mul_div_cancel_left₀ _ hH).symm

theorem spectralCompensatedHigh_continued (S : Finset Id) (hS : SourceExclusions S)
    (T : Finset PrimeIdeal) (hT : ∀P∈T,P.val∉S) (η : HeckeFamily.Character)
    (x w z : ℂ) (B q : PrimeIdeal→ℂ)
    (hx : 3/2<x.re) (hw : 2<w.re) (hz : 1/6<z.re) :
    spectralCompensatedHigh S T η x w z B q=
      (HeckeFamily.LFunction (fixedSourcePrincipal S hS.prime) (6*z) *
       HeckeFamily.LFunction (fixedSourcePrincipal S hS.prime) w /
       HeckeFamily.LFunction (η.excludePrimes S hS.prime) x * globalClosedCorrection η S x w z) *
        ∏P∈T,(compensatedReplacement (coordV (Ideal.absNorm P.val) z)
          (coordW (Ideal.absNorm P.val) 1 w)
          (coordD (Ideal.absNorm P.val) (HeckeFamily.idealCoeff η P.val) 1 x)
          (idealMarkedClosed η P x w z) (B P) (q P) / idealClosedCorrection η P x w z) := by
  rw [spectralCompensatedHigh_L_factorization S hS T hT η x w z B q hx hw hz]
  congr 1
  apply Finset.prod_congr rfl
  intro P hP
  exact idealCompensatedRatio_eq_continued S hS η P (hT P hP) x w z (B P) (q P) hx hw hz

end SevenEighths.ProbePhysical
end

end OAI
