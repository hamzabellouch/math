import OAI.NumberTheory.DirichletL.Moments.FirstAnnularMajorant
import OAI.NumberTheory.DirichletL.Moments.GaussNormalization

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap
namespace SevenEighths.CenteredMomentFirstAnnularEnergy
open HeckeFamily CanonicalQuadraticSieve CenteredMomentGaussEnergy
open CenteredMomentFirstAnnularMajorant CenteredMomentSectorLocalization
open CenteredMomentCanonicalFirst CenteredMomentSmoothedWindowEnergy
local notation "O"=>HeckeFamily.O

variable {α:Type*}

lemma dyadic_summable (S:Finset α)(a:α→O)(ha:∀i,Supported (Ideal.span {a i}))
    (c:α→ℂ)(j:ℤ):Summable (fun z:O=>dyadicWeight j (normValue z)*‖gaussPolynomial S a ha c z‖^2):=by
  have hs:=gaussEnergy_hasSum_re S a ha c CenteredMomentEnergyProfiles.annulusTemplate.profile
    (dyadicScale j) (dyadicScale_pos j)
  simpa only [CenteredMomentEnergyProfiles.annulusTemplate_apply,Complex.ofReal_re,
    dyadicWeight,normValue_eq_embedding,mul_comm] using hs.summable

lemma weighted_summable (S:Finset α)(a:α→O)(ha:∀i,Supported (Ideal.span {a i}))
    (c:α→ℂ)(H:ℝ)(hH:0<H):
    Summable (fun z:O=>‖gaussPolynomial S a ha c z‖^2*(profile (normValue z/H)).re):=by
  simpa only [normValue_eq_embedding] using (gaussEnergy_hasSum_re S a ha c profile H hH).summable

theorem energy_partition (S:Finset α)(a:α→O)(ha:∀i,Supported (Ideal.span {a i}))
    (c:α→ℂ)(H:ℝ)(hH:0<H):
    (gaussEnergy S a ha c profile H).re=
      ∑j∈bands H,∑'z:O,dyadicWeight j (normValue z)*
        (‖gaussPolynomial S a ha c z‖^2*(profile (normValue z/H)).re):=by
  have hs:=weighted_summable S a ha c H hH
  have hj (j:ℤ):Summable (fun z:O=>dyadicWeight j (normValue z)*
      (‖gaussPolynomial S a ha c z‖^2*(profile (normValue z/H)).re)):=by
    apply hs.of_nonneg_of_le
    · intro z
      exact mul_nonneg (dyadicWeight_bounds j _).1 (mul_nonneg (sq_nonneg _) (profile_nonneg _))
    · intro z
      exact mul_le_of_le_one_left (mul_nonneg (sq_nonneg _) (profile_nonneg _)) (dyadicWeight_bounds j _).2
  have he (z:O):‖gaussPolynomial S a ha c z‖^2*(profile (normValue z/H)).re=
      ∑j∈bands H,dyadicWeight j (normValue z)*
        (‖gaussPolynomial S a ha c z‖^2*(profile (normValue z/H)).re):=by
    rw [←Finset.sum_mul]
    calc
      _=‖gaussPolynomial S a ha c z‖^2*
          ((∑j∈bands H,dyadicWeight j (normValue z))*(profile (normValue z/H)).re):=by
        rw [←weighted_partition H (normValue z) hH]
      _=_:=by ring
  have hsum:=gaussEnergy_hasSum_re S a ha c profile H hH
  rw [←hsum.tsum_eq]
  simp_rw [←normValue_eq_embedding]
  calc
    _ = ∑'z:O, ∑j∈bands H,dyadicWeight j (normValue z)*
        (‖gaussPolynomial S a ha c z‖^2*(profile (normValue z/H)).re) :=
      tsum_congr he
    _ = _ := Summable.tsum_finsetSum (fun j _=>hj j)

theorem energy_le_dyadic (S:Finset α)(a:α→O)(ha:∀i,Supported (Ideal.span {a i}))
    (c:α→ℂ)(H:ℝ)(hH:0<H):
    (gaussEnergy S a ha c profile H).re≤
      ∑j∈bands H,∑'z:O,dyadicWeight j (normValue z)*‖gaussPolynomial S a ha c z‖^2:=by
  rw [energy_partition S a ha c H hH]
  apply Finset.sum_le_sum
  intro j hj
  have hs:=dyadic_summable S a ha c j
  have hdom (z:O):dyadicWeight j (normValue z)*
      (‖gaussPolynomial S a ha c z‖^2*(profile (normValue z/H)).re)≤
      dyadicWeight j (normValue z)*‖gaussPolynomial S a ha c z‖^2:=
    mul_le_mul_of_nonneg_left (mul_le_of_le_one_right (sq_nonneg _) (profile_le_one _))
      (dyadicWeight_bounds j _).1
  have hl:Summable (fun z:O=>dyadicWeight j (normValue z)*
      (‖gaussPolynomial S a ha c z‖^2*(profile (normValue z/H)).re)):=
    hs.of_nonneg_of_le (fun z=>mul_nonneg (dyadicWeight_bounds j _).1
      (mul_nonneg (sq_nonneg _) (profile_nonneg _))) hdom
  exact hl.tsum_le_tsum hdom hs

end SevenEighths.CenteredMomentFirstAnnularEnergy

end

end OAI
