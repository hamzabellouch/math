import OAI.NumberTheory.DirichletL.Dictionary.InverseRawInitialGates
import OAI.NumberTheory.DirichletL.Inversion.InitialExcludedEnergy

namespace OAI

noncomputable section

open scoped Classical BigOperators SchwartzMap
namespace SevenEighths.DetectorDictionaryInverseRawInitialEnergy
open HeckeFamily HeckeDyadic HeckeInverseAmplification InverseInitialConjugateEnergy
open InverseInitialRawDictionary InverseInitialExcludedPolynomial InverseInitialExcludedEnergy
open DetectorDictionaryInverseRawInitialGates CanonicalQuadraticSieve ConcreteTraceCRT
open ActualEisensteinCubic IdealMobiusDivisorSum CanonicalRowCompletion CanonicalCoefficientClass
local notation "O"=>HeckeFamily.O

private theorem admissible_one : Admissible (1:Ideal O) := by
  refine ⟨one_ne_zero,squarefree_one,?_⟩
  simp only [UniqueFactorizationMonoid.normalizedFactors_one,Multiset.notMem_zero,false_implies,forall_const]

def initialFunction (data:RowData)(W:ℝ→ℂ)(H b Btree cap D sigma freq:ℝ)(j:Ideal O):O→ℂ:=
  originalTotalPolynomial
    (InitialMeanSquare.outsideSquarefreeIdeals (excluded data) (completeCutoff H b Btree cap))
    1 (idealCoeff (deletedBase data)).toMonoidHom (fun _=>1)
    (twistedProfile W sigma freq) H (Real.logb H (D/(j.absNorm:ℝ))) 0

theorem deleted_rows_le_initial
    (Φ:𝓢(ℝ,ℂ))(hΦ:∀x,0≤(Φ x).re)(hone:∀x∈Set.Icc (0:ℝ) 1,Φ x=1)
    (data:RowData)(W:ℝ→ℂ)(H D c b Btree cap sigma freq:ℝ)
    (hH:1<H)(hD:1≤D)(hc:0<c)(hcapacity:D^(1+c)≤H)(hb:0≤b)
    (hW:∀x,W x≠0→x≤b)
    (j:Ideal O)(hj:j∈idealDivisors (∏P∈excluded data,P))
    (rows:Finset NonzeroElement)(hrows:∀u∈rows,((Ideal.span {u.val}).absNorm:ℝ)≤H):
    (∑u∈rows,‖polynomial ((data.character u).excludePrimes (excluded data)
      (reflectionExcludedPrimes_prime (basePeriod data))) true W (D/(j.absNorm:ℝ)) sigma freq‖^2)
      ≤smoothedEnergy Φ H (initialFunction data W H b Btree cap D sigma freq j) := by
  let F:=InitialMeanSquare.outsideSquarefreeIdeals (excluded data) (completeCutoff H b Btree cap)
  let f:=initialFunction data W H b Btree cap D sigma freq j
  have hFa:∀I∈F,Admissible I:=InitialMeanSquare.outsideSquarefree_admissible _ _
    (reflectionExcludedPrimes_bad (basePeriod data))
  have hs:Summable (fun u:O=>radialWeight Φ H u*‖f u‖^2):=
    (original_smoothed_overlap_triangle F admissible_one
      (fun I hI _=>admissible_supported (hFa I hI))
      (idealCoeff (deletedBase data)).toMonoidHom (fun _=>1) (twistedProfile W sigma freq)
      (zero_lt_one.trans hH) (Real.logb H (D/(j.absNorm:ℝ))) 0 (fun _=>0)
      Φ (fun x _=>hΦ x) (zero_lt_one.trans hH)).1
  have he (u:NonzeroElement)(hu:u∈rows):
      ‖polynomial ((data.character u).excludePrimes (excluded data)
        (reflectionExcludedPrimes_prime (basePeriod data))) true W (D/(j.absNorm:ℝ)) sigma freq‖^2=
        radialWeight Φ H u.val*‖f u.val‖^2:=by
    have hn:‖eisEmbedding u.val‖^2/H∈Set.Icc (0:ℝ) 1:=by
      refine ⟨div_nonneg (sq_nonneg _) (zero_lt_one.trans hH).le,?_⟩
      apply (div_le_one (zero_lt_one.trans hH)).mpr
      rw [eisEmbedding_norm_sq_eq_absNorm_span]
      exact hrows u hu
    rw [(raw_complete_pool data H D c b Btree cap hH hD hc hcapacity hb W hW).2 j hj u sigma freq]
    change ‖f u.val‖^2=(Φ (‖eisEmbedding u.val‖^2/H)).re*‖f u.val‖^2
    rw [hone _ hn,Complex.one_re,one_mul]
  calc
    _=∑u∈rows,radialWeight Φ H u.val*‖f u.val‖^2:=Finset.sum_congr rfl he
    _=∑u∈rows.image Subtype.val,radialWeight Φ H u*‖f u‖^2:=by
      rw [Finset.sum_image (fun a _ b _ hab=>Subtype.val_injective hab)]
    _≤∑'u:O,radialWeight Φ H u*‖f u‖^2:=hs.sum_le_tsum _
      (fun u _=>mul_nonneg (hΦ _) (sq_nonneg _))
    _=_:=rfl

theorem raw_rows_le_initial
    (Φ:𝓢(ℝ,ℂ))(hΦ:∀x,0≤(Φ x).re)(hone:∀x∈Set.Icc (0:ℝ) 1,Φ x=1)
    (data:RowData)(W:ℝ→ℂ)(H D c b Btree cap sigma freq:ℝ)
    (hH:1<H)(hD:1≤D)(hc:0<c)(hcapacity:D^(1+c)≤H)(hb:0≤b)
    (hW:∀x,W x≠0→x≤b)
    (rows:Finset NonzeroElement)(hrows:∀u∈rows,((Ideal.span {u.val}).absNorm:ℝ)≤H):
    (∑u∈rows,‖polynomial (data.character u) true W D sigma freq‖^2)≤
      ((idealDivisors (∏P∈excluded data,P)).card:ℝ)*
        ∑j∈idealDivisors (∏P∈excluded data,P),
          smoothedEnergy Φ H (initialFunction data W H b Btree cap D sigma freq j) := by
  have hd:=marked_family rows data.character (excluded data)
    (reflectionExcludedPrimes_prime (basePeriod data)) W D sigma freq b
    (zero_lt_one.trans_le hD) hW (fun _=>1) (fun _=>1) (by intros;norm_num)
  simp only [mul_one,one_mul] at hd
  apply hd.trans
  apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
  apply Finset.sum_le_sum
  intro j hj
  exact deleted_rows_le_initial Φ hΦ hone data W H D c b Btree cap sigma freq
    hH hD hc hcapacity hb hW j hj rows hrows

end SevenEighths.DetectorDictionaryInverseRawInitialEnergy

end

end OAI
