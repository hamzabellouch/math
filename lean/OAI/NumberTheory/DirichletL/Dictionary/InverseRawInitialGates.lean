import OAI.NumberTheory.DirichletL.Dictionary.InverseRawGeometry
import OAI.NumberTheory.DirichletL.Dictionary.InverseRawRadial
import OAI.NumberTheory.DirichletL.Inversion.InitialExcludedElement
import OAI.NumberTheory.DirichletL.Inversion.InitialExcludedOverlap

namespace OAI

noncomputable section

open scoped Classical BigOperators SchwartzMap Topology
open Filter
namespace SevenEighths.DetectorDictionaryInverseRawInitialGates
open HeckeFamily HeckeDyadic HeckeInverseAmplification InverseInitialDetectorSource
open InverseInitialRawDictionary InverseInitialRayAttachment InverseInitialExcludedPeriod
open InverseInitialExcludedPool InverseInitialExcludedOverlap InverseInitialExcludedPolynomial
open CanonicalRowCompletion CanonicalCoefficientClass CanonicalQuadraticSieve ConcreteTraceCRT
open ConcretePrimeRowBridge UniqueFactorizationMonoid IdealMobiusDivisorSum
open DetectorDictionaryInverseRawGeometry
local notation "O"=>HeckeFamily.O

def basePeriod (data:RowData):ℕ:=(baseCharacter data).period

def excluded (data:RowData):Finset (Ideal O):=reflectionExcludedPrimes (basePeriod data)

def deletedBase (data:RowData):Character:=
  (baseCharacter data).excludePrimes (excluded data) (reflectionExcludedPrimes_prime (basePeriod data))

theorem basePeriod_ne_zero (data:RowData):basePeriod data≠0:=Nat.ne_of_gt (Character.period_pos _)

theorem basePeriod_le (data:RowData):Ideal.span {(basePeriod data:O)}≤(baseCharacter data).modulus:=
  Ideal.span_le.mpr (Set.singleton_subset_iff.mpr (Character.period_mem _))

theorem raw_base_gates (data:RowData):
    deletedPeriod (basePeriod data)≠0 ∧
    reflectionExcludedPrimes (deletedPeriod (basePeriod data))=excluded data ∧
    (∀x,‖elementCharacter (idealCoeff (deletedBase data)).toMonoidHom x‖≤1) ∧
    FactorsModulo (fixedBaseConductor (deletedPeriod (basePeriod data)))
      (elementCharacter (idealCoeff (deletedBase data)).toMonoidHom):=
  deleted_physical_base_gates (baseCharacter data) (basePeriod data)
    (basePeriod_ne_zero data) (basePeriod_le data)

theorem actual_row_fixed_base (data:RowData)(u:NonzeroElement)(I:Ideal O):
    idealCoeff (data.character u) I=idealCoeff (baseCharacter data) I*idealRowHom u.val I:=by
  rw [baseCharacter_coeff]
  exact fixedBase_row data.η (data.character u) data.m data.f u.val (data.character_spec u) I

theorem actual_deleted_row (data:RowData)(u:NonzeroElement)(I:Ideal O):
    idealCoeff ((data.character u).excludePrimes (excluded data)
      (reflectionExcludedPrimes_prime (basePeriod data))) I=
      idealCoeff (deletedBase data) I*idealRowHom u.val I:=by
  unfold deletedBase excluded
  rw [idealCoeff_excludePrimes,idealCoeff_excludePrimes,actual_row_fixed_base]
  split_ifs <;> simp

def completeCutoff (H b Btree cap:ℝ):ℕ:=⌈max (Btree*H^(cap+1)) (b*H)⌉₊

theorem completeCutoff_tree (H b Btree cap:ℝ):
    Btree*H^(cap+1)≤(completeCutoff H b Btree cap:ℝ):=
  (le_max_left _ _).trans (Nat.le_ceil _)

theorem completeCutoff_columns (H b Btree cap D n:ℝ)(hb:0≤b)(hD:0≤D)
    (hDH:D≤H)(hn:1≤n):b*(D/n)≤(completeCutoff H b Btree cap:ℝ):=by
  have hn0:0<n:=zero_lt_one.trans_le hn
  have hdn:D/n≤D:=(div_le_iff₀ hn0).mpr (le_mul_of_one_le_right hD hn)
  exact (mul_le_mul_of_nonneg_left (hdn.trans hDH) hb).trans
    ((le_max_right _ _).trans (Nat.le_ceil _))

theorem excluded_divisor_norm (data:RowData)(j:Ideal O)
    (hj:j∈idealDivisors (∏P∈excluded data,P)):
    1≤(j.absNorm:ℝ) ∧ (j.absNorm:ℝ)≤((∏P∈excluded data,P).absNorm:ℝ):=by
  have hP:Squarefree (∏P∈excluded data,P):=
    prime_product_squarefree _ (reflectionExcludedPrimes_prime (basePeriod data))
  have hd: j∣∏P∈excluded data,P:=(mem_idealDivisors hP.ne_zero).mp hj
  have hj0:=ne_zero_of_dvd_ne_zero hP.ne_zero hd
  constructor
  · exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr hj0)
  · exact_mod_cast Nat.le_of_dvd
      (Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hP.ne_zero)) (map_dvd Ideal.absNorm hd)

theorem shifted_raw_geometry_eventually (data:RowData)(c eta:ℝ)(hc:0<c)(heta:0<eta):
    ∀ᶠH:ℝ in atTop,1<H ∧ ∀D:ℝ,1≤D→D^(1+c)≤H→
      ∀j∈idealDivisors (∏P∈excluded data,P),
      let r:=Real.logb H (D/(j.absNorm:ℝ));
      -eta≤r ∧ r≤1-capacityGap c ∧ 2*r≤3-capacityGap c ∧
      H^r=D/(j.absNorm:ℝ) ∧ r+7*eta≤1+7*eta ∧ D≤H:=by
  have ht:∀ᶠH:ℝ in atTop,((∏P∈excluded data,P).absNorm:ℝ)≤H^eta:=
    (tendsto_rpow_atTop heta).eventually (eventually_ge_atTop _)
  filter_upwards [eventually_gt_atTop (1:ℝ),ht] with H hH ht
  refine ⟨hH,?_⟩
  intro D hD hcap j hj r
  obtain ⟨hn,hnB⟩:=excluded_divisor_norm data j hj
  have hH0:0<H:=zero_lt_one.trans hH
  have hD0:0<D:=zero_lt_one.trans_le hD
  have hn0:0<(j.absNorm:ℝ):=zero_lt_one.trans_le hn
  obtain ⟨hr0,hr1,hr2,hex⟩:=raw_log_capacity H D c hH hD hc hcap
  have hr:r=Real.logb H D-Real.logb H (j.absNorm:ℝ):=
    Real.logb_div hD0.ne' hn0.ne'
  have hnlog:0≤Real.logb H (j.absNorm:ℝ):=
    div_nonneg (Real.log_nonneg hn) (Real.log_pos hH).le
  have hneta:Real.logb H (j.absNorm:ℝ)≤eta:=by
    exact (Real.logb_le_iff_le_rpow hH hn0).mpr (hnB.trans ht)
  have hrlo:-eta≤r:=by rw [hr];linarith
  have hrup:r≤1-capacityGap c:=by rw [hr];linarith
  refine ⟨hrlo,hrup,by rw [hr];linarith,
    Real.rpow_logb hH0 hH.ne' (div_pos hD0 hn0),?_,?_⟩
  · linarith [(capacityGap_pos c hc).le]
  · calc
      D=H^(Real.logb H D):=hex.symm
      _≤H^1:=Real.rpow_le_rpow_of_exponent_le hH.le (by linarith [(capacityGap_pos c hc).le])
      _=H:=Real.rpow_one _

theorem deleted_row_complete_polynomial (data:RowData)(u:NonzeroElement)
    (W:ℝ→ℂ)(H r sigma freq b:ℝ)(hH:0<H)
    (hW:∀x,W x≠0→x≤b)(Dpool:ℕ)(hbudget:b*H^r≤(Dpool:ℝ)):
    polynomial ((data.character u).excludePrimes (excluded data)
      (reflectionExcludedPrimes_prime (basePeriod data))) true W (H^r) sigma freq=
      InverseInitialConjugateEnergy.originalTotalPolynomial
        (InitialMeanSquare.outsideSquarefreeIdeals (excluded data) Dpool) 1
        (idealCoeff (deletedBase data)).toMonoidHom (fun _=>1)
        (twistedProfile W sigma freq) H r 0 u.val:=by
  let χ:=(data.character u).excludePrimes (excluded data)
    (reflectionExcludedPrimes_prime (basePeriod data))
  let F:=InitialMeanSquare.outsideSquarefreeIdeals (excluded data) Dpool
  have hs:(∑'I:Ideal O,(moebius I:ℂ)*idealCoeff χ I*
      (W ((I.absNorm:ℝ)/H^r)*(((I.absNorm:ℝ)/H^r:ℝ):ℂ)^(-HeckeDyadic.shift sigma freq)))=
      ∑I∈F,(moebius I:ℂ)*idealCoeff χ I*
        (W ((I.absNorm:ℝ)/H^r)*(((I.absNorm:ℝ)/H^r:ℝ):ℂ)^(-HeckeDyadic.shift sigma freq)):=by
    apply tsum_eq_sum
    intro I hn
    by_cases hsq:Squarefree I
    · by_cases hout:outside (excluded data) I
      · by_cases hw:W ((I.absNorm:ℝ)/H^r)=0
        · simp only [hw,zero_mul,mul_zero]
        · have hN:(I.absNorm:ℝ)≤(Dpool:ℝ):=
            ((div_le_iff₀ (Real.rpow_pos_of_pos hH r)).mp (hW _ hw)).trans hbudget
          have hmem:I∈F:=by
            apply Finset.mem_filter.mpr
            refine ⟨mem_outsideIdealsUpTo.mpr ⟨?_,?_,hout⟩,hsq⟩
            · exact Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr hsq.ne_zero)
            · exact_mod_cast hN
          exact False.elim (hn hmem)
      · have hz:=deleted_zero_outside (data.character u) (excluded data)
          (reflectionExcludedPrimes_prime (basePeriod data)) I hout
        simp only [χ,hz,mul_zero,zero_mul]
    · simp only [moebius_of_not_squarefree hsq,Int.cast_zero,zero_mul]
  rw [polynomial_all_ideals,hs,normalization_eq H r hH]
  unfold InverseInitialConjugateEnergy.originalTotalPolynomial
  simp only [add_zero,map_one,mul_one]
  congr 1
  apply Finset.sum_congr rfl
  intro I hI
  rw [actual_deleted_row]
  simp only [twistedProfile,InverseInitialPoissonBridge.heckeIdealCharacter_apply]
  change (moebius I:ℂ) * (idealCoeff (deletedBase data) I * idealRowHom u.val I) *
      (W ((I.absNorm:ℝ)/H^r)*(((I.absNorm:ℝ)/H^r:ℝ):ℂ)^(-shift sigma freq)) =
    (moebius I:ℂ) * (idealCoeff (deletedBase data) I * idealRowHom u.val I) *
      (W ((I.absNorm:ℝ)/H^r)*(((I.absNorm:ℝ)/H^r:ℝ):ℂ)^(-shift sigma freq))
  ring

theorem raw_complete_pool (data:RowData)(H D c b Btree cap:ℝ)
    (hH:1<H)(hD:1≤D)(hc:0<c)(hcap:D^(1+c)≤H)(hb:0≤b)
    (W:ℝ→ℂ)(hW:∀x,W x≠0→x≤b):
    Btree*H^(cap+1)≤(completeCutoff H b Btree cap:ℝ) ∧
    ∀j∈idealDivisors (∏P∈excluded data,P),∀u:NonzeroElement,∀sigma freq:ℝ,
      polynomial ((data.character u).excludePrimes (excluded data)
        (reflectionExcludedPrimes_prime (basePeriod data))) true W
        (D/(j.absNorm:ℝ)) sigma freq=
      InverseInitialConjugateEnergy.originalTotalPolynomial
        (InitialMeanSquare.outsideSquarefreeIdeals (excluded data)
          (completeCutoff H b Btree cap)) 1
        (idealCoeff (deletedBase data)).toMonoidHom (fun _=>1)
        (twistedProfile W sigma freq) H (Real.logb H (D/(j.absNorm:ℝ))) 0 u.val:=by
  refine ⟨completeCutoff_tree _ _ _ _,?_⟩
  intro j hj u sigma freq
  have hn:= (excluded_divisor_norm data j hj).1
  have hH0:0<H:=zero_lt_one.trans hH
  have hD0:0<D:=zero_lt_one.trans_le hD
  have hn0:0<(j.absNorm:ℝ):=zero_lt_one.trans_le hn
  have hex:=Real.rpow_logb hH0 hH.ne' (div_pos hD0 hn0)
  obtain ⟨_,hr,_,heD⟩:=raw_log_capacity H D c hH hD hc hcap
  have hDH:D≤H:=by
    calc
      D=H^(Real.logb H D):=heD.symm
      _≤H^1:=Real.rpow_le_rpow_of_exponent_le hH.le
        (by linarith [(capacityGap_pos c hc).le])
      _=H:=Real.rpow_one _
  have hbudget:b*H^(Real.logb H (D/(j.absNorm:ℝ)))≤
      (completeCutoff H b Btree cap:ℝ):=by
    rw [hex]
    exact completeCutoff_columns H b Btree cap D _ hb hD0.le hDH hn
  simpa only [hex] using deleted_row_complete_polynomial data u W H
    (Real.logb H (D/(j.absNorm:ℝ))) sigma freq b hH0 hW _ hbudget

end SevenEighths.DetectorDictionaryInverseRawInitialGates

end

end OAI
