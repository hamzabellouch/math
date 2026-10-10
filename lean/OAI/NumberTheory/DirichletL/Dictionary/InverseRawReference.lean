import OAI.NumberTheory.DirichletL.Dictionary.InverseRawInputBound
import OAI.NumberTheory.DirichletL.Dictionary.InverseRawInitialEnergy
import OAI.NumberTheory.DirichletL.Dictionary.InverseRawInput
import OAI.NumberTheory.DirichletL.Dictionary.InverseRawRealRadial
import OAI.NumberTheory.DirichletL.Dictionary.InverseRawCompact

namespace OAI

noncomputable section

open scoped Classical BigOperators SchwartzMap Topology
open Filter
namespace SevenEighths.DetectorDictionaryInverseRawReference
open HeckeFamily HeckeDyadic HeckeInverseAmplification InverseMoment
open ActualEisensteinCubic ConcreteTraceCRT ConcretePrimeRowBridge
open CanonicalRowCompletion CanonicalCoefficientClass CanonicalQuadraticSieve
open InverseInitialRawDictionary InverseInitialConjugateEnergy InverseInitialExcludedPeriod
open InverseInitialRayAttachment InverseInitialProfileBounds
open DetectorDictionaryInverseRawInitialGates DetectorDictionaryInverseRawInitialEnergy
open DetectorDictionaryInverseRawInput DetectorDictionaryInverseRawInputBound
open DetectorDictionaryInverseRawConjugateGates DetectorDictionaryInverseRawRealRadial
open DetectorDictionaryInverseRawGeometry IdealMobiusDivisorSum
local notation "O"=>HeckeFamily.O

theorem raw_reference_large (W:𝓢(ℝ,ℂ))(a b c κ:ℝ)(ha:0<a)(hb:0<b)
    (hs:Function.support W⊆Set.Icc a b)(hc:0<c)(hκ:0<κ):
    ∃J:ℕ,∀data:RowData,∃C H₀:ℝ,0<C ∧ 1<H₀ ∧
      ∀(t H D:ℝ),H₀≤H→1≤D→D^(1+c)≤H→∀rows:Finset NonzeroElement,
      (∀u∈rows,((Ideal.span {u.val}).absNorm:ℝ)≤H)→
      (∑u∈rows,‖polynomial (data.character u) true (childLogTest W t) D 0 0‖^2)≤
        (C*(1+‖t‖)^(2*J))*H*(H*max 1 D)^κ := by
  obtain ⟨Φ,hΦcompact,hΦ,hreal,hone⟩:=exists_real_raw_radial_majorant
  obtain ⟨η,τ,π,eps,hη,hτ,hπ,heps,hηone,hηgap,hτgap,hcost⟩:=
    raw_fixed_reserves c (κ/2) hc (by positivity)
  let gap:=capacityGap c/4
  have hgap:0<gap:=by dsimp [gap];exact div_pos (capacityGap_pos c hc) (by norm_num)
  have hηsmall:η≤gap/50:=by dsimp [gap];nlinarith
  have hτsmall:τ≤gap/50:=by dsimp [gap];nlinarith
  let Wbar:=SecondPassIntegration.conjugateProfile W
  have hsbar:Function.support Wbar⊆Set.Icc a b:=by
    intro x hx
    exact hs (by simpa only [Wbar,Function.mem_support,SecondPassIntegration.conjugateProfile_apply,star_ne_zero] using hx)
  obtain ⟨J,Btree,hBtree,hinput⟩:=raw_input_bound Wbar a b ha hsbar Φ
    gap eps π η τ (κ/4) hgap heps hπ hη hηone hηsmall hτ hτsmall (by positivity)
  refine ⟨J,?_⟩
  intro data
  obtain ⟨hq,hqset,hn,hperiod⟩:=raw_conjugate_base_gates data
  obtain ⟨C,Hq,hC,hHq,hinput⟩:=hinput (deletedPeriod (basePeriod data)) hq
  obtain ⟨Hg,hg⟩:=eventually_atTop.mp (shifted_raw_geometry_eventually data c η hc hη)
  let T:=idealDivisors (∏P∈excluded data,P)
  let Ctotal:=((T.card:ℝ)+1)^2*C
  refine ⟨Ctotal,max Hq Hg,by dsimp [Ctotal];positivity,lt_max_of_lt_left hHq,?_⟩
  intro t H D hH hD hcapacity rows hrows
  have hHq':Hq≤H:=(le_max_left _ _).trans hH
  obtain ⟨hHp,hgeom⟩:=hg H ((le_max_right _ _).trans hH)
  have hHpos:0<H:=zero_lt_one.trans hHp
  have hWt:∀x,childLogTest W t x≠0→x≤b:=by
    intro x hx
    exact (hs ((mul_ne_zero_iff.mp hx).1)).2
  have hraw:=raw_rows_le_initial Φ hΦ hone data (childLogTest W t) H D c b Btree 2 0 0
    hHp hD hc hcapacity hb.le hWt rows hrows
  have hterm (j:Ideal O)(hj:j∈T):
      smoothedEnergy Φ H (initialFunction data (childLogTest W t) H b Btree 2 D 0 0 j)≤
        C*H^(1+15*η+π+eps+κ/4)*(1+‖t‖)^(2*J):=by
    obtain ⟨hrlo,hr₁,hr₂,hex,hrcap,hDH⟩:=hgeom D hD hcapacity j hj
    let r:=Real.logb H (D/(j.absNorm:ℝ))
    let Dpool:=completeCutoff H b Btree 2
    have hpool:Btree*H^3≤(Dpool:ℝ):=by
      convert completeCutoff_tree H b Btree 2 using 1 ; norm_num
    have hbcover:b*H^r≤(Dpool:ℝ):=by
      rw [hex]
      exact completeCutoff_columns H b Btree 2 D _ hb.le (zero_lt_one.trans_le hD).le hDH
        (excluded_divisor_norm data j hj).1
    have hbound:=hinput H hHq' Dpool hpool
      (elementCharacter (conjugateIdealCharacter (idealCoeff (deletedBase data)).toMonoidHom))
      hn hperiod r (-t) (by dsimp [r];linarith)
      (by dsimp [gap] at *;linarith [(capacityGap_pos c hc).le])
      (by dsimp [gap] at *;linarith [(capacityGap_pos c hc).le])
      (by have hh:=capacityGap_lt_one c hc;linarith)
    let F:=InitialMeanSquare.outsideSquarefreeIdeals (reflectionExcludedPrimes (deletedPeriod (basePeriod data))) Dpool
    let hF:=InitialMeanSquare.outsideSquarefree_admissible (reflectionExcludedPrimes (deletedPeriod (basePeriod data))) Dpool
      (reflectionExcludedPrimes_bad (deletedPeriod (basePeriod data)))
    let:∀i:primePool F,(Ideal.span {poolPrimary F i}).IsMaximal:=fun i=>by
      rw [poolPrimary_span F hF i];infer_instance
    have hf:initialFunction data (childLogTest W t) H b Btree 2 D 0 0 j=
        originalTotalPolynomial F 1 (idealCoeff (deletedBase data)).toMonoidHom
          (fun _=>1) (childLogTest W t) H r 0:=by
      unfold initialFunction
      dsimp only [F]
      rw [hqset]
      congr 1
      funext x
      simp [twistedProfile,HeckeDyadic.shift]
    rw [hf,smoothedEnergy_eq_complex_norm Φ hΦ hreal H hHpos]
    have he: (∑'u:O,Φ (‖eisEmbedding u‖^2/H)*
        (‖originalTotalPolynomial F 1 (idealCoeff (deletedBase data)).toMonoidHom
          (fun _=>1) (childLogTest W t) H r 0 u‖^2:ℝ))=
        (∑'u:O,Φ (‖eisEmbedding u‖^2/H)*
        (‖((H^(-r/2):ℝ):ℂ)*SecondPassArithmetic.inputConjugateRow
          (poolPrimary F) (poolPrimary_good F (InitialMeanSquare.outsideSquarefree_admissible
            (reflectionExcludedPrimes (deletedPeriod (basePeriod data))) Dpool
            (reflectionExcludedPrimes_bad (deletedPeriod (basePeriod data)))))
          Finset.univ (elementCharacter (conjugateIdealCharacter
            (idealCoeff (deletedBase data)).toMonoidHom)) 1 1 1
          (initialTest (poolPrimary F) (fun _=>1) (childLogTest Wbar (-t)) H r) u‖^2:ℝ)):=by
      apply tsum_congr
      intro u
      congr 2
      exact original_complete_child_norm (reflectionExcludedPrimes (deletedPeriod (basePeriod data)))
        (reflectionExcludedPrimes_prime (deletedPeriod (basePeriod data))) Dpool
        (reflectionExcludedPrimes_bad (deletedPeriod (basePeriod data))) _ W b H r t hHpos
        (fun x hx=>(hs hx).2) hbcover u
    rw [he]
    simpa only [norm_neg] using hbound
  apply hraw.trans
  calc
    _≤(T.card:ℝ)*∑j∈T,C*H^(1+15*η+π+eps+κ/4)*(1+‖t‖)^(2*J):=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum hterm) (Nat.cast_nonneg _)
    _=(T.card:ℝ)^2*C*H^(1+15*η+π+eps+κ/4)*(1+‖t‖)^(2*J):=by
      simp only [Finset.sum_const,nsmul_eq_mul];ring
    _≤Ctotal*H^(1+15*η+π+eps+κ/4)*(1+‖t‖)^(2*J):=by
      dsimp [Ctotal]
      gcongr
      nlinarith [Nat.cast_nonneg (α:=ℝ) T.card]
    _≤(Ctotal*(1+‖t‖)^(2*J))*H*(H*max 1 D)^κ:=by
      have he:15*η+π+eps+κ/4≤κ:=by linarith
      have hh:=raw_output_budget H D κ (15*η+π+eps+κ/4) hHp.le hκ.le he
      rw [show (1+15*η+π+eps+κ/4:ℝ)=1+(15*η+π+eps+κ/4) by ring]
      nlinarith [mul_le_mul_of_nonneg_left hh
        (show 0≤Ctotal*(1+‖t‖)^(2*J) by dsimp [Ctotal];positivity)]

theorem raw_reference_moment (W:𝓢(ℝ,ℂ))(a b c κ:ℝ)(ha:0<a)(hb:0<b)
    (hs:Function.support W⊆Set.Icc a b)(hc:0<c)(hκ:0<κ):
    ∃J:ℕ,∀data:RowData,∃C:ℝ,0<C ∧ ∀t:ℝ,
      RawMoment data (childLogTest W t) c κ (C*(1+‖t‖)^(2*J)) := by
  obtain ⟨J,hlarge⟩:=raw_reference_large W a b c κ ha hb hs hc hκ
  refine ⟨J,?_⟩
  intro data
  obtain ⟨C,H₀,hC,hH₀,hlarge⟩:=hlarge data
  obtain ⟨C₀,hC₀,hcomplete⟩:=DetectorDictionaryInverseRawCompact.rawMoment_of_large_rows_ge_one
    W a b ha hs H₀ hH₀.le
  refine ⟨C+C₀,add_pos hC hC₀,?_⟩
  exact hcomplete data c κ C J hc.le hκ.le hC.le hlarge

end SevenEighths.DetectorDictionaryInverseRawReference

end

end OAI
