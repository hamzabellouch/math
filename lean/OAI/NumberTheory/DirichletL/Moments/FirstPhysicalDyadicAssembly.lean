import OAI.NumberTheory.DirichletL.Moments.FirstPhysicalSource
import OAI.NumberTheory.DirichletL.Moments.SecondDyadicPartition
import OAI.NumberTheory.DirichletL.Moments.SecondRetainedRows
import OAI.NumberTheory.DirichletL.Moments.OriginalCommonHarmonic

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace SevenEighths.CenteredMomentFirstPhysicalDyadicAssembly
open ActualEisensteinCubic ConcreteTraceCRT ConcretePrimeRowBridge
open HeckeFamily CanonicalQuadraticSieve CanonicalRowCompletion
open CenteredMomentFirstPhysicalSource CenteredMomentCanonicalFirst
open CenteredMomentFirstReduced CenteredMomentFirstColumns CenteredMomentCommonSupport
open CenteredMomentSupportedCorrelation CenteredMomentRowNorm
open CenteredMomentFirstWholeKernel CenteredMomentLogDyadic CenteredMomentSectorLocalization
open CenteredMomentDyadicCount CenteredMomentPrimitive
local notation "O"=>ActualEisensteinCubic.O

def retainedBlock (η:Character)(m A:O)(t:ℝ)(S:Finset (Ideal O))(c:Ideal O→ℂ)
    (C D:Ideal O)(hC:Supported C)(hD:Supported D)(E:Finset (CommonIndex C D))
    (rows:Finset O)(W:𝓢(ℝ,ℂ))(K R:ℝ):ℂ:=
  let e:=primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E
  let k:=K/‖eisEmbedding e‖^2
  let r:=activeConductor C D
  inactiveWeight C D E * ∑h∈rows,
    ∑a:columns C C hC.1 S,∑b:columns C D hD.1 S,
      let na:=element C C hC.1 S a
      let nb:=element C D hD.1 S b
      if IsCoprime (a:Ideal O) (b:Ideal O) then
        (tripleRow na nb r (supportedModulusCharacter na (element_supported C C hC.1 S a))
          (supportedModulusCharacter nb (element_supported C D hD.1 S b))⁻¹ (activeFunction C D hC) e *
        ((k/‖eisEmbedding (na*(nb*r))‖^2:ℝ):ℂ)*
        tripleFourier na nb r
          (supported_element_ne_zero _ (element_supported C C hC.1 S a))
          (supported_element_ne_zero _ (element_supported C D hD.1 S b))
          (finitePrimeModulus_ne_zero _) (supportedModulusCharacter na (element_supported C C hC.1 S a))
          (supportedModulusCharacter nb (element_supported C D hD.1 S b))⁻¹ (activeFunction C D hC) h)*
        (coefficient η m A t c C a*star (coefficient η m A t c D b))*
        (retainedWeight R (‖eisEmbedding h‖^2):ℂ)*
        EisensteinSchwartzPoisson.paperRadialFourier W (k*‖eisEmbedding h‖^2/‖eisEmbedding (na*(nb*r))‖^2)
      else 0

def retainedIndices (R:ℝ):Finset ℤ := (finite_retained_integral_dyads R).toFinset

lemma mem_retainedIndices (R:ℝ)(n:ℤ):
    n∈retainedIndices R↔Retained R n ∧ ∃q:ℝ,1≤q ∧ dyadicWeight n q≠0 :=
  (finite_retained_integral_dyads R).mem_toFinset

lemma retained_partition (R q:ℝ)(hq:1≤q):
    (∑n∈retainedIndices R,dyadicWeight n q)=retainedWeight R q :=by
  unfold retainedWeight
  rw [tsum_eq_sum (s:=retainedIndices R) (fun n hn=>by
    split_ifs with hr
    · by_contra hh
      exact hn ((mem_retainedIndices R n).mpr ⟨hr,q,hq,hh⟩)
    · rfl)]
  apply Finset.sum_congr rfl
  intro n hn
  rw [ite_eq_left ((mem_retainedIndices R n).mp hn).1]

def bands (K R A B:ℝ):Fin 4→Finset ℤ :=
  ![indices K K,retainedIndices R,indices 1 A,indices 1 B]

abbrev Blocks (K R A B:ℝ):=∀i:Fin 4,↥(bands K R A B i)

lemma product_partition (K R A B h a b:ℝ)(hK:0<K)(hh:1≤h)
    (ha:a∈Set.Icc (1:ℝ) A)(hb:b∈Set.Icc (1:ℝ) B):
    (∑n:Blocks K R A B,∏i:Fin 4,dyadicWeight (n i) (![K,h,a,b] i))=
      retainedWeight R h :=by
  have he (i:Fin 4):
      (∑n:bands K R A B i,dyadicWeight n (![K,h,a,b] i))=
        (if i=1 then retainedWeight R h else 1):=by
    fin_cases i
    · change (∑n:indices K K,dyadicWeight n K)=1
      rw [Finset.sum_coe_sort (indices K K) (fun n:ℤ=>dyadicWeight n K)]
      exact dyadic_partition_on_interval K K K hK ⟨le_rfl,le_rfl⟩
    · change (∑n:retainedIndices R,dyadicWeight n h)=retainedWeight R h
      rw [Finset.sum_coe_sort (retainedIndices R) (fun n:ℤ=>dyadicWeight n h)]
      exact retained_partition R h hh
    · change (∑n:indices 1 A,dyadicWeight n a)=1
      rw [Finset.sum_coe_sort (indices 1 A) (fun n:ℤ=>dyadicWeight n a)]
      exact dyadic_partition_on_interval 1 A a (by norm_num) ha
    · change (∑n:indices 1 B,dyadicWeight n b)=1
      rw [Finset.sum_coe_sort (indices 1 B) (fun n:ℤ=>dyadicWeight n b)]
      exact dyadic_partition_on_interval 1 B b (by norm_num) hb
  rw [←Fintype.prod_sum (fun (i:Fin 4)(n:bands K R A B i)=>
    dyadicWeight n (![K,h,a,b] i))]
  simp_rw [he]
  norm_num [Fin.prod_univ_four]

lemma windows_partition (K R A B h a b:ℝ)(hK:0<K)(hh:1≤h)
    (ha:a∈Set.Icc (1:ℝ) A)(hb:b∈Set.Icc (1:ℝ) B):
    (∑n:Blocks K R A B, windows (fun _=>logAnnulus) K h a b
      (dyadicScale (n 0)) (dyadicScale (n 1)) (dyadicScale (n 2)) (dyadicScale (n 3)))=
      (retainedWeight R h:ℂ):=by
  calc
    _ = ∑n:Blocks K R A B,((∏i:Fin 4,dyadicWeight (n i) (![K,h,a,b] i):ℝ):ℂ):=by
      apply Finset.sum_congr rfl
      intro n hn
      simpa [Fin.prod_univ_four] using
        (actual_product_windows K h a b hK (zero_lt_one.trans_le hh)
          (zero_lt_one.trans_le ha.1) (zero_lt_one.trans_le hb.1) (fun i=>n i)).symm
    _ = _ :=by
      rw [←Complex.ofReal_sum,product_partition K R A B h a b hK hh ha hb]

def effectiveScale (C D:Ideal O)(E:Finset (CommonIndex C D))(K:ℝ):ℝ:=
  (K/‖eisEmbedding (primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E)‖^2)/
    ‖eisEmbedding (activeConductor C D)‖^2

lemma effectiveScale_pos (C D:Ideal O)(E:Finset (CommonIndex C D))(K:ℝ)(hK:0<K):
    0<effectiveScale C D E K:=by
  unfold effectiveScale
  apply div_pos (div_pos hK ?_) ?_
  · exact sq_pos_of_pos (norm_pos_iff.mpr (eisEmbedding_ne_zero (primeSubsetGenerator_ne_zero _ _)))
  · exact sq_pos_of_pos (norm_pos_iff.mpr (eisEmbedding_ne_zero (finitePrimeModulus_ne_zero _)))

lemma element_norm (C D:Ideal O)(hD:D≠0)(S:Finset (Ideal O))(a:columns C D hD S):
    ‖eisEmbedding (element C D hD S a)‖^2=((a:Ideal O).absNorm:ℝ):=by
  rw [eisEmbedding_norm_sq_eq_absNorm_span,element_span]

lemma element_norm_ge_one (C D:Ideal O)(hD:D≠0)(S:Finset (Ideal O))(a:columns C D hD S):
    1≤‖eisEmbedding (element C D hD S a)‖^2:=by
  rw [element_norm]
  exact_mod_cast Nat.one_le_iff_ne_zero.mpr
    (Ideal.absNorm_eq_zero_iff.not.mpr (column_supported C D hD S a).1)

lemma element_norm_le (C D:Ideal O)(hD:D≠0)(S:Finset (Ideal O))(a:columns C D hD S)
    (c:Ideal O→ℂ)(H:ℝ)(hcap:∀I,c I≠0→(I.absNorm:ℝ)≤H)(ha:c (D*a)≠0):
    ‖eisEmbedding (element C D hD S a)‖^2≤H/(D.absNorm:ℝ):=by
  have hDpos:(0:ℝ)<D.absNorm:=by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hD)
  rw [element_norm]
  apply (le_div_iff₀ hDpos).mpr
  simpa only [map_mul,Nat.cast_mul,mul_comm] using hcap (D*a) ha

theorem retainedBlock_eq_blocks
    (η:Character)(m A:O)(t:ℝ)(S:Finset (Ideal O))(c:Ideal O→ℂ)
    (C D:Ideal O)(hC:Supported C)(hD:Supported D)(E:Finset (CommonIndex C D))
    (rows:Finset O)(hrows:∀h∈rows,h≠0)(W:𝓢(ℝ,ℂ))(K R H:ℝ)(hK:0<K)
    (hcap:∀I,c I≠0→(I.absNorm:ℝ)≤H):
    retainedBlock η m A t S c C D hC hD E rows W K R=
      ∑n:Blocks (effectiveScale C D E K) R (H/(C.absNorm:ℝ)) (H/(D.absNorm:ℝ)),
        block η m A t S c C D hC hD E rows W (fun _=>logAnnulus) K
          (dyadicScale (n 0)) (dyadicScale (n 1)) (dyadicScale (n 2)) (dyadicScale (n 3)):=by
  unfold retainedBlock block
  dsimp only
  rw [←Finset.mul_sum]
  congr 1
  conv_rhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro h hh
  conv_rhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a ha
  conv_rhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b hb
  by_cases hab:IsCoprime (a:Ideal O) (b:Ideal O)
  · simp only [hab,ite_true]
    by_cases hca:c (C*(a:Ideal O))=0
    · simp [coefficient,hca]
    by_cases hcb:c (D*(b:Ideal O))=0
    · simp [coefficient,hcb]
    have hnorm:1≤‖eisEmbedding h‖^2:=by
      rw [eisEmbedding_norm_sq_eq_absNorm_span]
      exact_mod_cast Nat.one_le_iff_ne_zero.mpr
        (Ideal.absNorm_eq_zero_iff.not.mpr (Ideal.span_singleton_eq_bot.not.mpr (hrows h hh)))
    have hpart:=windows_partition (effectiveScale C D E K) R
      (H/(C.absNorm:ℝ)) (H/(D.absNorm:ℝ)) (‖eisEmbedding h‖^2)
      (‖eisEmbedding (element C C hC.1 S a)‖^2) (‖eisEmbedding (element C D hD.1 S b)‖^2)
      (effectiveScale_pos C D E K hK) hnorm
      ⟨element_norm_ge_one C C hC.1 S a,element_norm_le C C hC.1 S a c H hcap hca⟩
      ⟨element_norm_ge_one C D hD.1 S b,element_norm_le C D hD.1 S b c H hcap hcb⟩
    rw [←Finset.sum_mul,←Finset.mul_sum]
    congr 1
    congr 1
    exact hpart.symm
  · simp [hab]

lemma block_retained (K R A B:ℝ)(n:Blocks K R A B):Retained R (n 1):=
  ((mem_retainedIndices R (n 1)).mp (n 1).property).1

def retainedInfiniteBlock (η:Character)(m A:O)(t:ℝ)(S:Finset (Ideal O))(c:Ideal O→ℂ)
    (C D:Ideal O)(hC:Supported C)(hD:Supported D)(E:Finset (CommonIndex C D))
    (W:𝓢(ℝ,ℂ))(K R:ℝ):ℂ:=
  let e:=primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E
  let k:=K/‖eisEmbedding e‖^2
  let r:=activeConductor C D
  inactiveWeight C D E * ∑'h:O,
    ∑a:columns C C hC.1 S,∑b:columns C D hD.1 S,
      let na:=element C C hC.1 S a
      let nb:=element C D hD.1 S b
      if IsCoprime (a:Ideal O) (b:Ideal O) then
        (tripleRow na nb r (supportedModulusCharacter na (element_supported C C hC.1 S a))
          (supportedModulusCharacter nb (element_supported C D hD.1 S b))⁻¹ (activeFunction C D hC) e *
        ((k/‖eisEmbedding (na*(nb*r))‖^2:ℝ):ℂ)*
        tripleFourier na nb r
          (supported_element_ne_zero _ (element_supported C C hC.1 S a))
          (supported_element_ne_zero _ (element_supported C D hD.1 S b))
          (finitePrimeModulus_ne_zero _) (supportedModulusCharacter na (element_supported C C hC.1 S a))
          (supportedModulusCharacter nb (element_supported C D hD.1 S b))⁻¹ (activeFunction C D hC) h)*
        (coefficient η m A t c C a*star (coefficient η m A t c D b))*
        (retainedWeight R (‖eisEmbedding h‖^2):ℂ)*
        EisensteinSchwartzPoisson.paperRadialFourier W (k*‖eisEmbedding h‖^2/‖eisEmbedding (na*(nb*r))‖^2)
      else 0

lemma retained_rows_nonzero (R:ℝ):
    ∀h∈CenteredMomentSecondRetainedRows.retainedRows R 1,h≠0:=by
  intro h hh hz
  have hn:=(mem_rowNormDisk.mp hh).1
  subst h
  simp at hn

theorem retainedInfiniteBlock_eq_finite
    (η:Character)(m A:O)(t:ℝ)(S:Finset (Ideal O))(c:Ideal O→ℂ)
    (C D:Ideal O)(hC:Supported C)(hD:Supported D)(E:Finset (CommonIndex C D))
    (W:𝓢(ℝ,ℂ))(K R:ℝ):
    retainedInfiniteBlock η m A t S c C D hC hD E W K R=
      retainedBlock η m A t S c C D hC hD E
        (CenteredMomentSecondRetainedRows.retainedRows R 1) W K R:=by
  unfold retainedInfiniteBlock retainedBlock
  dsimp only
  congr 1
  apply tsum_eq_sum
  intro h hh
  have hz:retainedWeight R (‖eisEmbedding h‖^2)=0:=by
    by_contra hn
    apply hh
    apply CenteredMomentSecondRetainedRows.retained_mem_rows R 1 h one_ne_zero
    simpa only [one_mul,normValue_eq_embedding] using hn
  simp only [hz,Complex.ofReal_zero,mul_zero,zero_mul,ite_self,Finset.sum_const_zero]

theorem original_retained_dyadic
    {ι:Type*}[Fintype ι][DecidableEq ι]
    (s:CenteredMomentCommonRadialData.Input ι)(Rbad seed:Ideal O)
    (hz₁:s.W₁ 0=0)(hz₂:s.W₂ 0=0)
    (m A:O)(t:ℝ)(S:Finset (Ideal O))
    (C D:Ideal O)(hC:Supported C)(hD:Supported D)(E:Finset (CommonIndex C D))
    (W:𝓢(ℝ,ℂ))(K R:ℝ)(hK:0<K):
    retainedInfiniteBlock s.η m A t S
      (CenteredMomentOriginalCommonHarmonic.coefficient s Rbad seed) C D hC hD E W K R=
      ∑n:Blocks (effectiveScale C D E K) R
          (CenteredMomentOriginalCommonHarmonic.sourceRadius s/(C.absNorm:ℝ))
          (CenteredMomentOriginalCommonHarmonic.sourceRadius s/(D.absNorm:ℝ)),
        block s.η m A t S (CenteredMomentOriginalCommonHarmonic.coefficient s Rbad seed)
          C D hC hD E (CenteredMomentSecondRetainedRows.retainedRows R 1) W
          (fun _=>logAnnulus) K (dyadicScale (n 0)) (dyadicScale (n 1))
            (dyadicScale (n 2)) (dyadicScale (n 3)):=by
  rw [retainedInfiniteBlock_eq_finite]
  exact retainedBlock_eq_blocks s.η m A t S _ C D hC hD E _
    (retained_rows_nonzero R) W K R _ hK
    (fun I hI=>(CenteredMomentOriginalCommonHarmonic.original_column_norm s Rbad seed I hz₁ hz₂ hI).2)

end SevenEighths.CenteredMomentFirstPhysicalDyadicAssembly

end

end OAI
