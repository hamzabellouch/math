import OAI.NumberTheory.DirichletL.QuadraticSieve.CuspCoercivity

namespace OAI

noncomputable section

namespace CanonicalQuadraticSieve

open scoped BigOperators
open MulChar AddChar
open scoped BigOperators
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped FourierTransform SchwartzMap
open Finset Complex
open scoped Classical
open scoped Classical
open Filter Real Asymptotics
open ActualEisensteinCubic
open Filter
open ActualEisensteinCubic RationalPrimeExtraction ShortDraftLatticeCount
open ActualEisensteinCubic ShortDraftLatticeCount
open Filter
open scoped Topology
open EisensteinEmbedding ConcreteTraceCRT ActualEisensteinCubic
open MulChar AddChar
open Filter Asymptotics
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter
open MulChar AddChar
open MulChar AddChar
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Filter Asymptotics
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics Ideal NumberField
open Filter
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped ContDiff FourierTransform SchwartzMap
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open MeasureTheory Set
open scoped BigOperators
open scoped BigOperators Classical
open scoped BigOperators Classical
open ActualEisensteinCubic UniqueFactorizationMonoid
open scoped BigOperators

section

open scoped BigOperators Classical SchwartzMap

section
open ActualEisensteinCubic ConcreteTraceCRT ConcretePrimeRowBridge CompletedGauss
open EisensteinSchwartzPoisson UnrestrictedIdealReindex IdealMobiusDivisorSum

def maskedPairDualTail (G I J : Ideal O) (W : 𝓢(ℝ,ℂ)) (M K : ℝ) : ℂ :=
  ((M:ℂ)/(Real.sqrt ((Ideal.absNorm I:ℝ)*(Ideal.absNorm J:ℝ)):ℂ))*
    ∑ q ∈ idealDivisors G,
      ((UniqueFactorizationMonoid.moebius q:ℂ)*unrestrictedPairCharacter I J q/(Ideal.absNorm q:ℂ))*
        dualSquarefreeTail I J W
          (M/((Ideal.absNorm q:ℝ)*(Ideal.absNorm I:ℝ)*(Ideal.absNorm J:ℝ))) K

def retainedDualPair (I J : Ideal O) (W : 𝓢(ℝ,ℂ)) (M F K : ℝ) : ℂ :=
  ∑ B : squarefreeIdealRange K, unrestrictedPairCharacter I J B.val*
    (((M/(Real.sqrt ((Ideal.absNorm I:ℝ)*(Ideal.absNorm J:ℝ))*F):ℝ):ℂ)*
      dualPrincipalIdeal I J W
        (Real.sqrt (F*(Ideal.absNorm I:ℝ)*(Ideal.absNorm J:ℝ)/(M*(Ideal.absNorm B.val:ℝ)))))

theorem maskedPairIdealDualKernel_retained
    (G I J : Ideal O) (hG : G ≠ 0) (hI : Admissible I) (hJ : Admissible J)
    (hray : columnRay I=columnRay J) (W : 𝓢(ℝ,ℂ)) (M K : ℝ) (hM : 0<M) :
    maskedPairIdealDualKernel G I J W M =
      (∑ q ∈ idealDivisors G, (UniqueFactorizationMonoid.moebius q:ℂ)*unrestrictedPairCharacter I J q*
        retainedDualPair I J (quadraticTransformedSquareProfile W) M (Ideal.absNorm q:ℝ) K) +
      maskedPairDualTail G I J W M K := by
  have hNI : 0<(Ideal.absNorm I:ℝ) := by
    exact_mod_cast Nat.pos_iff_ne_zero.mpr (fun hz => hI.1 (Ideal.absNorm_eq_zero_iff.mp hz))
  have hNJ : 0<(Ideal.absNorm J:ℝ) := by
    exact_mod_cast Nat.pos_iff_ne_zero.mpr (fun hz => hJ.1 (Ideal.absNorm_eq_zero_iff.mp hz))
  have hqpos (q : Ideal O) (hq : q ∈ idealDivisors G) : 0<(Ideal.absNorm q:ℝ) := by
    have hqG := (mem_idealDivisors hG).mp hq
    have hq0 : q ≠ 0 := by intro hz; rw [hz,zero_dvd_iff] at hqG; exact hG hqG
    exact_mod_cast Nat.pos_iff_ne_zero.mpr (fun hz => hq0 (Ideal.absNorm_eq_zero_iff.mp hz))
  have hpoint (q : Ideal O) (hq : q ∈ idealDivisors G) :
      ((M:ℂ)/(Real.sqrt ((Ideal.absNorm I:ℝ)*(Ideal.absNorm J:ℝ)):ℂ))*
        (((UniqueFactorizationMonoid.moebius q:ℂ)*unrestrictedPairCharacter I J q/(Ideal.absNorm q:ℂ))*
          ∑' B : NonzeroIdeal, unrestrictedPairCharacter I J B.val*paperRadialFourier W
            ((M/((Ideal.absNorm q:ℝ)*(Ideal.absNorm I:ℝ)*(Ideal.absNorm J:ℝ)))*(Ideal.absNorm B.val:ℝ))) =
        (UniqueFactorizationMonoid.moebius q:ℂ)*unrestrictedPairCharacter I J q*
          retainedDualPair I J (quadraticTransformedSquareProfile W) M (Ideal.absNorm q:ℝ) K +
        ((M:ℂ)/(Real.sqrt ((Ideal.absNorm I:ℝ)*(Ideal.absNorm J:ℝ)):ℂ))*
          (((UniqueFactorizationMonoid.moebius q:ℂ)*unrestrictedPairCharacter I J q/(Ideal.absNorm q:ℂ))*
            dualSquarefreeTail I J W
              (M/((Ideal.absNorm q:ℝ)*(Ideal.absNorm I:ℝ)*(Ideal.absNorm J:ℝ))) K) := by
    have hqN := hqpos q hq
    have ht : 0 < M/((Ideal.absNorm q:ℝ)*(Ideal.absNorm I:ℝ)*(Ideal.absNorm J:ℝ)) := by
      positivity
    rw [dual_ideal_low_add_tail I J W _ K ht,dualSquarefreeLow_principal_finite I J hI hJ hray W _ K ht,
      mul_add,mul_add]
    congr 1
    simp only [retainedDualPair,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro B _
    have hB : 0<(Ideal.absNorm B.val:ℝ) := by
      exact_mod_cast Nat.pos_iff_ne_zero.mpr
        (fun hz => (mem_squarefreeIdealRange.mp B.property).1.ne_zero (Ideal.absNorm_eq_zero_iff.mp hz))
    have harg : (1:ℝ)/((M/((Ideal.absNorm q:ℝ)*(Ideal.absNorm I:ℝ)*(Ideal.absNorm J:ℝ)))*(Ideal.absNorm B.val:ℝ)) =
        (Ideal.absNorm q:ℝ)*(Ideal.absNorm I:ℝ)*(Ideal.absNorm J:ℝ)/(M*(Ideal.absNorm B.val:ℝ)) := by
      field_simp
    rw [harg]
    push_cast
    ring
  unfold maskedPairIdealDualKernel maskedPairDualTail
  rw [Finset.mul_sum,Finset.mul_sum,← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl hpoint

end

section
open ActualEisensteinCubic ConcretePrimeRowBridge IdealMobiusDivisorSum EisensteinSchwartzPoisson

theorem retainedDualPrincipalSum_pair_expansion {n : Type} [Fintype n] [DecidableEq n]
    (W : 𝓢(ℝ,ℂ)) (cols : n → Ideal O) (a : n → ℂ) (M F K : ℝ) :
    retainedDualPrincipalSum W (fun I : squarefreeIdealRange K => I.val) cols a M F =
      ∑ j, ∑ k, if IsCoprime (cols j) (cols k) then
        star (a j)*a k*retainedDualPair (cols j) (cols k) W M F K else 0 := by
  unfold retainedDualPrincipalSum
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k _
  by_cases hc : IsCoprime (cols j) (cols k)
  · simp only [unrestrictedPairTerm,retainedDualPair,hc,ite_true,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro B _
    ring
  · simp only [unrestrictedPairTerm,hc,ite_false,zero_mul,Finset.sum_const_zero]

theorem retainedDualPrincipalSum_twist_expansion {n : Type} [Fintype n] [DecidableEq n]
    (W : 𝓢(ℝ,ℂ)) (cols : n → Ideal O) (a : n → ℂ) (M F K : ℝ) (q : Ideal O)
    (hcols : ∀ j, Admissible (cols j)) :
    retainedDualPrincipalSum W (fun I : squarefreeIdealRange K => I.val) cols
      (fun j => a j*quadraticRow (cols j) (idealGenerator q)) M F =
      ∑ j, ∑ k, if IsCoprime (cols j) (cols k) then
        star (a j)*a k*unrestrictedPairCharacter (cols j) (cols k) q*
          retainedDualPair (cols j) (cols k) W M F K else 0 := by
  rw [retainedDualPrincipalSum_pair_expansion]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro k _
  by_cases hc : IsCoprime (cols j) (cols k)
  · simp only [hc,ite_true,star_mul,canonical_quadraticRow_star _ (hcols j),unrestrictedPairCharacter]
    ring
  · simp only [hc,ite_false]

def maskedDualFamily {n : Type} [Fintype n]
    (G : Ideal O) (cols : n → Ideal O) (a : n → ℂ) (W : 𝓢(ℝ,ℂ)) (M : ℝ) : ℂ :=
  ∑ j, ∑ k, if IsCoprime (cols j) (cols k) then
    star (a j)*a k*maskedPairIdealDualKernel G (cols j) (cols k) W M else 0

def maskedDualTailFamily {n : Type} [Fintype n]
    (G : Ideal O) (cols : n → Ideal O) (a : n → ℂ) (W : 𝓢(ℝ,ℂ)) (M K : ℝ) : ℂ :=
  ∑ j, ∑ k, if IsCoprime (cols j) (cols k) then
    star (a j)*a k*maskedPairDualTail G (cols j) (cols k) W M K else 0

theorem maskedDualFamily_retained {n : Type} [Fintype n] [DecidableEq n]
    (G : Ideal O) (hG : G ≠ 0) (cols : n → Ideal O) (a : n → ℂ)
    (W : 𝓢(ℝ,ℂ)) (M K : ℝ) (hM : 0<M) (hcols : ∀ j, Admissible (cols j))
    (hray : ∀ j k, columnRay (cols j)=columnRay (cols k)) :
    maskedDualFamily G cols a W M =
      (∑ q ∈ idealDivisors G, (UniqueFactorizationMonoid.moebius q:ℂ)*
        retainedDualPrincipalSum (quadraticTransformedSquareProfile W)
          (fun I : squarefreeIdealRange K => I.val) cols
          (fun j => a j*quadraticRow (cols j) (idealGenerator q)) M (Ideal.absNorm q:ℝ)) +
      maskedDualTailFamily G cols a W M K := by
  have hp (j k : n) :
      (if IsCoprime (cols j) (cols k) then
        star (a j)*a k*maskedPairIdealDualKernel G (cols j) (cols k) W M else 0) =
      (∑ q ∈ idealDivisors G, (UniqueFactorizationMonoid.moebius q:ℂ)*
        (if IsCoprime (cols j) (cols k) then
          star (a j)*a k*unrestrictedPairCharacter (cols j) (cols k) q*
            retainedDualPair (cols j) (cols k) (quadraticTransformedSquareProfile W) M (Ideal.absNorm q:ℝ) K
          else 0)) +
      (if IsCoprime (cols j) (cols k) then
        star (a j)*a k*maskedPairDualTail G (cols j) (cols k) W M K else 0) := by
    by_cases hc : IsCoprime (cols j) (cols k)
    · simp only [hc,ite_true,maskedPairIdealDualKernel_retained G (cols j) (cols k)
        hG (hcols j) (hcols k) (hray j k) W M K hM,mul_add,Finset.mul_sum]
      congr 1
      apply Finset.sum_congr rfl
      intro q hq
      ring
    · simp only [hc,ite_false,mul_zero,Finset.sum_const_zero,add_zero]
  simp only [maskedDualFamily,hp,Finset.sum_add_distrib,maskedDualTailFamily]
  congr 1
  simp_rw [Finset.sum_comm (s := (Finset.univ : Finset n)) (t := idealDivisors G)]
  apply Finset.sum_congr rfl
  intro q hq
  rw [retainedDualPrincipalSum_twist_expansion _ cols a _ _ _ q hcols]
  simp only [Finset.mul_sum]

end

section
open ActualEisensteinCubic ConcreteTraceCRT ConcretePrimeRowBridge EisensteinSchwartzPoisson CompletedGauss
open IdealMobiusDivisorSum

theorem normalizedFactors_commonMaskIdeal (D : Ideal O) :
    UniqueFactorizationMonoid.normalizedFactors (commonMaskIdeal D) = (gcdMaskPrimes D).val := by
  have hp (P : Ideal O) (hP : P∈(gcdMaskPrimes D).val) : Prime P := by
    let : P.IsMaximal := gcdMaskPrimes_maximal D ⟨P,hP⟩
    exact Ideal.prime_of_isPrime (NeZero.ne P) inferInstance
  have h := UniqueFactorizationMonoid.normalizedFactors_prod_of_prime hp
  simpa only [commonMaskIdeal,Finset.prod_val,id_eq] using h

theorem idealZeroMask_commonMaskIdeal (D : Ideal O) (z : O) :
    idealZeroMask (commonMaskIdeal D) z =
      rowCoprimeMask (fun P : gcdMaskPrimes D => P.val) Finset.univ z := by
  classical
  simp only [idealZeroMask,normalizedFactors_commonMaskIdeal,rowCoprimeMask,
    Finset.mem_univ,true_and,Subtype.exists,exists_prop,Finset.mem_val]

lemma idealZeroMask_idempotent (D : Ideal O) (z : O) :
    idealZeroMask D z*idealZeroMask D z=idealZeroMask D z := by
  classical
  unfold idealZeroMask
  split_ifs <;> norm_num

theorem idealZeroMask_generator_eq_indicator (D B : Ideal O) (hD : D≠0) :
    idealZeroMask D (idealGenerator B) = if IsCoprime B D then 1 else 0 := by
  classical
  by_cases hc : IsCoprime B D
  · rw [ite_eq_left hc,idealZeroMask_generator_eq_one D B hc.symm]
  · rw [ite_eq_right hc]
    apply ite_eq_left
    by_contra hn
    apply hc
    apply IsCoprime.symm
    apply ideals_coprime_of_relprime
    apply (UniqueFactorizationMonoid.isRelPrime_iff_no_prime_factors hD).mpr
    intro P hPD hPB hp
    have hfac : P∈UniqueFactorizationMonoid.normalizedFactors D :=
      (UniqueFactorizationMonoid.mem_normalizedFactors_iff hD).mpr ⟨hp,hPD⟩
    have hgen : idealGenerator B∈P := by
      apply (Ideal.span_singleton_le_iff_mem P).mp
      rw [span_idealGenerator]
      exact Ideal.dvd_iff_le.mp hPB
    exact hn ⟨P,hfac,hgen⟩

theorem idealZeroMask_primary_eq_indicator (D B : Ideal O) (hD : D≠0) (hB : Supported B) :
    idealZeroMask D (primaryGenerator B) = if IsCoprime B D then 1 else 0 := by
  have he : Ideal.span {primaryGenerator B}=Ideal.span {idealGenerator B} := by
    rw [(primaryGenerator_spec B (supported_primaryGenerator_ne_zero B hB)).1,span_idealGenerator]
  rw [idealZeroMask_span_eq D _ _ he,idealZeroMask_generator_eq_indicator D B hD]

theorem commonMask_primary_indicator (D B : Ideal O) (hB : Supported B) :
    idealZeroMask D (primaryGenerator B) = if IsCoprime B (commonMaskIdeal D) then 1 else 0 := by
  have he := idealZeroMask_commonMaskIdeal D (primaryGenerator B)
  rw [gcdMaskPrimes_mask,badPrime_mask_primaryGenerator,ite_eq_left hB,one_mul] at he
  rw [←he,idealZeroMask_primary_eq_indicator _ B (commonMaskIdeal_squarefree D).ne_zero hB]

theorem residual_joint_mask (D I J : Ideal O) (hI : Admissible I) (hJ : Admissible J)
    (hDI : D∣I) (hDJ : D∣J) (z : O) :
    rowCoprimeMask (fun P : gcdMaskPrimes (I*J) => P.val) Finset.univ z =
      rowCoprimeMask (fun P : primePool {commonMaskIdeal D*(idealQuotient D I*idealQuotient D J)} => P.val)
        Finset.univ z := by
  have hD := admissible_of_dvd hI hDI
  have hIq := admissible_idealQuotient hI hDI
  have hJq := admissible_idealQuotient hJ hDJ
  have hi : idealZeroMask I z=idealZeroMask D z*idealZeroMask (idealQuotient D I) z := by
    calc
      _ = idealZeroMask (D*idealQuotient D I) z := congrArg (fun A => idealZeroMask A z) (idealQuotient_mul hDI).symm
      _ = _ := idealZeroMask_mul D _ hD.1 hIq.1 z
  have hj : idealZeroMask J z=idealZeroMask D z*idealZeroMask (idealQuotient D J) z := by
    calc
      _ = idealZeroMask (D*idealQuotient D J) z := congrArg (fun A => idealZeroMask A z) (idealQuotient_mul hDJ).symm
      _ = _ := idealZeroMask_mul D _ hD.1 hJq.1 z
  rw [gcdMaskPrimes_mask,singleton_rowCoprimeMask_eq_idealZeroMask,
    idealZeroMask_mul I J hI.1 hJ.1,
    idealZeroMask_mul (commonMaskIdeal D) _ (commonMaskIdeal_squarefree D).ne_zero (mul_ne_zero hIq.1 hJq.1),
    idealZeroMask_mul _ _ hIq.1 hJq.1,idealZeroMask_commonMaskIdeal,gcdMaskPrimes_mask,hi,hj]
  calc
    _ = (rowCoprimeMask badPrime Finset.univ z)*(idealZeroMask D z*idealZeroMask D z)*
      (idealZeroMask (idealQuotient D I) z*idealZeroMask (idealQuotient D J) z) := by ring
    _ = _ := by rw [idealZeroMask_idempotent]

theorem lowPrincipalLattice_residual (D I J : Ideal O) (hI : Admissible I) (hJ : Admissible J)
    (hDI : D∣I) (hDJ : D∣J) (W : 𝓢(ℝ,ℂ)) (X : ℝ) :
    lowPrincipalLattice I J W X =
      ∑' z : O, rowCoprimeMask
        (fun P : primePool {commonMaskIdeal D*(idealQuotient D I*idealQuotient D J)} => P.val) Finset.univ z *
        (if z=0 then 0 else quadraticSquareProfile W (‖eisEmbedding z‖^2/X)) := by
  unfold lowPrincipalLattice
  apply tsum_congr
  intro z
  by_cases hz : z=0
  · subst z
    simp only [jointMask_zero,ite_true,mul_zero,zero_mul]
  · rw [ite_eq_right hz,quadraticSquareProfile_apply,residual_joint_mask D I J hI hJ hDI hDJ]

theorem idealRange_filter_coprime (G : Ideal O) (K : ℝ)
    (hbad : ∀ P∈fixedBadPrimes, P∣G) :
    (idealRange K).filter (fun B => IsCoprime B G)=coprimeSquarefreeRange G K := by
  classical
  ext B
  constructor
  · intro h
    obtain ⟨hb,hc⟩ := Finset.mem_filter.mp h
    have hB := mem_idealRange.mp hb
    exact Finset.mem_filter.mpr ⟨mem_squarefreeIdealRange.mpr ⟨hB.1.2.1,hB.2⟩,hc⟩
  · intro h
    refine Finset.mem_filter.mpr ⟨?_,(Finset.mem_filter.mp h).2⟩
    exact coprimeSquarefreeRange_subset_idealRange G hbad K h

theorem sum_idealRange_coprime (G : Ideal O) (K : ℝ)
    (hbad : ∀ P∈fixedBadPrimes, P∣G) (f : Ideal O → ℂ) :
    (∑ B : idealRange K, if IsCoprime B.val G then f B.val else 0) =
      ∑ B : coprimeSquarefreeRange G K, f B.val := by
  classical
  rw [Finset.sum_coe_sort (idealRange K) (fun B => if IsCoprime B G then f B else 0),
    ←Finset.sum_filter,idealRange_filter_coprime G K hbad,
    Finset.sum_coe_sort (coprimeSquarefreeRange G K) f]

def pairMaskedSquareSource (G I J : Ideal O) (W : 𝓢(ℝ,ℂ)) (M : ℝ) (B : Ideal O) : ℂ :=
  (quadraticRow I (primaryGenerator B)*quadraticRow J (primaryGenerator B))*
    ∑' z : O, rowCoprimeMask (fun P : primePool {G*(I*J)} => P.val) Finset.univ z *
      (if z=0 then 0 else quadraticSquareProfile W (‖eisEmbedding z‖^2/sourcePrincipalScale M B))

theorem originalPairLow_residual_finite (D I J : Ideal O) (hI : Admissible I) (hJ : Admissible J)
    (hDI : D∣I) (hDJ : D∣J) (W : 𝓢(ℝ,ℂ)) (M K : ℝ) (hM : 0<M) :
    (∑' lengthScale : Ideal O, originalPairLow I J W M K lengthScale) =
      (6:ℂ)⁻¹*∑ B : coprimeSquarefreeRange (commonMaskIdeal D) K,
        pairMaskedSquareSource (commonMaskIdeal D) (idealQuotient D I) (idealQuotient D J) W M B.val := by
  classical
  rw [originalPairLow_principal_finite I J hI hJ W M K hM]
  have ht (B : idealRange K) :
      (quadraticRow I (primaryGenerator B.val)*quadraticRow J (primaryGenerator B.val))*
        ((6:ℂ)⁻¹*lowPrincipalLattice I J W (Real.sqrt (M/(Ideal.absNorm B.val:ℝ)))) =
      (6:ℂ)⁻¹*(if IsCoprime B.val (commonMaskIdeal D) then
        pairMaskedSquareSource (commonMaskIdeal D) (idealQuotient D I) (idealQuotient D J) W M B.val else 0) := by
    have hB := admissible_supported (mem_idealRange.mp B.property).1
    have hp := canonical_pair_divisor_mask D I J hI hJ hDI hDJ (primaryGenerator B.val)
    rw [canonical_quadraticRow_star I hI,commonMask_primary_indicator D B.val hB] at hp
    rw [hp,lowPrincipalLattice_residual D I J hI hJ hDI hDJ]
    by_cases hc : IsCoprime B.val (commonMaskIdeal D)
    · simp only [hc,ite_true,one_mul,pairMaskedSquareSource,sourcePrincipalScale]
      ring
    · simp only [hc,ite_false,zero_mul,mul_zero]
  simp_rw [ht]
  rw [←Finset.mul_sum,sum_idealRange_coprime (commonMaskIdeal D) K
    (fun P hP => fixedBadPrimes_dvd_commonMaskIdeal D P hP)]

theorem originalLow_gcd_aggregate
    {n : Type} [Fintype n] [DecidableEq n]
    (D : Ideal O) (hD : D≠0) (cols : n → Ideal O) (hcols : ∀ j, Admissible (cols j))
    (hdiv : ∀ j, D∣cols j) (a : n → ℂ) (W : 𝓢(ℝ,ℂ)) (M K : ℝ) (hM : 0<M) :
    (∑ j, ∑ k, if gcd (cols j) (cols k)=D then
      star (a j)*a k*(∑' lengthScale : Ideal O, originalPairLow (cols j) (cols k) W M K lengthScale) else 0) =
      (6:ℂ)⁻¹ * maskedPrincipalSourceSum (commonMaskIdeal D) (quadraticSquareProfile W)
        (fun B : coprimeSquarefreeRange (commonMaskIdeal D) K => B.val)
        (fun j => idealQuotient D (cols j)) a M := by
  classical
  let S := coprimeSquarefreeRange (commonMaskIdeal D) K
  let q := fun j => idealQuotient D (cols j)
  have hq (j : n) : Admissible (q j) := admissible_idealQuotient (hcols j) (hdiv j)
  have ht (j k : n) :
      (if gcd (cols j) (cols k)=D then
        star (a j)*a k*(∑' lengthScale : Ideal O, originalPairLow (cols j) (cols k) W M K lengthScale) else 0) =
      (6:ℂ)⁻¹ * ∑ B : S,
        originalTerm (fun B : S => B.val) q q a a 1 1 B j k *
          ∑' z : O, rowCoprimeMask (fun P : primePool {commonMaskIdeal D*(q j*q k)} => P.val) Finset.univ z *
            (if z=0 then 0 else quadraticSquareProfile W (‖eisEmbedding z‖^2/sourcePrincipalScale M B.val)) := by
    have heq := gcd_eq_iff_quotient_coprime D (cols j) (cols k) hD (hdiv j) (hdiv k)
    by_cases hc : IsCoprime (q j) (q k)
    · rw [ite_eq_left (heq.mpr hc),originalPairLow_residual_finite D _ _ (hcols j) (hcols k) (hdiv j) (hdiv k) W M K hM]
      simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro B _
      simp only [originalTerm,hc,ite_true,one_dvd,pairMaskedSquareSource,star_mul,
        canonical_quadraticRow_star _ (hq j)]
      dsimp only [q]
      ring
    · have hg : ¬gcd (cols j) (cols k)=D := fun h => hc (heq.mp h)
      simp only [hg,ite_false,originalTerm,hc,Finset.sum_const_zero,zero_mul,mul_zero]
  simp_rw [ht,Finset.mul_sum]
  simp_rw [Finset.sum_comm (s := (Finset.univ:Finset n)) (t := (Finset.univ:Finset S))]
  simp only [maskedPrincipalSourceSum,Finset.mul_sum,S,q,sourcePrincipalScale]

end

open ActualEisensteinCubic ConcretePrimeRowBridge IdealMobiusDivisorSum EisensteinSchwartzPoisson

theorem originalDual_gcd_aggregate {n : Type} [Fintype n] [DecidableEq n]
    (D : Ideal O) (hD : D≠0) (cols : n → Ideal O) (hcols : ∀ j, Admissible (cols j))
    (hdiv : ∀ j, D∣cols j) (hproper : ∀ j, cols j≠D)
    (hray : ∀ j k, columnRay (cols j)=columnRay (cols k))
    (a : n → ℂ) (W : 𝓢(ℝ,ℂ)) (M : ℝ) (hM : 0<M) :
    (∑ j, ∑ k, if gcd (cols j) (cols k)=D then
      star (a j)*a k*originalPairDualKernel D (cols j) (cols k) W M else 0) =
      maskedDualFamily (commonMaskIdeal D) (fun j => idealQuotient D (cols j)) a W M := by
  unfold maskedDualFamily
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro k _
  have heq := gcd_eq_iff_quotient_coprime D (cols j) (cols k) hD (hdiv j) (hdiv k)
  by_cases hg : gcd (cols j) (cols k)=D
  · have hneq : cols j≠cols k := by
      intro h
      rw [← h] at hg
      exact hproper j (by simpa using hg)
    rw [ite_eq_left hg,ite_eq_left (heq.mp hg),
      originalPairDualKernel_eq_divisors D (cols j) (cols k) (hcols j) (hcols k)
        (hdiv j) (hdiv k) hneq (hray j k) W M hM]
  · rw [ite_eq_right hg,ite_eq_right (fun hc => hg (heq.mpr hc))]

theorem originalHigh_gcd_principal_assembly {n : Type} [Fintype n] [DecidableEq n]
    (D : Ideal O) (hD : D≠0) (cols : n → Ideal O) (hcols : ∀ j, Admissible (cols j))
    (hdiv : ∀ j, D∣cols j) (hproper : ∀ j, cols j≠D)
    (hray : ∀ j k, columnRay (cols j)=columnRay (cols k))
    (a : n → ℂ) (W : 𝓢(ℝ,ℂ)) (M K : ℝ) (hM : 0<M) :
    (∑ j, ∑ k, if gcd (cols j) (cols k)=D then
      star (a j)*a k*(∑' lengthScale : Ideal O, originalPairHigh (cols j) (cols k) W M K lengthScale) else 0) =
      (∑ q ∈ idealDivisors (commonMaskIdeal D), (UniqueFactorizationMonoid.moebius q:ℂ)*
        retainedDualPrincipalSum (quadraticTransformedSquareProfile W)
          (fun I : squarefreeIdealRange K => I.val) (fun j => idealQuotient D (cols j))
          (fun j => a j*quadraticRow (idealQuotient D (cols j)) (idealGenerator q)) M (Ideal.absNorm q:ℝ)) +
      maskedDualTailFamily (commonMaskIdeal D) (fun j => idealQuotient D (cols j)) a W M K -
      (6:ℂ)⁻¹ * maskedPrincipalSourceSum (commonMaskIdeal D) (quadraticSquareProfile W)
        (fun B : coprimeSquarefreeRange (commonMaskIdeal D) K => B.val)
        (fun j => idealQuotient D (cols j)) a M := by
  have hsplit :
      (∑ j, ∑ k, if gcd (cols j) (cols k)=D then
        star (a j)*a k*(∑' lengthScale : Ideal O, originalPairHigh (cols j) (cols k) W M K lengthScale) else 0) =
      (∑ j, ∑ k, if gcd (cols j) (cols k)=D then
        star (a j)*a k*originalPairDualKernel D (cols j) (cols k) W M else 0) -
      (∑ j, ∑ k, if gcd (cols j) (cols k)=D then
        star (a j)*a k*(∑' lengthScale : Ideal O, originalPairLow (cols j) (cols k) W M K lengthScale) else 0) := by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro j _
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro k _
    by_cases hg : gcd (cols j) (cols k)=D
    · rw [ite_eq_left hg,ite_eq_left hg,ite_eq_left hg,
        originalPairHigh_eq_source_sub_low (cols j) (cols k) W M K hM,
        originalPairSource_poisson D (cols j) (cols k) (hcols j) (hcols k) hg (hray j k) W M hM]
      ring
    · simp only [hg,ite_false,sub_self]
  rw [hsplit,originalDual_gcd_aggregate D hD cols hcols hdiv hproper hray a W M hM,
    originalLow_gcd_aggregate D hD cols hcols hdiv a W M K hM,
    maskedDualFamily_retained _ (commonMaskIdeal_squarefree D).ne_zero _ a W M K hM
      (fun j => admissible_idealQuotient (hcols j) (hdiv j))
      (fun j k => columnRay_idealQuotient_eq D (cols j) (cols k) (hcols j) (hcols k)
        (hdiv j) (hdiv k) (hray j k))]

end

section

open scoped BigOperators Classical
open ActualEisensteinCubic ConcretePrimeRowBridge IdealMobiusDivisorSum

theorem residual_commonMask_coprime (D I : Ideal O) (hI : Admissible I) (hDI : D∣I) :
    IsCoprime (commonMaskIdeal D) (idealQuotient D I) := by
  have hD := admissible_of_dvd hI hDI
  have hQ := admissible_idealQuotient hI hDI
  have hs : Squarefree (D*idealQuotient D I) := by rw [idealQuotient_mul hDI]; exact hI.2.1
  have hrel := (squarefree_mul_iff.mp hs).1
  have hG := (commonMaskIdeal_squarefree D).ne_zero
  apply ideals_coprime_of_relprime
  apply (UniqueFactorizationMonoid.isRelPrime_iff_no_prime_factors hG).mpr
  intro P hPG hPQ hp
  have hf : P∈UniqueFactorizationMonoid.normalizedFactors (commonMaskIdeal D) :=
    (UniqueFactorizationMonoid.mem_normalizedFactors_iff hG).mpr ⟨hp,hPG⟩
  rw [normalizedFactors_commonMaskIdeal] at hf
  have hmem : P∈fixedBadPrimes ∨ P∈primeSupport D := Finset.mem_union.mp hf
  rcases hmem with hbad | hPD
  · let : P.IsMaximal := (Ideal.isPrime_of_prime hp).isMaximal hp.ne_zero
    have hfac : P∈UniqueFactorizationMonoid.normalizedFactors (idealQuotient D I) :=
      (UniqueFactorizationMonoid.mem_normalizedFactors_iff hQ.1).mpr ⟨hp,hPQ⟩
    exact (prime_good_iff_not_bad P).mp (hQ.2.2 P hfac) hbad
  · have hd : P∣D := UniqueFactorizationMonoid.dvd_of_mem_normalizedFactors (Multiset.mem_toFinset.mp hPD)
    exact hp.not_isUnit (hrel hd hPQ)

theorem idealQuotient_norm_eq (D I : Ideal O) (hD : D≠0) (hDI : D∣I) :
    (Ideal.absNorm (idealQuotient D I):ℝ)=(Ideal.absNorm I:ℝ)/(Ideal.absNorm D:ℝ) := by
  have hn : (Ideal.absNorm D:ℝ)≠0 := by
    exact_mod_cast (show Ideal.absNorm D≠0 from fun h => hD (Ideal.absNorm_eq_zero_iff.mp h))
  apply (eq_div_iff hn).mpr
  rw [mul_comm,←Nat.cast_mul,←map_mul,idealQuotient_mul hDI]

theorem idealQuotient_shell (D I : Ideal O) (hD : D≠0) (hDI : D∣I) (N : ℝ)
    (hI : N/2≤(Ideal.absNorm I:ℝ) ∧ (Ideal.absNorm I:ℝ)≤N) :
    (N/(Ideal.absNorm D:ℝ))/2≤(Ideal.absNorm (idealQuotient D I):ℝ) ∧
      (Ideal.absNorm (idealQuotient D I):ℝ)≤N/(Ideal.absNorm D:ℝ) := by
  have hn : 0<(Ideal.absNorm D:ℝ) := by
    exact_mod_cast Nat.pos_iff_ne_zero.mpr (fun h => hD (Ideal.absNorm_eq_zero_iff.mp h))
  rw [idealQuotient_norm_eq D I hD hDI]
  constructor
  · calc
      _ = (N/2)/(Ideal.absNorm D:ℝ) := by ring
      _ ≤ _ := div_le_div_of_nonneg_right hI.1 hn.le
  · exact div_le_div_of_nonneg_right hI.2 hn.le

end

open scoped BigOperators Classical SchwartzMap
open ActualEisensteinCubic ConcretePrimeRowBridge IdealMobiusDivisorSum EisensteinSchwartzPoisson

def gcdRaySupport {n : Type} [Fintype n] (cols : n → Ideal O) (a : n → ℂ)
    (D : Ideal O) (c : EisensteinEPrimaryPhase.Coord) : Finset n :=
  Finset.univ.filter (fun j => D ∣ cols j ∧ columnRay (cols j)=c ∧ a j≠0)

theorem mem_gcdRaySupport {n : Type} [Fintype n] (cols : n → Ideal O) (a : n → ℂ)
    (D : Ideal O) (c : EisensteinEPrimaryPhase.Coord) (j : n) :
    j∈gcdRaySupport cols a D c ↔ D∣cols j ∧ columnRay (cols j)=c ∧ a j≠0 := by
  simp only [gcdRaySupport,Finset.mem_filter,Finset.mem_univ,true_and]

theorem gcd_ray_pair_sum_restrict {n : Type} [Fintype n]
    (cols : n → Ideal O) (a : n → ℂ) (D : Ideal O)
    (c : EisensteinEPrimaryPhase.Coord) (H : n → n → ℂ) :
    (∑ j, ∑ k, if gcd (cols j) (cols k)=D ∧ columnRay (cols j)=c ∧ columnRay (cols k)=c
      then star (a j)*a k*H j k else 0) =
    ∑ j : gcdRaySupport cols a D c, ∑ k : gcdRaySupport cols a D c,
      if gcd (cols j.val) (cols k.val)=D then star (a j.val)*a k.val*H j.val k.val else 0 := by
  classical
  let S := gcdRaySupport cols a D c
  let f := fun j k => if gcd (cols j) (cols k)=D ∧ columnRay (cols j)=c ∧ columnRay (cols k)=c
    then star (a j)*a k*H j k else 0
  have hjzero (j : n) (hj : j∉S) (k : n) : f j k=0 := by
    dsimp only [f]
    split_ifs with h
    · have hz : a j=0 := by
        by_contra hn
        apply hj
        exact (mem_gcdRaySupport cols a D c j).mpr
          ⟨h.1 ▸ GCDMonoid.gcd_dvd_left (cols j) (cols k),h.2.1,hn⟩
      simp only [hz,star_zero,zero_mul]
    · rfl
  have hkzero (k : n) (hk : k∉S) (j : n) : f j k=0 := by
    dsimp only [f]
    split_ifs with h
    · have hz : a k=0 := by
        by_contra hn
        apply hk
        exact (mem_gcdRaySupport cols a D c k).mpr
          ⟨h.1 ▸ GCDMonoid.gcd_dvd_right (cols j) (cols k),h.2.2,hn⟩
      simp only [hz,mul_zero,zero_mul]
    · rfl
  have hleft : (∑ j∈S, ∑ k, f j k) = ∑ j, ∑ k, f j k := by
    apply Finset.sum_subset (Finset.subset_univ S)
    intro j _ hj
    exact Finset.sum_eq_zero (fun k _ => hjzero j hj k)
  change (∑ j, ∑ k, f j k)=_
  rw [←hleft,←Finset.sum_coe_sort S (fun j => ∑ k, f j k)]
  apply Finset.sum_congr rfl
  intro j _
  have hright : (∑ k∈S, f j.val k) = ∑ k, f j.val k := by
    apply Finset.sum_subset (Finset.subset_univ S)
    intro k _ hk
    exact hkzero k hk j.val
  rw [←hright,←Finset.sum_coe_sort S (fun k => f j.val k)]
  apply Finset.sum_congr rfl
  intro k _
  have hj := (mem_gcdRaySupport cols a D c j.val).mp j.property
  have hk := (mem_gcdRaySupport cols a D c k.val).mp k.property
  simp only [f,hj.2.1,hk.2.1,and_true]

theorem gcdRaySupport_energy {n : Type} [Fintype n]
    (cols : n → Ideal O) (a : n → ℂ) (D : Ideal O) (c : EisensteinEPrimaryPhase.Coord) :
    (∑ j : gcdRaySupport cols a D c, ‖a j.val‖^2) ≤ ∑ j, ‖a j‖^2 := by
  rw [Finset.sum_coe_sort (gcdRaySupport cols a D c) (fun j => ‖a j‖^2)]
  exact Finset.sum_le_univ_sum_of_nonneg (fun j => sq_nonneg ‖a j‖)

theorem gcdRaySupport_quotient_properties (N X : ℝ) (a : idealRange N → ℂ)
    (ha : CoefficientOnShell N X a) (D : Ideal O) (hD : D≠0)
    (c : EisensteinEPrimaryPhase.Coord) :
    let cols := fun j : gcdRaySupport (fun I : idealRange N => I.val) a D c =>
      idealQuotient D j.val.val
    Function.Injective cols ∧
    (∀ j, Admissible (cols j) ∧
      (X/(Ideal.absNorm D:ℝ))/2≤(Ideal.absNorm (cols j):ℝ) ∧
      (Ideal.absNorm (cols j):ℝ)≤X/(Ideal.absNorm D:ℝ) ∧
      IsCoprime (commonMaskIdeal D) (cols j)) ∧
    (∀ j k, columnRay (cols j)=columnRay (cols k)) := by
  dsimp only
  have hp (j : gcdRaySupport (fun I : idealRange N => I.val) a D c) :=
    (mem_gcdRaySupport (fun I : idealRange N => I.val) a D c j.val).mp j.property
  refine ⟨?_,?_,?_⟩
  · intro j k hjk
    apply Subtype.ext
    apply Subtype.ext
    exact idealQuotient_injective_on D (hp j).1 (hp k).1 hjk
  · intro j
    have hadm := (mem_idealRange.mp j.val.property).1
    have hshell := idealQuotient_shell D j.val.val hD (hp j).1 X
      ⟨(ha j.val (hp j).2.2).1.le,(ha j.val (hp j).2.2).2⟩
    exact ⟨admissible_idealQuotient hadm (hp j).1,hshell.1,hshell.2,
      residual_commonMask_coprime D j.val.val hadm (hp j).1⟩
  · intro j k
    exact columnRay_idealQuotient_eq D j.val.val k.val.val
      (mem_idealRange.mp j.val.property).1 (mem_idealRange.mp k.val.property).1
      (hp j).1 (hp k).1 ((hp j).2.1.trans (hp k).2.1.symm)

theorem gcdRaySupport_proper (N X : ℝ) (a : idealRange N → ℂ)
    (ha : CoefficientOnShell N X a) (D : Ideal O) (c : EisensteinEPrimaryPhase.Coord)
    (hsmall : (Ideal.absNorm D:ℝ)≤X/2)
    (j : gcdRaySupport (fun I : idealRange N => I.val) a D c) : j.val.val≠D := by
  intro h
  have hp := (mem_gcdRaySupport (fun I : idealRange N => I.val) a D c j.val).mp j.property
  have hs := (ha j.val hp.2.2).1
  rw [h] at hs
  exact (not_lt_of_ge hsmall) hs

end CanonicalQuadraticSieve

end

end OAI
