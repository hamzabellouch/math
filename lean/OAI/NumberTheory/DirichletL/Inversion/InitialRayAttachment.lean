import OAI.NumberTheory.DirichletL.Inversion.InitialKernelBridge

namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap

namespace SevenEighths.InverseInitialRayAttachment
open ActualEisensteinCubic ConcretePrimeRowBridge CanonicalQuadraticSieve
open CanonicalRowCompletion CompletedGauss UniqueFactorizationMonoid
open FirstCauchyArithmetic SecondPassArithmetic ConcreteTraceCRT EisensteinSchwartzPoisson
open InverseInitialOverlap InverseInitialPoissonBridge InverseInitialKernelBridge
open InverseInitialArithmetic InverseInitialProfile
local notation "O" => ActualEisensteinCubic.O

def elementCharacter (η : Ideal O →* ℂ) : O →* ℂ where
  toFun x := η (Ideal.span {x})
  map_one' := by rw [Ideal.span_singleton_one, ←Ideal.one_eq_top, map_one]
  map_mul' x y := by rw [←Ideal.span_singleton_mul_span_singleton,map_mul]

theorem elementCharacter_product {ι : Type*} (η : Ideal O →* ℂ)
    (p : ι → O) (A : Finset ι) :
    elementCharacter η (∏ i ∈ A,p i) = η (∏ i ∈ A,Ideal.span {p i}) := by
  change η (Ideal.span {∏ i ∈ A,p i}) = _
  rw [FiniteGaussPhase.span_finset_prod]

def reconstructedSelector (S : Finset (Ideal O)) (P j : Ideal O)
    (a : Ideal O → ℂ) (A : Finset (primePool (columns S P j))) : ℂ :=
  if (∏ i ∈ A,i.val) ∈ columns S P j then a (reconstruct P j (∏ i ∈ A,i.val)) else 0

theorem poolPrimary_injective (F : Finset (Ideal O)) (hF : ∀ I ∈ F,Admissible I) :
    Function.Injective (fun i : primePool F => Ideal.span {poolPrimary F i}) := by
  intro i k he
  change Ideal.span {poolPrimary F i} = Ideal.span {poolPrimary F k} at he
  rw [poolPrimary_span F hF,poolPrimary_span F hF] at he
  exact Subtype.ext he

theorem poolPrimary_primary (F : Finset (Ideal O)) (hF : ∀ I ∈ F,Admissible I)
    (i : primePool F) : goodLambda^2 ∣ poolPrimary F i-1 :=
  (primaryPrime_spec i.val (poolPrimary_ne_zero F hF i)).2.2.2

theorem selected_mask (F : Finset (Ideal O)) (j : Ideal O) (hj : Admissible j)
    (A : Finset (primePool F)) (hcop : IsCoprime (∏ i ∈ A,i.val) j) :
    rowCoprimeMask (fun i : primePool F => i.val) A (primaryGenerator j)=1 := by
  have hspan := (primaryGenerator_spec j (primaryGenerator_admissible j hj)).1
  unfold rowCoprimeMask
  split_ifs with h
  · obtain ⟨i,hi,hm⟩ := h
    have hd : i.val ∣ ∏ k ∈ A,k.val := Finset.dvd_prod_of_mem _ hi
    have hjd : i.val ∣ j := by
      rw [Ideal.dvd_iff_le,←hspan]
      exact Ideal.span_le.mpr (Set.singleton_subset_iff.mpr hm)
    have hp : Prime i.val := Ideal.prime_of_isPrime (NeZero.ne i.val) inferInstance
    exact False.elim (hp.not_isUnit (hcop.isRelPrime hd hjd))
  · rfl

theorem selected_conjugate_row (F : Finset (Ideal O))
    (hF : ∀ I ∈ F,Admissible I) (j : Ideal O) (hj : Admissible j)
    (hcop : ∀ I ∈ F,IsCoprime I j) (η : Ideal O →* ℂ) (H : Ideal O → ℂ) (u : O) :
    let : ∀ i : primePool F,(Ideal.span {poolPrimary F i}).IsMaximal :=
      fun i => by rw [poolPrimary_span F hF i]; infer_instance
    (∑ I ∈ F,(moebius I : ℂ)*η I*H I*star (idealRowHom u I)) =
      inputConjugateRow (poolPrimary F) (poolPrimary_good F hF) Finset.univ
        (elementCharacter η) (primaryGenerator j) 1 1
        (fun A => if (∏ i ∈ A,i.val)∈F then H (∏ i ∈ A,i.val) else 0) u := by
  let : ∀ i : primePool F,(Ideal.span {poolPrimary F i}).IsMaximal :=
    fun i => by rw [poolPrimary_span F hF i]; infer_instance
  have he : (fun i : primePool F => Ideal.span {poolPrimary F i}) =
      (fun i : primePool F => i.val) := funext (poolPrimary_span F hF)
  dsimp only
  rw [InitialMeanSquare.sum_selected_ideals F (fun I hI => (hF I hI).2.1)]
  erw [initial_input_row]
  unfold supportConjugateSum
  apply Finset.sum_congr rfl
  intro A hA
  dsimp only
  rw [elementCharacter_product]
  simp only [he]
  by_cases hAF : (∏ i ∈ A,i.val)∈F
  · simp only [hAF,ite_true]
    rw [selected_mask F j hj A (hcop _ hAF),mul_one]
    rw [idealRowHom_eq_idealSexticRow F hF hAF]
    simp only [supportMobius,idealSexticRow,InitialMeanSquare.pool_support_product]
    ring
  · simp only [hAF,ite_false,mul_zero,zero_mul]

theorem residual_eq_input (S : Finset (Ideal O)) {P j : Ideal O}
    (hP : Admissible P) (hj : j ∣ P)
    (hS : ∀ n ∈ S,Squarefree n → Supported n)
    (η : Ideal O →* ℂ) (a : Ideal O → ℂ) (W : ℝ → ℂ)
    (Z r z G : ℝ) (u : O) :
    let F := columns S P j
    let hF : ∀ I ∈ F,Admissible I := fun I hI => columns_admissible S hP hj hS hI
    let : ∀ i : primePool F,(Ideal.span {poolPrimary F i}).IsMaximal :=
      fun i => by rw [poolPrimary_span F hF i]; infer_instance
    residualNormalizedPolynomial S P j η a W Z r z G u =
      (Z^(-(r+z-2*G)/2) : ℝ)*
        inputConjugateRow (poolPrimary F) (poolPrimary_good F hF) Finset.univ
          (elementCharacter η) (primaryGenerator j) 1 1
          (fun A => reconstructedSelector S P j a A *
            residualOverlapWindow P j W Z z G
              ((Ideal.absNorm (∏ i ∈ A,i.val) : ℝ)/Z^(r+z-2*G))) u := by
  intro F hF
  let : ∀ i : primePool F,(Ideal.span {poolPrimary F i}).IsMaximal :=
    fun i => by rw [poolPrimary_span F hF i]; infer_instance
  unfold residualNormalizedPolynomial
  congr 1
  have hc : ∀ I ∈ F,IsCoprime I j := fun I hI => ((mem_columns hP.2.1 hj).mp hI).2.1
  have ht := selected_conjugate_row F hF j (admissible_of_dvd hP hj) hc η
    (fun I => a (reconstruct P j I)*residualOverlapWindow P j W Z z G
      ((Ideal.absNorm I : ℝ)/Z^(r+z-2*G))) u
  convert ht using 1
  · apply Finset.sum_congr rfl
    intro I hI
    rw [overlapCoefficient_residual]
    unfold bareOverlapCoefficient
    ring
  · congr 1
    funext A
    unfold reconstructedSelector
    dsimp only [F]
    split_ifs <;> simp only [zero_mul]

section RayModes
variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) (hp : ∀ i,p i≠0) [∀ i,(Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i,goodLambda∉Ideal.span {p i})
open FirstPassCubeLabels (primeProductNorm primeProductNorm_union)

def initialTest (σ : Finset ι → ℂ) (V : ℝ → ℂ) (Z D : ℝ) (A : Finset ι) : ℂ :=
  σ A*V (primeProductNorm p A/Z^D)

def initialBeta (Ψ : O →* ℂ) (j : O) (G : Finset ι) : ℂ :=
  (‖Ψ (∏ i ∈ G,p i)*rowCoprimeMask (fun i => Ideal.span {p i}) G j‖^2 : ℝ)

theorem initial_overlap_weight (Ψ : O →* ℂ) (j : O)
    (σ : Finset ι → ℂ) (V : ℝ → ℂ) (Z D : ℝ) (G U T : Finset ι) :
    overlapPairWeight p hg Ψ j 1 1 (initialTest p σ V Z D) G U T =
      initialBeta p Ψ j G *
        star (supportMobius (fun i => Ideal.span {p i}) U *
          secondInputCoefficient p hg Ψ j 1 1 (fun A => σ (G∪A)) U) *
        (supportMobius (fun i => Ideal.span {p i}) T *
          secondInputCoefficient p hg Ψ j 1 1 (fun A => σ (G∪A)) T) *
        star (V (primeProductNorm p (G∪U)/Z^D))*V (primeProductNorm p (G∪T)/Z^D) := by
  have hrow (A : Finset ι) :
      finiteSquarefreeRow (fun i => Ideal.span {p i}) hg A 1 = 1 :=
    finiteSquarefreeRow_one _ hg A
  simp only [overlapPairWeight,secondInputCoefficient,initialBeta,initialTest,
    hrow,one_pow,mul_one,star_mul]
  ring

theorem initial_pair_rays
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (hc : ∀ i,ringChar (O ⧸ Ideal.span {p i})≠2)
    (hpr : ∀ i,goodLambda^2∣p i-1)
    (Ψ : O →* ℂ) (j e h : O) (σ : Finset ι → ℂ)
    (G U T : Finset ι) (hGU : Disjoint G U) (hGT : Disjoint G T) (hUT : Disjoint U T) :
    star (supportMobius (fun i => Ideal.span {p i}) U *
      secondInputCoefficient p hg Ψ j 1 1 (fun A => σ (G∪A)) U) *
      (supportMobius (fun i => Ideal.span {p i}) T *
        secondInputCoefficient p hg Ψ j 1 1 (fun A => σ (G∪A)) T) *
      activeGaussRowFactor p hp hinj hg T U e h =
    ∑ ρ : SecondRayIndex,secondRayCoefficient ρ *
      star (initialColumn p hp hcop hg (secondRayMinus Ψ ρ) j (∏ i ∈ G,p i) e h
        (fun A => σ (G∪A)) U) *
      initialColumn p hp hcop hg (secondRayPlus Ψ ρ) j (∏ i ∈ G,p i) e (-h)
        (fun A => σ (G∪A)) T := by
  have hm (A : Finset ι) (hAG : Disjoint A G) :
      secondInputCoefficient p hg Ψ (j*∏ i ∈ G,p i) 1 1 (fun A => σ (G∪A)) A =
        secondInputCoefficient p hg Ψ j 1 1 (fun A => σ (G∪A)) A := by
    erw [secondInputCoefficient_fixed_mask,commonProduct_mask p hg hinj]
    simp only [hAG,ite_true,one_mul]
  have he := second_gauss_ray_expansion p hp hcop hg hinj hc hpr Ψ Ψ
    (j*∏ i ∈ G,p i) 1 1 e h (fun A => σ (G∪A)) (fun A => σ (G∪A)) U T hUT
  rw [hm U hGU.symm,hm T hGT.symm] at he
  simpa only [Fintype.sum_prod_type,secondRayCoefficient,secondRayMinus,secondRayPlus,
    initialColumn_eq_secondPre] using he

omit [∀ i,(Ideal.span {p i}).IsMaximal] in

theorem initial_product_kernel (V : ℝ → ℂ) (Φ : 𝓢(ℝ,ℂ)) (Z D m : ℝ)
    (G U T E : Finset ι) (hGU : Disjoint G U) (hGT : Disjoint G T)
    (hUT : Disjoint U T) (h : O) :
    physicalKernel (fun x => star (V x)) V Φ Z D m
      (physicalCoordinates (sourceIdeal p G) (sourceIdeal p E) 1
        (sourceIdeal p U) (sourceIdeal p T) h) =
    ((Z^(-D) : ℝ) : ℂ)*star (V (primeProductNorm p (G∪U)/Z^D))*
      V (primeProductNorm p (G∪T)/Z^D)*
      ((Z^m : ℝ) : ℂ)/(‖eisEmbedding (∏ i : activeSupport T U,p i.val)‖ : ℂ) *
      (1/(‖eisEmbedding (primeSubsetGenerator (fun i => Ideal.span {p i}) E)‖^2 : ℝ)) *
      paperRadialFourier Φ (Z^m*‖eisEmbedding h‖^2/
        (‖eisEmbedding (primeSubsetGenerator (fun i => Ideal.span {p i}) E)‖^2 *
          ‖eisEmbedding (∏ i : activeSupport T U,p i.val)‖^2)) := by
  have hn := active_norm_sq_disjoint p U T hUT
  have hr : Real.sqrt (primeProductNorm p U*primeProductNorm p T) =
      ‖eisEmbedding (∏ i : activeSupport T U,p i.val)‖ := by
    rw [←hn,Real.sqrt_sq_eq_abs,abs_of_nonneg (norm_nonneg _)]
  have he : (Ideal.absNorm (sourceIdeal p E) : ℝ) =
      ‖eisEmbedding (primeSubsetGenerator (fun i => Ideal.span {p i}) E)‖^2 := by
    rw [primeSubsetGenerator_norm_sq,sourceIdeal,FiniteGaussPhase.span_finset_prod]
  have hnorm (A : Finset ι) : (Ideal.absNorm (sourceIdeal p A) : ℝ)=primeProductNorm p A :=
    (eisEmbedding_norm_sq_eq_absNorm_span _).symm
  unfold physicalKernel physicalCoordinates
  simp only [Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val,
    hnorm,map_one,Nat.cast_one,mul_one,one_pow]
  rw [hr,←hnorm E,he,hn]
  rw [primeProductNorm_union p G U hGU,primeProductNorm_union p G T hGT]
  push_cast
  ring_nf

def initialPhysicalMode (Ψ : O →* ℂ) (j : O) (σ : Finset ι → ℂ)
    (V : ℝ → ℂ) (Φ : 𝓢(ℝ,ℂ)) (Z D m : ℝ) (G U T E : Finset ι) (h : O) : ℂ :=
  initialBeta p Ψ j G * (moebius (sourceIdeal p E) : ℂ) *
    (∑ ρ : SecondRayIndex,secondRayCoefficient ρ *
      star (initialColumn p hp hcop hg (secondRayMinus Ψ ρ) j (∏ i ∈ G,p i)
        (primeSubsetGenerator (fun i => Ideal.span {p i}) E) h (fun A => σ (G∪A)) U) *
      initialColumn p hp hcop hg (secondRayPlus Ψ ρ) j (∏ i ∈ G,p i)
        (primeSubsetGenerator (fun i => Ideal.span {p i}) E) (-h) (fun A => σ (G∪A)) T) *
    physicalKernel (fun x => star (V x)) V Φ Z D m
      (physicalCoordinates (sourceIdeal p G) (sourceIdeal p E) 1
        (sourceIdeal p U) (sourceIdeal p T) h)

theorem normalized_overlap_mode
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (hc : ∀ i,ringChar (O ⧸ Ideal.span {p i})≠2)
    (hpr : ∀ i,goodLambda^2∣p i-1)
    (Ψ : O →* ℂ) (j : O) (σ : Finset ι → ℂ)
    (V : ℝ → ℂ) (Φ : 𝓢(ℝ,ℂ)) (Z D m : ℝ) (G U T E : Finset ι)
    (hGU : Disjoint G U) (hGT : Disjoint G T) (hUT : Disjoint U T) (h : O) :
    ((Z^(-D) : ℝ) : ℂ)*
      overlapPairWeight p hg Ψ j 1 1 (initialTest p σ V Z D) G U T *
      (((Z^m : ℝ) : ℂ)/(‖eisEmbedding (∏ i : activeSupport T U,p i.val)‖ : ℂ)) *
      ((moebius (∏ i ∈ E,Ideal.span {p i}) : ℂ)/
        (‖eisEmbedding (primeSubsetGenerator (fun i => Ideal.span {p i}) E)‖^2 : ℝ)) *
      (paperRadialFourier Φ (Z^m*‖eisEmbedding h‖^2/
        (‖eisEmbedding (primeSubsetGenerator (fun i => Ideal.span {p i}) E)‖^2 *
          ‖eisEmbedding (∏ i : activeSupport T U,p i.val)‖^2)) *
        activeGaussRowFactor p hp hinj hg T U
          (primeSubsetGenerator (fun i => Ideal.span {p i}) E) h) =
      initialPhysicalMode p hp hcop hg Ψ j σ V Φ Z D m G U T E h := by
  rw [initial_overlap_weight]
  unfold initialPhysicalMode
  rw [←initial_pair_rays p hp hcop hg hinj hc hpr Ψ j _ h σ G U T hGU hGT hUT,
    initial_product_kernel p V Φ Z D m G U T E hGU hGT hUT h]
  simp only [sourceIdeal,FiniteGaussPhase.span_finset_prod]
  ring

theorem initial_input_physical
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (hc : ∀ i,ringChar (O ⧸ Ideal.span {p i})≠2)
    (hpr : ∀ i,goodLambda^2∣p i-1)
    (F : Finset ι) (Ψ : O →* ℂ) (j : O) (σ : Finset ι → ℂ)
    (V : ℝ → ℂ) (Φ : 𝓢(ℝ,ℂ)) {Z : ℝ} (hZ : 0<Z) (D m : ℝ) :
    (∑' u : O,Φ (‖eisEmbedding u‖^2/Z^m)*
      (‖((Z^(-D/2) : ℝ) : ℂ)*inputConjugateRow p hg F Ψ j 1 1
        (initialTest p σ V Z D) u‖^2 : ℝ)) =
    ∑ G ∈ F.powerset,∑ U ∈ (F\G).powerset,∑ T ∈ (F\G).powerset,
      if Disjoint U T then ∑ E ∈ G.powerset,∑' h : O,
        initialPhysicalMode p hp hcop hg Ψ j σ V Φ Z D m G U T E h else 0 := by
  have hn := norm_rpow_half_sq hZ D
  simp only [norm_mul,mul_pow,hn,Complex.ofReal_mul]
  have hs : (∑' u : O,Φ (‖eisEmbedding u‖^2/Z^m)*
      (((Z^(-D) : ℝ) : ℂ)*(‖inputConjugateRow p hg F Ψ j 1 1
        (initialTest p σ V Z D) u‖^2 : ℝ))) =
      ((Z^(-D) : ℝ) : ℂ)*(∑' u : O,Φ (‖eisEmbedding u‖^2/Z^m)*
        (‖inputConjugateRow p hg F Ψ j 1 1 (initialTest p σ V Z D) u‖^2 : ℝ)) := by
    rw [←tsum_mul_left]
    apply tsum_congr
    intro u
    ring
  rw [hs,inputConjugateRow_smoothed_second_poisson p hg hp hinj hc F Ψ j 1 1
    (initialTest p σ V Z D) Φ (Z^m) (Real.rpow_pos_of_pos hZ m)]
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro G hG
  apply Finset.sum_congr rfl
  intro U hU
  apply Finset.sum_congr rfl
  intro T hT
  by_cases hUT : Disjoint U T
  · simp only [hUT,ite_true]
    have hGU : Disjoint G U := Finset.disjoint_of_subset_right
      (Finset.mem_powerset.mp hU) disjoint_sdiff_self_right
    have hGT : Disjoint G T := Finset.disjoint_of_subset_right
      (Finset.mem_powerset.mp hT) disjoint_sdiff_self_right
    unfold maskedSecondDual
    simp only [Finset.mul_sum,←tsum_mul_left]
    apply Finset.sum_congr rfl
    intro E hE
    apply tsum_congr
    intro h
    convert normalized_overlap_mode p hp hcop hg hinj hc hpr Ψ j σ V Φ
      Z D m G U T E hGU hGT hUT h using 1
    ring
  · simp only [hUT,ite_false,mul_zero]

theorem initialPhysicalMode_summable
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (hc : ∀ i,ringChar (O ⧸ Ideal.span {p i})≠2)
    (hpr : ∀ i,goodLambda^2∣p i-1)
    (Ψ : O →* ℂ) (j : O) (σ : Finset ι → ℂ)
    (V : ℝ → ℂ) (Φ : 𝓢(ℝ,ℂ)) {Z : ℝ} (hZ : 0<Z) (D m : ℝ)
    (G U T E : Finset ι) (hGU : Disjoint G U) (hGT : Disjoint G T)
    (hUT : Disjoint U T) :
    Summable (initialPhysicalMode p hp hcop hg Ψ j σ V Φ Z D m G U T E) := by
  have hs := secondPairRadialMode_summable p hp hg hinj U T
    (primeSubsetGenerator (fun i => Ideal.span {p i}) E) (primeSubsetGenerator_ne_zero _ _)
    Φ (Z^m) (Real.rpow_pos_of_pos hZ m)
  have hs' := (hs.mul_left ((moebius (∏ i ∈ E,Ideal.span {p i}) : ℂ)/
    (‖eisEmbedding (primeSubsetGenerator (fun i => Ideal.span {p i}) E)‖^2 : ℝ))).mul_left
    (((Z^(-D) : ℝ) : ℂ)*overlapPairWeight p hg Ψ j 1 1 (initialTest p σ V Z D) G U T)
  apply hs'.congr
  intro h
  rw [←normalized_overlap_mode p hp hcop hg hinj hc hpr Ψ j σ V Φ
    Z D m G U T E hGU hGT hUT h]
  unfold secondPairRadialMode
  ring

theorem initialPhysicalMode_zero_split
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (hc : ∀ i,ringChar (O ⧸ Ideal.span {p i})≠2)
    (hpr : ∀ i,goodLambda^2∣p i-1)
    (Ψ : O →* ℂ) (j : O) (σ : Finset ι → ℂ)
    (V : ℝ → ℂ) (Φ : 𝓢(ℝ,ℂ)) {Z : ℝ} (hZ : 0<Z) (D m : ℝ)
    (G U T E : Finset ι) (hGU : Disjoint G U) (hGT : Disjoint G T)
    (hUT : Disjoint U T) :
    (∑' h : O,initialPhysicalMode p hp hcop hg Ψ j σ V Φ Z D m G U T E h) =
      initialPhysicalMode p hp hcop hg Ψ j σ V Φ Z D m G U T E 0 +
      ∑' h : O,if h=0 then 0 else
        initialPhysicalMode p hp hcop hg Ψ j σ V Φ Z D m G U T E h :=
  (initialPhysicalMode_summable p hp hcop hg hinj hc hpr Ψ j σ V Φ hZ D m
    G U T E hGU hGT hUT).tsum_eq_add_tsum_ite 0

end RayModes

theorem poolPrimary_norm (F : Finset (Ideal O)) (hF : ∀ I ∈ F,Admissible I)
    (A : Finset (primePool F)) :
    FirstPassCubeLabels.primeProductNorm (poolPrimary F) A = (Ideal.absNorm (∏ i ∈ A,i.val) : ℝ) := by
  unfold FirstPassCubeLabels.primeProductNorm
  rw [eisEmbedding_norm_sq_eq_absNorm_span,FiniteGaussPhase.span_finset_prod]
  simp only [poolPrimary_span F hF]

theorem reconstructedSelector_support (S : Finset (Ideal O)) (P j : Ideal O)
    (a : Ideal O → ℂ) (A : Finset (primePool (columns S P j)))
    (hA : reconstructedSelector S P j a A≠0) : (∏ i ∈ A,i.val)∈columns S P j := by
  by_contra h
  exact hA (by simp only [reconstructedSelector,h,ite_false])

theorem reconstructedSelector_original (S : Finset (Ideal O)) {P j : Ideal O}
    (hP : Squarefree P) (hj : j∣P) (a : Ideal O → ℂ)
    (A : Finset (primePool (columns S P j)))
    (hA : reconstructedSelector S P j a A≠0) :
    Squarefree (∏ i ∈ A,i.val) ∧ IsCoprime (∏ i ∈ A,i.val) j ∧
      residual P j ∣ (∏ i ∈ A,i.val) ∧ reconstruct P j (∏ i ∈ A,i.val)∈S :=
  (mem_columns hP hj).mp (reconstructedSelector_support S P j a A hA)

theorem reconstructedSelector_empty (S : Finset (Ideal O)) (P j : Ideal O)
    (a : Ideal O → ℂ) (h : columns S P j=∅) (A : Finset (primePool (columns S P j))) :
    reconstructedSelector S P j a A=0 := by simp only [reconstructedSelector,h,Finset.notMem_empty,ite_false]

theorem residual_empty (S : Finset (Ideal O)) (P j : Ideal O)
    (η : Ideal O →* ℂ) (a : Ideal O → ℂ) (W : ℝ → ℂ) (Z r z G : ℝ)
    (h : columns S P j=∅) (u : O) :
    residualNormalizedPolynomial S P j η a W Z r z G u=0 := by
  simp only [residualNormalizedPolynomial,h,Finset.sum_empty,mul_zero]

theorem residual_eq_initialTest (S : Finset (Ideal O)) {P j : Ideal O}
    (hP : Admissible P) (hj : j∣P)
    (hS : ∀ n∈S,Squarefree n → Supported n)
    (η : Ideal O →* ℂ) (a : Ideal O → ℂ) (W : ℝ → ℂ) (Z r z G : ℝ) (u : O) :
    let F := columns S P j
    let hF : ∀ I∈F,Admissible I := fun I hI => columns_admissible S hP hj hS hI
    letI : ∀ i : primePool F,(Ideal.span {poolPrimary F i}).IsMaximal :=
      fun i => by rw [poolPrimary_span F hF i]; infer_instance
    residualNormalizedPolynomial S P j η a W Z r z G u =
      ((Z^(-(r+z-2*G)/2) : ℝ) : ℂ)*inputConjugateRow (poolPrimary F)
        (poolPrimary_good F hF) Finset.univ (elementCharacter η) (primaryGenerator j) 1 1
        (initialTest (poolPrimary F) (reconstructedSelector S P j a)
          (residualOverlapWindow P j W Z z G) Z (r+z-2*G)) u := by
  intro F hF
  let : ∀ i : primePool F,(Ideal.span {poolPrimary F i}).IsMaximal :=
    fun i => by rw [poolPrimary_span F hF i]; infer_instance
  rw [residual_eq_input S hP hj hS η a W Z r z G u]
  congr 2
  funext A
  simp only [initialTest,poolPrimary_norm F hF]
  rfl

theorem residual_initial_physical_rays (S : Finset (Ideal O)) {P j : Ideal O}
    (hP : Admissible P) (hj : j∣P)
    (hS : ∀ n∈S,Squarefree n → Supported n)
    (η : Ideal O →* ℂ) (a : Ideal O → ℂ) (W : ℝ → ℂ) {Z : ℝ} (hZ : 0<Z)
    (r z G m : ℝ) (Φ : 𝓢(ℝ,ℂ)) :
    let F := columns S P j
    let hF : ∀ I∈F,Admissible I := fun I hI => columns_admissible S hP hj hS hI
    letI : ∀ i : primePool F,(Ideal.span {poolPrimary F i}).IsMaximal :=
      fun i => by rw [poolPrimary_span F hF i]; infer_instance
    (∑' u : O,Φ (‖eisEmbedding u‖^2/Z^m)*
      (‖residualNormalizedPolynomial S P j η a W Z r z G u‖^2 : ℝ)) =
    ∑ C ∈ (Finset.univ : Finset (primePool F)).powerset,
      ∑ U ∈ (Finset.univ\C).powerset,∑ T ∈ (Finset.univ\C).powerset,
        if Disjoint U T then ∑ E ∈ C.powerset,∑' h : O,
          initialPhysicalMode (poolPrimary F) (poolPrimary_ne_zero F hF) (poolPrimary_coprime F hF)
            (poolPrimary_good F hF) (elementCharacter η) (primaryGenerator j)
            (reconstructedSelector S P j a) (residualOverlapWindow P j W Z z G)
            Φ Z (r+z-2*G) m C U T E h else 0 := by
  intro F hF
  let : ∀ i : primePool F,(Ideal.span {poolPrimary F i}).IsMaximal :=
    fun i => by rw [poolPrimary_span F hF i]; infer_instance
  simp_rw [residual_eq_initialTest S hP hj hS η a W Z r z G]
  exact initial_input_physical (poolPrimary F) (poolPrimary_ne_zero F hF)
    (poolPrimary_coprime F hF) (poolPrimary_good F hF) (poolPrimary_injective F hF)
    (poolPrimary_odd F hF) (poolPrimary_primary F hF) Finset.univ (elementCharacter η)
    (primaryGenerator j) (reconstructedSelector S P j a) (residualOverlapWindow P j W Z z G)
    Φ hZ (r+z-2*G) m

theorem idealPair_product_transport (F : Finset (Ideal O))
    (hF : ∀ I∈F,Admissible I) (I J : Ideal O) (Φ : 𝓢(ℝ,ℂ)) (Y : ℝ) :
    letI : ∀ i : primePool F,(Ideal.span {poolPrimary F i}).IsMaximal :=
      fun i => by rw [poolPrimary_span F hF i]; infer_instance
    idealPairPoissonKernel F (pool_positive F hF) (pool_good F hF) I J Φ Y =
      GaussGeneratorTransport.squarefreePairProductPoissonKernel (poolPrimary F)
        (poolPrimary_ne_zero F hF) (poolPrimary_injective F hF) (poolPrimary_good F hF)
        (idealSupport F I) (idealSupport F J) Φ Y := by
  let : ∀ i : primePool F,(Ideal.span {poolPrimary F i}).IsMaximal :=
    fun i => by rw [poolPrimary_span F hF i]; infer_instance
  have he : (fun i : primePool F => Ideal.span {poolPrimary F i}) =
      (fun i : primePool F => i.val) := funext (poolPrimary_span F hF)
  have ht := GaussGeneratorTransport.squarefreePairPoissonKernel_eq_product
    (poolPrimary F) (poolPrimary_ne_zero F hF) (poolPrimary_injective F hF)
    (poolPrimary_good F hF) (idealSupport F I) (idealSupport F J) Φ Y
  simpa only [he,idealPairPoissonKernel] using ht

end SevenEighths.InverseInitialRayAttachment

end

end OAI
