import OAI.NumberTheory.DirichletL.Inversion.InitialPoissonBridge
import OAI.NumberTheory.DirichletL.Inversion.InitialProfile
import OAI.NumberTheory.DirichletL.Inversion.InitialArithmetic

namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap ContDiff
open ActualEisensteinCubic ConcretePrimeRowBridge ConcreteTraceCRT
open EisensteinSchwartzPoisson UniqueFactorizationMonoid CanonicalQuadraticSieve
open SevenEighths.InverseInitialPoissonBridge SevenEighths.InverseInitialOverlap
open SevenEighths.InverseInitialProfile
namespace SevenEighths.InverseInitialKernelBridge

local notation "Eis" => ActualEisensteinCubic.O
local notation "N" => fun I : Ideal Eis => (Ideal.absNorm I : ℝ)
variable {ι : Type*} [DecidableEq ι] (P : ι → Ideal Eis)
  [∀ i, (P i).IsMaximal] (hinj : Function.Injective P)
  (hg : ∀ i, goodLambda ∉ P i)

def pairRow (S T : Finset ι) (h : Eis) : ℂ :=
  finiteSexticRow (activePrimes P S T) (fun i => hg i.val) (activeExponent S T) h

def pairGauss (S T : Finset ι) : ℂ :=
  canonicalNormalizedGauss (activePrimes P S T)
    (activePrimes_pairwise_isCoprime P hinj S T) (fun i => hg i.val) (activeExponent S T)

def pairCoordinates (S T E : Finset ι) (h : Eis) : Fin 6 → ℝ :=
  ![N (∏ i ∈ S∩T,P i), N (∏ i ∈ E,P i), 1, ‖eisEmbedding h‖^2,
    N (∏ i ∈ S\T,P i), N (∏ i ∈ T\S,P i)]

omit [∀ i, (P i).IsMaximal] in
theorem common_left_product (S T : Finset ι) :
    (∏ i ∈ S∩T,P i)*(∏ i ∈ S\T,P i) = ∏ i ∈ S,P i := by
  rw [mul_comm,←Finset.prod_union (Finset.disjoint_sdiff_inter S T),Finset.sdiff_union_inter]

omit [∀ i, (P i).IsMaximal] in
theorem common_right_product (S T : Finset ι) :
    (∏ i ∈ S∩T,P i)*(∏ i ∈ T\S,P i) = ∏ i ∈ T,P i := by
  simpa only [Finset.inter_comm] using common_left_product P T S

omit [∀ i, (P i).IsMaximal] in
theorem conductor_norm (S T : Finset ι) :
    ‖eisEmbedding (finitePrimeModulus (activePrimes P S T))‖ =
      Real.sqrt (N (∏ i ∈ S\T,P i)*N (∏ i ∈ T\S,P i)) := by
  have hn := activePrimeModulus_norm_sq P S T
  have hd : Disjoint (S\T) (T\S) := by
    apply Finset.disjoint_left.mpr
    intro i hi hj
    exact (Finset.mem_sdiff.mp hi).2 (Finset.mem_sdiff.mp hj).1
  simp only [activeSupport,Finset.prod_union hd,map_mul,Nat.cast_mul] at hn
  rw [←hn,Real.sqrt_sq_eq_abs,abs_of_nonneg (norm_nonneg _)]
  rfl

def pairArithmetic (S T E : Finset ι) (h : Eis) : ℂ :=
  pairGauss P hinj hg S T * (moebius (∏ i ∈ E,P i) : ℂ) *
    pairRow P hg S T (primeSubsetGenerator P E) * star (pairRow P hg S T h)

def pairMode (S T E : Finset ι) (Φ : 𝓢(ℝ,ℂ)) (Y : ℝ) (h : Eis) : ℂ :=
  ((Y : ℂ)*pairGauss P hinj hg S T /
    (‖eisEmbedding (finitePrimeModulus (activePrimes P S T))‖ : ℂ)) *
    (((moebius (∏ i ∈ E,P i) : ℂ)*pairRow P hg S T (primeSubsetGenerator P E) /
      (‖eisEmbedding (primeSubsetGenerator P E)‖^2 : ℝ)) *
      (star (pairRow P hg S T h)*paperRadialFourier Φ
        (Y*‖eisEmbedding h‖^2/(‖eisEmbedding (primeSubsetGenerator P E)‖^2 *
          ‖eisEmbedding (finitePrimeModulus (activePrimes P S T))‖^2))))

theorem pairKernel_eq_modes (S T : Finset ι) (Φ : 𝓢(ℝ,ℂ)) (Y : ℝ) :
    squarefreePairPoissonKernel P hinj hg S T Φ Y =
      ∑ E ∈ (S∩T).powerset, ∑' h : Eis, pairMode P hinj hg S T E Φ Y h := by
  simp only [squarefreePairPoissonKernel,pairMode,pairGauss,pairRow,
    tsum_mul_left,Finset.mul_sum]

private theorem physicalKernel_vector (W₁ W₂ : ℝ → ℂ) (Φ : 𝓢(ℝ,ℂ))
    (Z D m q₀ q₁ q₂ q₃ q₄ q₅ : ℝ) :
    physicalKernel W₁ W₂ Φ Z D m ![q₀,q₁,q₂,q₃,q₄,q₅] =
      ((Z^(-D)*Z^m/(q₁*q₂*Real.sqrt (q₄*q₅)) : ℝ) : ℂ)*
        W₁ (q₀*q₂*q₄/Z^D)*W₂ (q₀*q₂*q₅/Z^D)*
          paperRadialFourier Φ (Z^m*q₃/(q₁*q₂^2*q₄*q₅)) := rfl

theorem pairMode_physical (S T E : Finset ι) (Φ : 𝓢(ℝ,ℂ))
    (W₁ W₂ : ℝ → ℂ) (Z D m : ℝ) (h : Eis) :
    (Z^(-D) : ℝ)*W₁ (N (∏ i ∈ S,P i)/Z^D)*W₂ (N (∏ i ∈ T,P i)/Z^D)*
      pairMode P hinj hg S T E Φ (Z^m) h =
    pairArithmetic P hinj hg S T E h *
      physicalKernel W₁ W₂ Φ Z D m (pairCoordinates P S T E h) := by
  have hs := congrArg N (common_left_product P S T)
  have ht := congrArg N (common_right_product P S T)
  simp only [map_mul,Nat.cast_mul] at hs ht
  have hc := conductor_norm P S T
  have hc2 := congrArg (fun x : ℝ => x^2) hc
  rw [Real.sq_sqrt (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))] at hc2
  unfold pairMode pairArithmetic pairCoordinates
  rw [physicalKernel_vector]
  simp only [mul_one,one_pow,primeSubsetGenerator_norm_sq,hc2]
  rw [hc,hs,ht]
  push_cast
  ring_nf

theorem pairKernel_physical (S T : Finset ι) (Φ : 𝓢(ℝ,ℂ))
    (W₁ W₂ : ℝ → ℂ) (Z D m : ℝ) :
    (Z^(-D) : ℝ)*W₁ (N (∏ i ∈ S,P i)/Z^D)*W₂ (N (∏ i ∈ T,P i)/Z^D)*
      squarefreePairPoissonKernel P hinj hg S T Φ (Z^m) =
    ∑ E ∈ (S∩T).powerset, ∑' h : Eis,
      pairArithmetic P hinj hg S T E h *
        physicalKernel W₁ W₂ Φ Z D m (pairCoordinates P S T E h) := by
  rw [pairKernel_eq_modes]
  simp only [Finset.mul_sum,←tsum_mul_left]
  apply Finset.sum_congr rfl
  intro E hE
  apply tsum_congr
  intro h
  exact pairMode_physical P hinj hg S T E Φ W₁ W₂ Z D m h

def idealPhysicalPair (F : Finset (Ideal Eis)) (hFpos : ∀ I ∈ F, I ≠ ⊥)
    (hFgood : ∀ I ∈ F, ∀ Q ∈ normalizedFactors I, goodLambda ∉ Q)
    (I J : Ideal Eis) (Φ : 𝓢(ℝ,ℂ)) (W₁ W₂ : ℝ → ℂ) (Z D m : ℝ) : ℂ := by
  letI : ∀ q : primePool F, q.val.IsMaximal := primePool_maximal F hFpos
  exact ∑ E ∈ (idealSupport F I ∩ idealSupport F J).powerset, ∑' h : Eis,
    pairArithmetic (fun q : primePool F => q.val) Subtype.val_injective
      (primePool_good F hFgood) (idealSupport F I) (idealSupport F J) E h *
      physicalKernel W₁ W₂ Φ Z D m
        (pairCoordinates (fun q : primePool F => q.val) (idealSupport F I) (idealSupport F J) E h)

theorem ideal_conductor_norm_sq (F : Finset (Ideal Eis)) {I J : Ideal Eis}
    (hI : I ∈ F) (hJ : J ∈ F) (hsI : Squarefree I) (hsJ : Squarefree J) :
    ‖eisEmbedding (finitePrimeModulus (activePrimes (fun q : primePool F => q.val)
      (idealSupport F I) (idealSupport F J)))‖^2 *
        (N (primeSubsetProduct F (idealSupport F I∩idealSupport F J)))^2 = N I*N J :=
  idealPairPoisson_conductor_norm_sq F hI hJ hsI hsJ

theorem idealPairKernel_physical (F : Finset (Ideal Eis)) (hFpos : ∀ I ∈ F, I ≠ ⊥)
    (hFgood : ∀ I ∈ F, ∀ Q ∈ normalizedFactors I, goodLambda ∉ Q)
    {I J : Ideal Eis} (hI : I ∈ F) (hJ : J ∈ F) (hsI : Squarefree I) (hsJ : Squarefree J)
    (Φ : 𝓢(ℝ,ℂ)) (W₁ W₂ : ℝ → ℂ) (Z D m : ℝ) :
    (Z^(-D) : ℝ)*W₁ (N I/Z^D)*W₂ (N J/Z^D)*
      idealPairPoissonKernel F hFpos hFgood I J Φ (Z^m) =
      idealPhysicalPair F hFpos hFgood I J Φ W₁ W₂ Z D m := by
  let : ∀ q : primePool F, q.val.IsMaximal := primePool_maximal F hFpos
  simpa only [idealPairPoissonKernel,idealPhysicalPair,
    idealSupport_product_eq F hI hsI,idealSupport_product_eq F hJ hsJ] using
    pairKernel_physical (fun q : primePool F => q.val) Subtype.val_injective
      (primePool_good F hFgood) (idealSupport F I) (idealSupport F J) Φ W₁ W₂ Z D m

def bareOverlapCoefficient (P j : Ideal Eis) (η : Ideal Eis →* ℂ)
    (a : Ideal Eis → ℂ) (c : Ideal Eis) : ℂ :=
  (moebius c : ℂ)*η c*a (reconstruct P j c)

def maskedOverlapWindow (P j : Ideal Eis) (W : ℝ → ℂ) (Z z G : ℝ) (x : ℝ) : ℂ :=
  W ((x/Z^G)/((N (residual P j))/Z^(z-G)))

def residualOverlapWindow (P j : Ideal Eis) (W : ℝ → ℂ) (Z z G : ℝ) (x : ℝ) : ℂ :=
  W (((N j/Z^G)*x)/((N (residual P j))/Z^(z-G)))

theorem overlapCoefficient_masked (P j c : Ideal Eis) (η : Ideal Eis →* ℂ)
    (a : Ideal Eis → ℂ) (W : ℝ → ℂ) (Z r z G : ℝ) :
    overlapResidualCoefficient P j η a W Z r z G c =
      bareOverlapCoefficient P j η a c *
        maskedOverlapWindow P j W Z z G (N (j*c)/Z^(r+z-2*G)) := by
  unfold overlapResidualCoefficient bareOverlapCoefficient maskedOverlapWindow
  simp only [map_mul,Nat.cast_mul]
  congr 2
  ring_nf

theorem overlapCoefficient_residual (P j c : Ideal Eis) (η : Ideal Eis →* ℂ)
    (a : Ideal Eis → ℂ) (W : ℝ → ℂ) (Z r z G : ℝ) :
    overlapResidualCoefficient P j η a W Z r z G c =
      bareOverlapCoefficient P j η a c *
        residualOverlapWindow P j W Z z G (N c/Z^(r+z-2*G)) := rfl

theorem original_fixed_overlap_physical
    (S : Finset (Ideal Eis)) {P j : Ideal Eis} (hP : Admissible P) (hj : j ∣ P)
    (hS : ∀ n ∈ S, Squarefree n → Supported n) (η : Ideal Eis →* ℂ)
    (a : Ideal Eis → ℂ) (W : ℝ → ℂ) {Z : ℝ} (hZ : 0 < Z) (r z G m : ℝ)
    (Φ : 𝓢(ℝ,ℂ)) :
    let C := columns S P j
    let F := C.image (fun c => j*c)
    let hF : ∀ I ∈ F, Admissible I := fun I hI => by
      obtain ⟨c,hc,rfl⟩ := Finset.mem_image.mp hI
      exact masked_columns_admissible S hP hj hS hc
    let b := bareOverlapCoefficient P j η a
    let V := maskedOverlapWindow P j W Z z G
    (∑' u : Eis, Φ (‖eisEmbedding u‖^2/Z^m)*
      (‖originalFixedPolynomial S P j η a W Z r z u‖^2 : ℝ)) =
      ((Z^(-2*G)*‖η j‖^4 : ℝ) : ℂ)*
        ∑ c ∈ C, ∑ d ∈ C, (star (b c)*b d)*
          idealPhysicalPair F (pool_positive F hF) (pool_good F hF) (j*c) (j*d)
            Φ (fun x => star (V x)) V Z (r+z-2*G) m := by
  intro C F hF b V
  rw [original_fixed_overlap_smoothed_poisson S hP hj hS η a W hZ r z G Φ
    (Z^m) (Real.rpow_pos_of_pos hZ m)]
  have he : Z^(-2*G-(r+z-2*G)) = Z^(-2*G)*Z^(-(r+z-2*G)) := by
    rw [←Real.rpow_add hZ]
    congr 1
  rw [he]
  simp only [Complex.ofReal_mul]
  rw [show ((Z^(-2*G):ℝ):ℂ)*((Z^(-(r+z-2*G)):ℝ):ℂ)*↑(‖η j‖^4) =
    (((Z^(-2*G):ℝ):ℂ)*↑(‖η j‖^4))*((Z^(-(r+z-2*G)):ℝ):ℂ) from by ring_nf,mul_assoc]
  congr 1
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro c hc
  apply Finset.sum_congr rfl
  intro d hd
  have hcF : j*c ∈ F := Finset.mem_image.mpr ⟨c,hc,rfl⟩
  have hdF : j*d ∈ F := Finset.mem_image.mpr ⟨d,hd,rfl⟩
  have hker := idealPairKernel_physical F (pool_positive F hF) (pool_good F hF)
    hcF hdF (hF _ hcF).2.1 (hF _ hdF).2.1 Φ (fun x => star (V x)) V Z (r+z-2*G) m
  rw [overlapCoefficient_masked,overlapCoefficient_masked]
  simp only [star_mul]
  dsimp only [b,V,F,C] at hker ⊢
  rw [←hker]
  ring_nf

theorem residual_normalized_physical
    (S : Finset (Ideal Eis)) {P j : Ideal Eis} (hP : Admissible P) (hj : j ∣ P)
    (hS : ∀ n ∈ S, Squarefree n → Supported n) (η : Ideal Eis →* ℂ)
    (a : Ideal Eis → ℂ) (W : ℝ → ℂ) {Z : ℝ} (hZ : 0 < Z) (r z G m : ℝ)
    (Φ : 𝓢(ℝ,ℂ)) :
    let C := columns S P j
    let F := C.image (fun c => c)
    let hF : ∀ I ∈ F, Admissible I := fun I hI => by
      obtain ⟨c,hc,rfl⟩ := Finset.mem_image.mp hI
      exact columns_admissible S hP hj hS hc
    let b := bareOverlapCoefficient P j η a
    let V := residualOverlapWindow P j W Z z G
    (∑' u : Eis, Φ (‖eisEmbedding u‖^2/Z^m)*
      (‖residualNormalizedPolynomial S P j η a W Z r z G u‖^2 : ℝ)) =
        ∑ c ∈ C, ∑ d ∈ C, (b c*star (b d))*
          idealPhysicalPair F (pool_positive F hF) (pool_good F hF) c d
            Φ V (fun x => star (V x)) Z (r+z-2*G) m := by
  intro C F hF b V
  rw [residual_normalized_smoothed_poisson S hP hj hS η a W hZ r z G Φ
    (Z^m) (Real.rpow_pos_of_pos hZ m)]
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro c hc
  apply Finset.sum_congr rfl
  intro d hd
  have hcF : c ∈ F := Finset.mem_image.mpr ⟨c,hc,rfl⟩
  have hdF : d ∈ F := Finset.mem_image.mpr ⟨d,hd,rfl⟩
  have hker := idealPairKernel_physical F (pool_positive F hF) (pool_good F hF)
    hcF hdF (hF _ hcF).2.1 (hF _ hdF).2.1 Φ V (fun x => star (V x)) Z (r+z-2*G) m
  rw [overlapCoefficient_residual,overlapCoefficient_residual]
  simp only [star_mul]
  dsimp only [b,V,F,C] at hker ⊢
  rw [←hker]
  ring_nf

def physicalCoordinates (C d s n₁ n₂ : Ideal Eis) (h : Eis) : Fin 6 → ℝ :=
  ![N C,N d,N s,‖eisEmbedding h‖^2,N n₁,N n₂]

theorem physicalCoordinates_pos (C d s n₁ n₂ : Ideal Eis) (h : Eis)
    (hC : C ≠ 0) (hd : d ≠ 0) (hs : s ≠ 0) (h₁ : n₁ ≠ 0) (h₂ : n₂ ≠ 0) (hh : h ≠ 0) :
    ∀ i, 0 < physicalCoordinates C d s n₁ n₂ h i := by
  have hp (I : Ideal Eis) (hI : I ≠ 0) : 0 < N I := by
    change 0 < (Ideal.absNorm I : ℝ)
    exact_mod_cast Nat.pos_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr hI)
  intro i
  fin_cases i
  · exact hp C hC
  · exact hp d hd
  · exact hp s hs
  · exact sq_pos_of_pos (norm_pos_iff.mpr (eisEmbedding_ne_zero hh))
  · exact hp n₁ h₁
  · exact hp n₂ h₂

theorem physicalKernel_common_factor (C d s n₁ n₂ : Ideal Eis) (h : Eis)
    (W₁ W₂ : ℝ → ℂ) (Φ : 𝓢(ℝ,ℂ)) (Z D m : ℝ) :
    physicalKernel W₁ W₂ Φ Z D m (physicalCoordinates C d 1 (s*n₁) (s*n₂) h) =
      physicalKernel W₁ W₂ Φ Z D m (physicalCoordinates C d s n₁ n₂ h) := by
  have hroot : Real.sqrt ((N s*N n₁)*(N s*N n₂)) = N s*Real.sqrt (N n₁*N n₂) := by
    rw [show (N s*N n₁)*(N s*N n₂) = (N s)^2*(N n₁*N n₂) from by ring_nf,
      Real.sqrt_mul (sq_nonneg _),Real.sqrt_sq_eq_abs,abs_of_nonneg (Nat.cast_nonneg _)]
  unfold physicalCoordinates
  rw [physicalKernel_vector,physicalKernel_vector]
  simp only [map_one,Nat.cast_one,map_mul,Nat.cast_mul,mul_one,one_pow]
  rw [hroot]
  have hl : N C*(N s*N n₁)/Z^D = N C*N s*N n₁/Z^D := by ring_nf
  have hr : N C*(N s*N n₂)/Z^D = N C*N s*N n₂/Z^D := by ring_nf
  have hk : Z^m*‖eisEmbedding h‖^2/(N d*(N s*N n₁)*(N s*N n₂)) =
      Z^m*‖eisEmbedding h‖^2/(N d*(N s)^2*N n₁*N n₂) := by ring_nf
  rw [hl,hr,hk]
  push_cast
  ring_nf

omit [∀ i, (P i).IsMaximal] in

theorem pairCoordinates_eq (S T E : Finset ι) (h : Eis) :
    pairCoordinates P S T E h = physicalCoordinates
      (∏ i ∈ S∩T,P i) (∏ i ∈ E,P i) 1 (∏ i ∈ S\T,P i) (∏ i ∈ T\S,P i) h := by
  simp only [pairCoordinates,physicalCoordinates,map_one,Nat.cast_one]

theorem pairArithmetic_residual_rows (S T E : Finset ι) (h : Eis) :
    pairArithmetic P hinj hg S T E h =
      pairGauss P hinj hg S T * (moebius (∏ i ∈ E,P i) : ℂ) *
        (star (finiteSquarefreeRow P hg (S\T) (primeSubsetGenerator P E)) *
          finiteSquarefreeRow P hg (T\S) (primeSubsetGenerator P E)) *
        (finiteSquarefreeRow P hg (S\T) h * star (finiteSquarefreeRow P hg (T\S) h)) := by
  have he (u : Eis) : pairRow P hg S T u =
      star (finiteSquarefreeRow P hg (S\T) u)*finiteSquarefreeRow P hg (T\S) u :=
    finiteSexticRow_activeSupport P hg S T u
  simp only [pairArithmetic,he,star_mul,star_star]
  ring_nf

theorem pairMode_summable (S T E : Finset ι) (Φ : 𝓢(ℝ,ℂ)) (Y : ℝ) (hY : 0 < Y) :
    Summable (pairMode P hinj hg S T E Φ Y) := by
  let den := ‖eisEmbedding (primeSubsetGenerator P E)‖^2 *
    ‖eisEmbedding (finitePrimeModulus (activePrimes P S T))‖^2
  have hd : 0 < den := mul_pos
    (sq_pos_of_pos (norm_pos_iff.mpr (eisEmbedding_ne_zero (primeSubsetGenerator_ne_zero P E))))
    (sq_pos_of_pos (norm_pos_iff.mpr (eisEmbedding_ne_zero (finitePrimeModulus_ne_zero _))))
  have hs := activeRow_paperFourier_summable P hg S T Φ (Y/den) (div_pos hY hd)
  have he (h : Eis) : (Y/den)*‖eisEmbedding h‖^2 = Y*‖eisEmbedding h‖^2/den := by ring_nf
  simp_rw [he] at hs
  exact (hs.mul_left _).mul_left _

theorem pairMode_zero_split (S T E : Finset ι) (Φ : 𝓢(ℝ,ℂ)) (Y : ℝ) (hY : 0 < Y) :
    (∑' h : Eis, pairMode P hinj hg S T E Φ Y h) =
      pairMode P hinj hg S T E Φ Y 0 +
        ∑' h : Eis, if h=0 then 0 else pairMode P hinj hg S T E Φ Y h :=
  (pairMode_summable P hinj hg S T E Φ Y hY).tsum_eq_add_tsum_ite 0

theorem physicalMode_zero_split (S T E : Finset ι) (Φ : 𝓢(ℝ,ℂ))
    (W₁ W₂ : ℝ → ℂ) (Z D m : ℝ) (hZ : 0 < Z) :
    (∑' h : Eis, pairArithmetic P hinj hg S T E h *
      physicalKernel W₁ W₂ Φ Z D m (pairCoordinates P S T E h)) =
      pairArithmetic P hinj hg S T E 0 *
        physicalKernel W₁ W₂ Φ Z D m (pairCoordinates P S T E 0) +
      ∑' h : Eis, if h=0 then 0 else pairArithmetic P hinj hg S T E h *
        physicalKernel W₁ W₂ Φ Z D m (pairCoordinates P S T E h) := by
  have hs := (pairMode_summable P hinj hg S T E Φ (Z^m) (Real.rpow_pos_of_pos hZ m)).mul_left
    (((Z^(-D):ℝ):ℂ)*W₁ (N (∏ i ∈ S,P i)/Z^D)*W₂ (N (∏ i ∈ T,P i)/Z^D))
  have he := (funext fun h => pairMode_physical P hinj hg S T E Φ W₁ W₂ Z D m h)
  rw [he] at hs
  exact hs.tsum_eq_add_tsum_ite 0

open InverseInitialArithmetic SecondPassArithmetic

theorem common_extracted_physical_mode
    (p : ι → Eis) (hp : ∀ i,p i≠0) [∀ i,(Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hgood : ∀ i,goodLambda∉Ideal.span {p i})
    (hpr : ∀ i,goodLambda^2∣p i-1) (Ψ₁ Ψ₂ : Eis →* ℂ)
    (j t d h : Eis) (H₁ H₂ : Finset ι → ℂ) (V N₁ N₂ : Finset ι)
    (h₁ : Disjoint V N₁) (h₂ : Disjoint V N₂)
    (W₁ W₂ : ℝ → ℂ) (Φ : 𝓢(ℝ,ℂ)) (Z D m : ℝ) :
    star (initialColumn p hp hcop hgood Ψ₁ j (d*t) d h H₁ (V∪N₁)) *
      initialColumn p hp hcop hgood Ψ₂ j (d*t) d h H₂ (V∪N₂) *
      physicalKernel W₁ W₂ Φ Z D m
        (physicalCoordinates (Ideal.span {d*t}) (Ideal.span {d}) 1
          (sourceIdeal p (V∪N₁)) (sourceIdeal p (V∪N₂)) h) =
    (star (initialColumn p hp hcop hgood Ψ₁ j (d*t) d h (fun _=>1) V) *
      initialColumn p hp hcop hgood Ψ₂ j (d*t) d h (fun _=>1) V) *
      star (secondChildColumn p hp hcop hgood Ψ₁ (j*t) (d*∏ i∈V,p i) (d*h)
        (fun U=>H₁ (V∪U)) N₁) *
      secondChildColumn p hp hcop hgood Ψ₂ (j*t) (d*∏ i∈V,p i) (d*h)
        (fun U=>H₂ (V∪U)) N₂ *
      physicalKernel W₁ W₂ Φ Z D m
        (physicalCoordinates (Ideal.span {d*t}) (Ideal.span {d}) (sourceIdeal p V)
          (sourceIdeal p N₁) (sourceIdeal p N₂) h) := by
  rw [initial_common_extraction p hp hcop hgood hpr Ψ₁ j t d h H₁ V N₁ h₁,
    initial_common_extraction p hp hcop hgood hpr Ψ₂ j t d h H₂ V N₂ h₂,
    sourceIdeal_union p V N₁ h₁,sourceIdeal_union p V N₂ h₂,
    physicalKernel_common_factor]
  simp only [star_mul]
  ring_nf

omit [∀ i, (P i).IsMaximal] in

theorem pairDivisor_dvd_common (S T E : Finset ι) (hE : E ∈ (S∩T).powerset) :
    (∏ i ∈ E,P i) ∣ (∏ i ∈ S∩T,P i) :=
  Finset.prod_dvd_prod_of_subset E (S∩T) P (Finset.mem_powerset.mp hE)

omit [DecidableEq ι] [∀ i, (P i).IsMaximal] in
theorem pairDivisor_span (E : Finset ι) :
    Ideal.span {primeSubsetGenerator P E} = ∏ i ∈ E,P i :=
  span_idealGenerator _

theorem physicalCoordinates_frequency_ideal (C d s n₁ n₂ : Ideal Eis) (h : Eis) :
    physicalCoordinates C d s n₁ n₂ h =
      ![N C,N d,N s,N (Ideal.span {h}),N n₁,N n₂] := by
  simp only [physicalCoordinates,eisEmbedding_norm_sq_eq_absNorm_span]

end SevenEighths.InverseInitialKernelBridge

end

end OAI
