import OAI.NumberTheory.DirichletL.Inversion.InitialConjugateEnergy
import OAI.NumberTheory.DirichletL.Inversion.InitialClippedColumns

namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap FourierTransform ContDiff

namespace SevenEighths.InverseInitialPhysicalMeasure
open ActualEisensteinCubic CompletedGauss ConcretePrimeRowBridge ConcreteTraceCRT
open FirstPassCubeLabels FirstCauchyArithmetic SecondPassArithmetic
open InverseMoment InverseInitialArithmetic InverseInitialRayAttachment
open InverseInitialKernelBridge InverseInitialProfile InverseInitialClippedColumns
open MeasureTheory FourierBridge JointLogSeparation
local notation "O" => ActualEisensteinCubic.O

@[ext] structure Point (ι : Type*) where
  common : Finset ι
  divisor : Finset ι
  overlap : Finset ι
  left : Finset ι
  right : Finset ι
  frequency : O

variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) (hp : ∀ i,p i≠0) [∀ i,(Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
  (hg : ∀ i,goodLambda∉Ideal.span {p i})

def divisor (x : Point ι) : O := primeSubsetGenerator (fun i=>Ideal.span {p i}) x.divisor

def quotient (x : Point ι) : O := primaryGenerator (sourceIdeal p (x.common\x.divisor))

def coordinates (x : Point ι) : Fin 6 → ℝ :=
  physicalCoordinates (sourceIdeal p x.common) (sourceIdeal p x.divisor)
    (sourceIdeal p x.overlap) (sourceIdeal p x.left) (sourceIdeal p x.right) x.frequency

structure Valid (x : Point ι) : Prop where
  divisor_subset : x.divisor⊆x.common
  overlap_left : Disjoint x.overlap x.left
  overlap_right : Disjoint x.overlap x.right
  frequency_nonzero : x.frequency≠0

include hp in
omit [DecidableEq ι] [∀ i,(Ideal.span {p i}).IsMaximal] in
theorem coordinates_pos (x : Point ι) (hx : Valid x) : ∀ i,0<coordinates p x i :=
  physicalCoordinates_pos _ _ _ _ _ _ (sourceIdeal_ne_zero p hp _) (sourceIdeal_ne_zero p hp _)
    (sourceIdeal_ne_zero p hp _) (sourceIdeal_ne_zero p hp _) (sourceIdeal_ne_zero p hp _) hx.frequency_nonzero

omit [DecidableEq ι] [∀ i,(Ideal.span {p i}).IsMaximal] in
theorem divisor_span (x : Point ι) : Ideal.span {divisor p x}=sourceIdeal p x.divisor := by
  simpa only [divisor,sourceIdeal,FiniteGaussPhase.span_finset_prod] using
    pairDivisor_span (fun i=>Ideal.span {p i}) x.divisor

include hp in
omit [∀ i,(Ideal.span {p i}).IsMaximal] in
theorem quotient_span (hpr : ∀ i,goodLambda^2∣p i-1) (x : Point ι) :
    Ideal.span {quotient p x}=sourceIdeal p (x.common\x.divisor) := by
  rw [quotient,sourceIdeal_gen p hp hpr]
  rfl

include hp in
omit [∀ i,(Ideal.span {p i}).IsMaximal] in
theorem common_span (hpr : ∀ i,goodLambda^2∣p i-1) (x : Point ι) (hx : Valid x) :
    Ideal.span {divisor p x*quotient p x}=sourceIdeal p x.common := by
  rw [←Ideal.span_singleton_mul_span_singleton,divisor_span p,quotient_span p hp hpr,
    ←sourceIdeal_union p _ _ (Finset.disjoint_left.mpr (fun i hi hj => (Finset.mem_sdiff.mp hj).2 hi)),
    Finset.union_sdiff_of_subset hx.divisor_subset]

include hp in
def unitSector (hpr : ∀ i,goodLambda^2∣p i-1) (x : Point ι) : Oˣ :=
  Classical.choose (generator_eq_unit_primary (sourceIdeal p x.divisor) (divisor p x)
    (divisor_span p x) (by rw [sourceIdeal_gen p hp hpr]; exact Finset.prod_ne_zero_iff.mpr (fun i _=>hp i)))

include hp in
omit [∀ i,(Ideal.span {p i}).IsMaximal] in
theorem unitSector_spec (hpr : ∀ i,goodLambda^2∣p i-1) (x : Point ι) :
    divisor p x=(unitSector p hp hpr x:O)*primaryGenerator (sourceIdeal p x.divisor) :=
  Classical.choose_spec (generator_eq_unit_primary (sourceIdeal p x.divisor) (divisor p x)
    (divisor_span p x) (by rw [sourceIdeal_gen p hp hpr]; exact Finset.prod_ne_zero_iff.mpr (fun i _=>hp i)))

theorem child_normalized (hpr : ∀ i,goodLambda^2∣p i-1) (x : Point ι)
    (Ψ : O →* ℂ) (j h : O) (H : Finset ι→ℂ) (N : Finset ι) :
    secondChildColumn p hp hcop hg Ψ (j*quotient p x)
      (divisor p x*∏ i∈x.overlap,p i) (divisor p x*h) H N =
    secondChildColumn p hp hcop hg Ψ (j*quotient p x)
      (primaryGenerator (sourceIdeal p x.divisor*sourceIdeal p x.overlap))
      (primaryGenerator (sourceIdeal p x.divisor)*((unitSector p hp hpr x:O)^5*h)) H N := by
  obtain ⟨u,hu,he⟩ := initial_poisson_child_normalized p hp hcop hg hpr
    x.common x.divisor x.overlap Ψ j (divisor p x) (quotient p x) h
    (divisor_span p x) (quotient_span p hp hpr x)
  have hgen : primaryGenerator (sourceIdeal p x.divisor)≠0 := by
    rw [sourceIdeal_gen p hp hpr];exact Finset.prod_ne_zero_iff.mpr (fun i _=>hp i)
  have hu' : u=unitSector p hp hpr x := Units.val_injective
    (mul_right_cancel₀ hgen (hu.symm.trans (unitSector_spec p hp hpr x)))
  simpa only [hu',quotient] using he H N

include hp hcop hg in
theorem column_extraction (hpr : ∀ i,goodLambda^2∣p i-1)
    (x : Point ι) (hx : Valid x) (Ψ : O →* ℂ) (j h : O)
    (σ : Finset ι→ℂ) (N : Finset ι) (hN : Disjoint x.overlap N) :
    initialColumn p hp hcop hg Ψ j (∏ i∈x.common,p i) (divisor p x) h
      (fun A=>σ (x.common∪A)) (x.overlap∪N) =
      initialColumn p hp hcop hg Ψ j (∏ i∈x.common,p i) (divisor p x) h (fun _=>1) x.overlap *
      secondChildColumn p hp hcop hg Ψ (j*quotient p x)
        (primaryGenerator (sourceIdeal p x.divisor*sourceIdeal p x.overlap))
        (primaryGenerator (sourceIdeal p x.divisor)*((unitSector p hp hpr x:O)^5*h))
        (fun A=>σ (x.common∪(x.overlap∪A))) N := by
  have hm (A : Finset ι) :
      rowCoprimeMask (fun i=>Ideal.span {p i}) A (j*∏ i∈x.common,p i)=
      rowCoprimeMask (fun i=>Ideal.span {p i}) A (j*(divisor p x*quotient p x)) :=
    rowCoprimeMask_mul_eq_of_span_eq _ A j (common_span p hp hpr x hx).symm
  have hc (H : Finset ι→ℂ) (A : Finset ι) :
      initialColumn p hp hcop hg Ψ j (∏ i∈x.common,p i) (divisor p x) h H A =
      initialColumn p hp hcop hg Ψ j (divisor p x*quotient p x) (divisor p x) h H A := by
    simp only [initialColumn,hm]
  rw [hc,initial_common_extraction p hp hcop hg hpr Ψ j (quotient p x) (divisor p x) h _ _ _ hN,
    ←hc,child_normalized p hp hcop hg hpr]

def outerCoefficient (Ψ : O →* ℂ) (j : O) (x : Point ι) (ρ : SecondRayIndex) : ℂ :=
  initialBeta p Ψ j x.common * (UniqueFactorizationMonoid.moebius (sourceIdeal p x.divisor):ℂ) *
    supportMobius (fun i=>Ideal.span {p i}) x.overlap * secondRayCoefficient ρ *
    star (initialColumn p hp hcop hg (secondRayMinus Ψ ρ) j (∏ i∈x.common,p i)
      (divisor p x) x.frequency (fun _=>1) x.overlap) *
    initialColumn p hp hcop hg (secondRayPlus Ψ ρ) j (∏ i∈x.common,p i)
      (divisor p x) (-x.frequency) (fun _=>1) x.overlap

def canonicalColumn (hpr : ∀ i,goodLambda^2∣p i-1)
    (Ψ : O →* ℂ) (j : O) (σ : Finset ι→ℂ) (x : Point ι) (h : O)
    (H : Finset ι→ℂ) (N : Finset ι) : ℂ :=
  secondChildColumn p hp hcop hg Ψ (j*quotient p x)
    (primaryGenerator (sourceIdeal p x.divisor*sourceIdeal p x.overlap))
    (primaryGenerator (sourceIdeal p x.divisor)*((unitSector p hp hpr x:O)^5*h))
    (fun A=>σ (x.common∪(x.overlap∪A))*H A) N

def physicalTerm (Ψ : O →* ℂ) (j : O) (σ : Finset ι→ℂ)
    (W₁ W₂ : ℝ→ℂ) (Φ : 𝓢(ℝ,ℂ)) (Z D m : ℝ)
    (x : Point ι) (ρ : SecondRayIndex) : ℂ :=
  (initialBeta p Ψ j x.common * (UniqueFactorizationMonoid.moebius (sourceIdeal p x.divisor):ℂ) *
    supportMobius (fun i=>Ideal.span {p i}) x.overlap * secondRayCoefficient ρ) *
  star (initialColumn p hp hcop hg (secondRayMinus Ψ ρ) j (∏ i∈x.common,p i)
    (divisor p x) x.frequency (fun A=>σ (x.common∪A)) (x.overlap∪x.left)) *
  initialColumn p hp hcop hg (secondRayPlus Ψ ρ) j (∏ i∈x.common,p i)
    (divisor p x) (-x.frequency) (fun A=>σ (x.common∪A)) (x.overlap∪x.right) *
  physicalKernel W₁ W₂ Φ Z D m
    (physicalCoordinates (sourceIdeal p x.common) (sourceIdeal p x.divisor) 1
      (sourceIdeal p (x.overlap∪x.left)) (sourceIdeal p (x.overlap∪x.right)) x.frequency)

include hp hcop hg in
theorem physicalTerm_extracted (hpr : ∀ i,goodLambda^2∣p i-1)
    (Ψ : O →* ℂ) (j : O) (σ : Finset ι→ℂ)
    (W₁ W₂ : ℝ→ℂ) (Φ : 𝓢(ℝ,ℂ)) (Z D m : ℝ)
    (x : Point ι) (hx : Valid x) (ρ : SecondRayIndex) :
    physicalTerm p hp hcop hg Ψ j σ W₁ W₂ Φ Z D m x ρ =
      outerCoefficient p hp hcop hg Ψ j x ρ *
      star (canonicalColumn p hp hcop hg hpr (secondRayMinus Ψ ρ) j σ x x.frequency (fun _=>1) x.left) *
      canonicalColumn p hp hcop hg hpr (secondRayPlus Ψ ρ) j σ x (-x.frequency) (fun _=>1) x.right *
      physicalKernel W₁ W₂ Φ Z D m (coordinates p x) := by
  unfold physicalTerm
  rw [column_extraction p hp hcop hg hpr x hx _ _ _ σ _ hx.overlap_left,
    column_extraction p hp hcop hg hpr x hx _ _ _ σ _ hx.overlap_right,
    sourceIdeal_union p _ _ hx.overlap_left,sourceIdeal_union p _ _ hx.overlap_right,
    physicalKernel_common_factor]
  simp only [canonicalColumn,mul_one,star_mul,outerCoefficient,coordinates]
  ring

def barePair (hpr : ∀ i,goodLambda^2∣p i-1) (Ψ : O →* ℂ) (j : O)
    (σ : Finset ι→ℂ) (x : Point ι) (ρ : SecondRayIndex) : ℂ :=
  outerCoefficient p hp hcop hg Ψ j x ρ *
    star (canonicalColumn p hp hcop hg hpr (secondRayMinus Ψ ρ) j σ x x.frequency (fun _=>1) x.left) *
    canonicalColumn p hp hcop hg hpr (secondRayPlus Ψ ρ) j σ x (-x.frequency) (fun _=>1) x.right

def columnRatio (N : Finset ι) (Z D B v : ℝ) : ℝ :=
  (Ideal.absNorm (sourceIdeal p N):ℝ)/Z^(columnCenter D B v)

omit [DecidableEq ι] [∀ i,(Ideal.span {p i}).IsMaximal] in
theorem relative_column_left (x : Point ι) (Z D B v θ H : ℝ) :
    relativeNorm (coordinates p x) Z D B v θ H 4=columnRatio p x.left Z D B v := rfl

omit [DecidableEq ι] [∀ i,(Ideal.span {p i}).IsMaximal] in
theorem relative_column_right (x : Point ι) (Z D B v θ H : ℝ) :
    relativeNorm (coordinates p x) Z D B v θ H 5=columnRatio p x.right Z D B v := rfl

omit [DecidableEq ι] [∀ i,(Ideal.span {p i}).IsMaximal] in
theorem columnRatio_actual (N : Finset ι) (Z D B v : ℝ) :
    columnRatio p N Z D B v=primeProductNorm p N/Z^(columnCenter D B v) := by
  unfold columnRatio sourceIdeal primeProductNorm
  rw [←eisEmbedding_norm_sq_eq_absNorm_span]

def canonicalPairMode (hpr : ∀ i,goodLambda^2∣p i-1) (Ψ : O →* ℂ) (j : O)
    (σ : Finset ι→ℂ) (ω₁ ω₂ : ℝ→ℂ) (Z D B v θ H : ℝ)
    (x : Point ι) (ρ : SecondRayIndex) (z : Frequency × (Fin 6→ℝ)) : ℂ :=
  let height :=  profileHeight secondLeftSlope secondRightSlope secondKernelSlope z.1 z.2
  outerCoefficient p hp hcop hg Ψ j x ρ *
    secondOuterPhase height (relativeLog (coordinates p x) Z D B v θ H) *
    star (canonicalColumn p hp hcop hg hpr (secondRayMinus Ψ ρ) j σ x x.frequency
      (fun A=>childLogTest ω₁ (-height 4) (columnRatio p A Z D B v)) x.left) *
    canonicalColumn p hp hcop hg hpr (secondRayPlus Ψ ρ) j σ x (-x.frequency)
      (fun A=>childLogTest ω₂ (height 5) (columnRatio p A Z D B v)) x.right

theorem canonical_pair_mode (hpr : ∀ i,goodLambda^2∣p i-1) (Ψ : O →* ℂ) (j : O)
    (σ : Finset ι→ℂ) (ω₁ ω₂ : ℝ→ℂ) (Z D B v θ H : ℝ)
    (x : Point ι) (ρ : SecondRayIndex) (z : Frequency × (Fin 6→ℝ)) :
    barePair p hp hcop hg hpr Ψ j σ x ρ *
      (star (ω₁ (columnRatio p x.left Z D B v))*ω₂ (columnRatio p x.right Z D B v)) *
      pureProfileMode secondLeftSlope secondRightSlope secondKernelSlope
        (relativeLog (coordinates p x) Z D B v θ H) z.1 z.2 =
      canonicalPairMode p hp hcop hg hpr Ψ j σ ω₁ ω₂ Z D B v θ H x ρ z := by
  rw [second_mode_split]
  simp only [canonicalPairMode,barePair,canonicalColumn,secondChildColumn,childLogTest,
    star_mul,SecondPassIntegration.logPhase_conjugate,neg_neg,relativeLog,
    relative_column_left,relative_column_right,mul_one]
  ring

theorem family_density_finite_sum {κ : Type*} (s : Finset κ)
    (g : Fin 6→𝓢(ℝ,ℂ)) (g₁ g₂ b₃ : 𝓢(ℝ,ℂ)) (c₁ c₂ θ₁ θ₂ L : ℝ)
    (c : κ→ℂ) (y : κ→Fin 6→ℝ) :
    (∑ k∈s,c k*∫ z : Frequency × (Fin 6→ℝ),
      familyDensity g g₁ g₂ b₃ c₁ c₂ θ₁ θ₂ L z *
        pureProfileMode secondLeftSlope secondRightSlope secondKernelSlope (y k) z.1 z.2) =
    ∫ z : Frequency × (Fin 6→ℝ),familyDensity g g₁ g₂ b₃ c₁ c₂ θ₁ θ₂ L z *
      ∑ k∈s,c k*pureProfileMode secondLeftSlope secondRightSlope secondKernelSlope (y k) z.1 z.2 := by
  simp only [familyDensity,mul_assoc,integral_const_mul]
  have he := full_density_finite_sum s g (𝓕 (clippedTwist g₁ c₁ θ₁))
    (𝓕 (clippedTwist g₂ c₂ θ₂)) b₃ secondLeftSlope secondRightSlope secondKernelSlope c y
  calc
    _ = (Real.exp (-3*L):ℂ)*∑ k∈s,c k*∫ z : Frequency × (Fin 6→ℝ),
        fullProfileDensity g (𝓕 (clippedTwist g₁ c₁ θ₁)) (𝓕 (clippedTwist g₂ c₂ θ₂)) b₃ z *
          pureProfileMode secondLeftSlope secondRightSlope secondKernelSlope (y k) z.1 z.2 := by
      rw [Finset.mul_sum];apply Finset.sum_congr rfl;intro k hk;ring
    _ = _ := by rw [he]

def physicalBlock (source : Finset (Point ι)) (w : Point ι→ℂ)
    (Ψ : O →* ℂ) (j : O) (σ : Finset ι→ℂ)
    (W₁ W₂ : ℝ→ℂ) (Φ : 𝓢(ℝ,ℂ)) (Z D m : ℝ) : ℂ :=
  ∑ x∈source,∑ ρ : SecondRayIndex,w x*physicalTerm p hp hcop hg Ψ j σ W₁ W₂ Φ Z D m x ρ

def canonicalBlock (hpr : ∀ i,goodLambda^2∣p i-1)
    (source : Finset (Point ι)) (w : Point ι→ℂ) (Ψ : O →* ℂ) (j : O) (σ : Finset ι→ℂ)
    (ω₁ ω₂ : ℝ→ℂ) (Z D B v θ H : ℝ) (z : Frequency × (Fin 6→ℝ)) : ℂ :=
  ∑ x∈source,∑ ρ : SecondRayIndex,w x*canonicalPairMode p hp hcop hg hpr Ψ j σ ω₁ ω₂ Z D B v θ H x ρ z

theorem physicalBlock_integral
    (hpr : ∀ i,goodLambda^2∣p i-1)
    (W₁ W₂ : ℝ→ℂ) (Φ : 𝓢(ℝ,ℂ)) (V : Fin 6→ℝ→ℂ)
    (g : Fin 6→𝓢(ℝ,ℂ)) (g₁ g₂ b₃ : 𝓢(ℝ,ℂ))
    (Z D B v m θ H η c₁ c₂ θ₁ θ₂ : ℝ)
    (hid : PhysicalIdentityAt W₁ W₂ Φ V g g₁ g₂ b₃ Z D B v m θ H η c₁ c₂ θ₁ θ₂)
    (source : Finset (Point ι)) (hs : ∀ x∈source,Valid x)
    (w : Point ι→ℂ) (Ψ : O →* ℂ) (j : O) (σ : Finset ι→ℂ) (ω₁ ω₂ : ℝ→ℂ)
    (hω₁ : ∀ x∈source,clippedSource W₁ c₁ θ₁
      (relativeNorm (coordinates p x) Z D B v θ H 0 * relativeNorm (coordinates p x) Z D B v θ H 2 *
        relativeNorm (coordinates p x) Z D B v θ H 4)≠0 → star (ω₁ (columnRatio p x.left Z D B v))=1)
    (hω₂ : ∀ x∈source,clippedSource W₂ c₂ θ₂
      (relativeNorm (coordinates p x) Z D B v θ H 0 * relativeNorm (coordinates p x) Z D B v θ H 2 *
        relativeNorm (coordinates p x) Z D B v θ H 5)≠0 → ω₂ (columnRatio p x.right Z D B v)=1)
    (hcut : ∀ x∈source,star (ω₁ (columnRatio p x.left Z D B v))≠0 →
      ω₂ (columnRatio p x.right Z D B v)≠0 → ∀ i,V i (relativeLog (coordinates p x) Z D B v θ H i)=1) :
    physicalBlock p hp hcop hg source w Ψ j σ (clippedSource W₁ c₁ θ₁) (clippedSource W₂ c₂ θ₂) Φ Z D m =
      (Z^(prefactorCenter m D B θ+3*η):ℝ)*
      ∫ z : Frequency × (Fin 6→ℝ),familyDensity g g₁ g₂ b₃ c₁ c₂ θ₁ θ₂ (η*Real.log Z) z *
        canonicalBlock p hp hcop hg hpr source w Ψ j σ ω₁ ω₂ Z D B v θ H z := by
  let S := source ×ˢ (Finset.univ : Finset SecondRayIndex)
  let c := fun a : Point ι × SecondRayIndex => w a.1*barePair p hp hcop hg hpr Ψ j σ a.1 a.2 *
    (star (ω₁ (columnRatio p a.1.left Z D B v))*ω₂ (columnRatio p a.1.right Z D B v))
  let y := fun a : Point ι × SecondRayIndex => relativeLog (coordinates p a.1) Z D B v θ H
  have he := family_density_finite_sum S g g₁ g₂ b₃ c₁ c₂ θ₁ θ₂ (η*Real.log Z) c y
  have hpnt (x : Point ι) (hx : x∈source) (ρ : SecondRayIndex) :
      w x*physicalTerm p hp hcop hg Ψ j σ (clippedSource W₁ c₁ θ₁) (clippedSource W₂ c₂ θ₂) Φ Z D m x ρ =
      (Z^(prefactorCenter m D B θ+3*η):ℝ)*c (x,ρ)*
        ∫ z : Frequency × (Fin 6→ℝ),familyDensity g g₁ g₂ b₃ c₁ c₂ θ₁ θ₂ (η*Real.log Z) z *
          pureProfileMode secondLeftSlope secondRightSlope secondKernelSlope (y (x,ρ)) z.1 z.2 := by
    rw [physicalTerm_extracted p hp hcop hg hpr Ψ j σ _ _ Φ Z D m x (hs x hx) ρ]
    rw [hid (fun r=>star (ω₁ r)) ω₂ (coordinates p x) (coordinates_pos p hp x (hs x hx))
      (hω₁ x hx) (hω₂ x hx) (hcut x hx)]
    dsimp only [c,y,barePair]
    rw [relative_column_left,relative_column_right]
    ring
  have hsumeq : physicalBlock p hp hcop hg source w Ψ j σ
      (clippedSource W₁ c₁ θ₁) (clippedSource W₂ c₂ θ₂) Φ Z D m =
      (Z^(prefactorCenter m D B θ+3*η):ℝ)*
        ∑ a∈S,c a*∫ z : Frequency × (Fin 6→ℝ),
          familyDensity g g₁ g₂ b₃ c₁ c₂ θ₁ θ₂ (η*Real.log Z) z *
            pureProfileMode secondLeftSlope secondRightSlope secondKernelSlope (y a) z.1 z.2 := by
    simp only [physicalBlock,S,Finset.sum_product,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro x hx
    apply Finset.sum_congr rfl
    intro ρ hρ
    rw [hpnt x hx ρ]
    ring
  rw [hsumeq,he]
  congr 1
  apply integral_congr_ae
  filter_upwards with z
  congr 1
  simp only [S,Finset.sum_product,canonicalBlock,c,y]
  apply Finset.sum_congr rfl
  intro x hx
  apply Finset.sum_congr rfl
  intro ρ hρ
  rw [mul_assoc (w x),mul_assoc (w x),canonical_pair_mode]

theorem original_ray_common_insertion
    (hinj : Function.Injective (fun i=>Ideal.span {p i}))
    (F G E : Finset ι) (h : O) (Ψ : O →* ℂ) (j : O) (σ : Finset ι→ℂ)
    (W : ℝ→ℂ) (Φ : 𝓢(ℝ,ℂ)) (Z D m : ℝ) :
    (∑ U∈F.powerset,∑ T∈F.powerset,if Disjoint U T then
      initialPhysicalMode p hp hcop hg Ψ j σ W Φ Z D m G U T E h else 0) =
    ∑ V∈F.powerset,∑ N₁∈(F\V).powerset,∑ N₂∈(F\V).powerset,
      ∑ ρ : SecondRayIndex,physicalTerm p hp hcop hg Ψ j σ (fun x=>star (W x)) W Φ Z D m
        ⟨G,E,V,N₁,N₂,h⟩ ρ := by
  rw [CoprimeMobiusExtension.double_sum_disjoint_reindexed]
  apply Finset.sum_congr rfl
  intro V hV
  rw [←prime_product_moebius (fun i=>Ideal.span {p i})
    (fun i=>Ideal.prime_of_isPrime (NeZero.ne _) inferInstance) hinj V]
  simp only [Finset.mul_sum,initialPhysicalMode,Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro N₁ hN₁
  apply Finset.sum_congr rfl
  intro N₂ hN₂
  apply Finset.sum_congr rfl
  intro ρ hρ
  simp only [physicalTerm,divisor,supportMobius]
  ring

theorem physicalBlock_zero (source : Finset (Point ι)) (w : Point ι→ℂ)
    (Ψ : O →* ℂ) (j : O) (σ : Finset ι→ℂ)
    (W₁ W₂ : ℝ→ℂ) (Φ : 𝓢(ℝ,ℂ)) (Z D m : ℝ)
    (hw : ∀ x∈source,w x=0) : physicalBlock p hp hcop hg source w Ψ j σ W₁ W₂ Φ Z D m=0 := by
  unfold physicalBlock
  apply Finset.sum_eq_zero
  intro x hx
  simp only [hw x hx,zero_mul,Finset.sum_const_zero]

include hp in
omit [DecidableEq ι] [∀ i,(Ideal.span {p i}).IsMaximal] in
theorem child_test_clipping (w₀ : ℝ→ℂ) {Z : ℝ} (hZ : 0<Z)
    (N t : ℝ) (A : Finset ι) :
    childLogTest w₀ t ((Ideal.absNorm (sourceIdeal p A):ℝ)/Z^N) =
      logPhase t ((max 0 N-N)*Real.log Z) *
        clippedTest w₀ (Z^(max 0 N-N)) t
          ((Ideal.absNorm (sourceIdeal p A):ℝ)/Z^(max 0 N)) := by
  rw [clippedTest_eq_source]
  simpa only [childLogTest,Real.log_rpow hZ,mul_comm] using
    clipped_column_source_identity w₀ hZ
      (QuadraticMainBoundary.norm_pos (sourceIdeal_ne_zero p hp A)) N t

def BlockSupport (source : Finset (Point ι)) (W₁ W₂ ω₁ ω₂ : ℝ→ℂ)
    (V : Fin 6→ℝ→ℂ) (Z D B v θ H c₁ c₂ θ₁ θ₂ : ℝ) : Prop :=
  (∀ x∈source,clippedSource W₁ c₁ θ₁
    (relativeNorm (coordinates p x) Z D B v θ H 0 * relativeNorm (coordinates p x) Z D B v θ H 2 *
      relativeNorm (coordinates p x) Z D B v θ H 4)≠0 → star (ω₁ (columnRatio p x.left Z D B v))=1) ∧
  (∀ x∈source,clippedSource W₂ c₂ θ₂
    (relativeNorm (coordinates p x) Z D B v θ H 0 * relativeNorm (coordinates p x) Z D B v θ H 2 *
      relativeNorm (coordinates p x) Z D B v θ H 5)≠0 → ω₂ (columnRatio p x.right Z D B v)=1) ∧
  (∀ x∈source,star (ω₁ (columnRatio p x.left Z D B v))≠0 →
    ω₂ (columnRatio p x.right Z D B v)≠0 → ∀ i,V i (relativeLog (coordinates p x) Z D B v θ H i)=1)

theorem actual_initial_block_common_measure
    (W₁ W₂ : ℝ→ℂ) (a b : ℝ) (ha : 0<a)
    (hs₁ : Function.support W₁⊆Set.Icc a b) (hs₂ : Function.support W₂⊆Set.Icc a b)
    (hW₁ : ContDiff ℝ ∞ W₁) (hW₂ : ContDiff ℝ ∞ W₂)
    (Φ : 𝓢(ℝ,ℂ)) (V : Fin 6→ℝ→ℂ) (M : Fin 6→ℝ)
    (hV : ∀ i,ContDiff ℝ ∞ (V i)) (hS : ∀ i,HasCompactSupport (V i))
    (hM : ∀ i,0≤M i) (hbox : ∀ i y,V i y≠0 → |y|≤M i) (A J : ℕ) :
    let g := secondRootSchwartz V hV hS
    let g₁ := CubicReflectionKernel.logSchwartz W₁ a b ha hs₁ hW₁
    let g₂ := CubicReflectionKernel.logSchwartz W₂ a b ha hs₂ hW₂
    ∃ C : ℝ,0≤C ∧ ∀ Z D B v m θ H η : ℝ,0<Z → 0≤η*Real.log Z →
      ∃ b₃ : 𝓢(ℝ,ℂ),∀ c₁ c₂ θ₁ θ₂ : ℝ,0<c₁ → 0<c₂ →
      (∀ {κ : Type*} [DecidableEq κ] (p : κ→O) (hp : ∀ i,p i≠0)
        [∀ i,(Ideal.span {p i}).IsMaximal]
        (hcop : Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
        (hg : ∀ i,goodLambda∉Ideal.span {p i}) (hpr : ∀ i,goodLambda^2∣p i-1)
        (source : Finset (Point κ)) (_hs : ∀ x∈source,Valid x)
        (w : Point κ→ℂ) (Ψ : O →* ℂ) (j : O) (σ : Finset κ→ℂ) (ω₁ ω₂ : ℝ→ℂ),
        BlockSupport p source W₁ W₂ ω₁ ω₂ V Z D B v θ H c₁ c₂ θ₁ θ₂ →
        physicalBlock p hp hcop hg source w Ψ j σ
          (clippedSource W₁ c₁ θ₁) (clippedSource W₂ c₂ θ₂) Φ Z D m =
          (Z^(prefactorCenter m D B θ+3*η):ℝ)*
            ∫ z : Frequency × (Fin 6→ℝ),familyDensity g g₁ g₂ b₃ c₁ c₂ θ₁ θ₂ (η*Real.log Z) z *
              canonicalBlock p hp hcop hg hpr source w Ψ j σ ω₁ ω₂ Z D B v θ H z) ∧
      Integrable (fun z : Frequency × (Fin 6→ℝ)=>tripleHeight J z.1*coordinateHeight J z.2*
        ‖familyDensity g g₁ g₂ b₃ c₁ c₂ θ₁ θ₂ (η*Real.log Z) z‖) ∧
      (1+Z^(radialCenter m H θ D B))^A *
        (∫ z : Frequency × (Fin 6→ℝ),tripleHeight J z.1*coordinateHeight J z.2*
          ‖familyDensity g g₁ g₂ b₃ c₁ c₂ θ₁ θ₂ (η*Real.log Z) z‖) ≤
        C*((1+‖θ₁‖)^InverseClippingProfiles.momentOrder J*(1+‖θ₂‖)^InverseClippingProfiles.momentOrder J) := by
  dsimp only
  obtain ⟨C,hC,hfamily⟩ := initial_physical_family_common_measure
    W₁ W₂ a b ha hs₁ hs₂ hW₁ hW₂ Φ V M hV hS hM hbox A J
  refine ⟨C,hC,?_⟩
  intro Z D B v m θ H η hZ hL
  obtain ⟨b₃,hb₃⟩ := hfamily Z D B v m θ H η hZ hL
  refine ⟨b₃,?_⟩
  intro c₁ c₂ θ₁ θ₂ hc₁ hc₂
  obtain ⟨hid,hi,hb⟩ := hb₃ c₁ c₂ θ₁ θ₂ hc₁ hc₂
  refine ⟨?_,hi,hb⟩
  intro κ _ p hp _ hcop hg hpr source hs w Ψ j σ ω₁ ω₂ hsupport
  exact physicalBlock_integral p hp hcop hg hpr W₁ W₂ Φ V _ _ _ b₃
    Z D B v m θ H η c₁ c₂ θ₁ θ₂ hid source hs w Ψ j σ ω₁ ω₂
    hsupport.1 hsupport.2.1 hsupport.2.2

open InverseInitialOverlap InverseInitialPoissonBridge CanonicalQuadraticSieve

def overlapDilation (P j : Ideal O) (Z z G : ℝ) : ℝ :=
  ((Ideal.absNorm j:ℝ)/Z^G)/((Ideal.absNorm (residual P j):ℝ)/Z^(z-G))

theorem residualWindow_eq_clipped (P j : Ideal O) (W : ℝ→ℂ) (Z z G : ℝ) :
    residualOverlapWindow P j W Z z G=clippedSource W (overlapDilation P j Z z G) 0 := by
  funext x
  simp only [residualOverlapWindow,clippedSource,logPhase,mul_zero,Complex.ofReal_zero,zero_mul,Complex.exp_zero,one_mul,overlapDilation]
  congr 1
  ring

theorem overlapDilation_pos {P j : Ideal O} (hP : Admissible P) (hj : j∣P)
    {Z : ℝ} (hZ : 0<Z) (z G : ℝ) : 0<overlapDilation P j Z z G := by
  exact div_pos (div_pos (QuadraticMainBoundary.norm_pos (admissible_of_dvd hP hj).2.1.ne_zero)
      (Real.rpow_pos_of_pos hZ _))
    (div_pos (QuadraticMainBoundary.norm_pos (residual_squarefree hP.2.1 hj).ne_zero)
      (Real.rpow_pos_of_pos hZ _))

theorem clippedSource_zero_star (W : ℝ→ℂ) (c : ℝ) :
    (fun x=>star (clippedSource W c 0 x))=clippedSource (fun x=>star (W x)) c 0 := by
  funext x
  simp [clippedSource,logPhase]

def originalBlock (S : Finset (Ideal O)) {P j : Ideal O}
    (hP : Admissible P) (hj : j∣P) (hS : ∀ n∈S,Squarefree n → Supported n)
    (η : Ideal O →* ℂ) (a : Ideal O→ℂ) (W : ℝ→ℂ) (Φ : 𝓢(ℝ,ℂ))
    (Z r z G m : ℝ) (source : Finset (Point (primePool (columns S P j))))
    (w : Point (primePool (columns S P j))→ℂ) : ℂ :=
  let F := columns S P j
  let hF : ∀ I∈F,Admissible I := fun I hI=>columns_admissible S hP hj hS hI
  letI : ∀ i : primePool F,(Ideal.span {poolPrimary F i}).IsMaximal :=
    fun i=>by rw [poolPrimary_span F hF i];infer_instance
  physicalBlock (poolPrimary F) (poolPrimary_ne_zero F hF) (poolPrimary_coprime F hF)
    (poolPrimary_good F hF) source w (elementCharacter η) (primaryGenerator j)
    (reconstructedSelector S P j a) (fun x=>star (residualOverlapWindow P j W Z z G x))
    (residualOverlapWindow P j W Z z G) Φ Z (r+z-2*G) m

theorem originalBlock_integral
    (S : Finset (Ideal O)) {P j : Ideal O}
    (hP : Admissible P) (hj : j∣P) (hS : ∀ n∈S,Squarefree n → Supported n)
    (η : Ideal O →* ℂ) (a : Ideal O→ℂ) (W : ℝ→ℂ) (Φ : 𝓢(ℝ,ℂ))
    (V : Fin 6→ℝ→ℂ) (g : Fin 6→𝓢(ℝ,ℂ)) (g₁ g₂ b₃ : 𝓢(ℝ,ℂ))
    (Z r z G B v m θ H ε : ℝ)
    (hid : PhysicalIdentityAt (fun x=>star (W x)) W Φ V g g₁ g₂ b₃
      Z (r+z-2*G) B v m θ H ε (overlapDilation P j Z z G) (overlapDilation P j Z z G) 0 0)
    (source : Finset (Point (primePool (columns S P j)))) (hs : ∀ x∈source,Valid x)
    (w : Point (primePool (columns S P j))→ℂ) (ω₁ ω₂ : ℝ→ℂ)
    (hcut : BlockSupport (poolPrimary (columns S P j)) source (fun x=>star (W x)) W ω₁ ω₂ V
      Z (r+z-2*G) B v θ H (overlapDilation P j Z z G) (overlapDilation P j Z z G) 0 0) :
    let F := columns S P j
    let hF : ∀ I∈F,Admissible I := fun I hI=>columns_admissible S hP hj hS hI
    letI : ∀ i : primePool F,(Ideal.span {poolPrimary F i}).IsMaximal :=
      fun i=>by rw [poolPrimary_span F hF i];infer_instance
    originalBlock S hP hj hS η a W Φ Z r z G m source w =
      (Z^(prefactorCenter m (r+z-2*G) B θ+3*ε):ℝ)*
        ∫ q : Frequency × (Fin 6→ℝ),
          familyDensity g g₁ g₂ b₃ (overlapDilation P j Z z G) (overlapDilation P j Z z G)
            0 0 (ε*Real.log Z) q *
          canonicalBlock (poolPrimary F) (poolPrimary_ne_zero F hF) (poolPrimary_coprime F hF)
            (poolPrimary_good F hF) (poolPrimary_primary F hF) source w (elementCharacter η)
            (primaryGenerator j) (reconstructedSelector S P j a) ω₁ ω₂ Z (r+z-2*G) B v θ H q := by
  intro F hF
  let : ∀ i : primePool F,(Ideal.span {poolPrimary F i}).IsMaximal :=
    fun i=>by rw [poolPrimary_span F hF i];infer_instance
  unfold originalBlock
  rw [residualWindow_eq_clipped,clippedSource_zero_star]
  exact physicalBlock_integral (poolPrimary F) (poolPrimary_ne_zero F hF) (poolPrimary_coprime F hF)
    (poolPrimary_good F hF) (poolPrimary_primary F hF) _ _ Φ V g g₁ g₂ b₃
    Z (r+z-2*G) B v m θ H ε _ _ 0 0 hid source hs w (elementCharacter η)
    (primaryGenerator j) (reconstructedSelector S P j a) ω₁ ω₂ hcut.1 hcut.2.1 hcut.2.2

end SevenEighths.InverseInitialPhysicalMeasure

end

end OAI
