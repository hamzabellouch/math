import OAI.NumberTheory.DirichletL.CubicSieve.ReopenedFibers

namespace OAI

noncomputable section

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
open scoped BigOperators
open scoped BigOperators Classical SchwartzMap
open scoped BigOperators Classical

open scoped BigOperators Classical SchwartzMap
namespace SecondPassArithmetic
open ActualEisensteinCubic
open ConcreteTraceCRT (eisEmbedding eisEmbedding_ne_zero)
open FirstPassCubeLabels (columnLog primeProductNorm)
open FourierBridge (logPhase)
open JointLogSeparation (frequencyTwist)

def normPhase (t : ℝ) : ActualEisensteinCubic.O →* ℂ where
  toFun z := if z=0 then 0 else logPhase t (Real.log (‖eisEmbedding z‖^2))
  map_one' := by simp [FourierBridge.logPhase_zero]
  map_mul' a b := by
    by_cases ha : a=0
    · simp [ha]
    by_cases hb : b=0
    · simp [hb]
    simp only [ite_eq_right ha,ite_eq_right hb,ite_eq_right (mul_ne_zero ha hb),map_mul,norm_mul,mul_pow]
    rw [Real.log_mul (pow_ne_zero _ (norm_ne_zero_iff.mpr (eisEmbedding_ne_zero ha)))
      (pow_ne_zero _ (norm_ne_zero_iff.mpr (eisEmbedding_ne_zero hb))),FourierBridge.logPhase_add]

@[simp] theorem normPhase_zero (t : ℝ) : normPhase t 0=0 := by simp [normPhase]

theorem normPhase_of_ne_zero (t : ℝ) (z : ActualEisensteinCubic.O) (hz : z≠0) :
    normPhase t z=logPhase t (Real.log (‖eisEmbedding z‖^2)) := by simp [normPhase,hz]

theorem normPhase_norm (t : ℝ) (z : ActualEisensteinCubic.O) (hz : z≠0) : ‖normPhase t z‖=1 := by
  rw [normPhase_of_ne_zero t z hz,FourierBridge.logPhase_norm]

theorem normPhase_norm_le_one (t : ℝ) (z : ActualEisensteinCubic.O) : ‖normPhase t z‖≤1 := by
  by_cases hz : z=0
  · simp [hz]
  · rw [normPhase_norm t z hz]

theorem normPhase_add (s t : ℝ) : normPhase (s+t)=normPhase s*normPhase t := by
  ext z
  by_cases hz : z=0
  · simp [hz]
  · simp only [MonoidHom.mul_apply,normPhase_of_ne_zero _ z hz,JointLogSeparation.logPhase_add_frequency]

theorem normPhase_star (t : ℝ) (z : ActualEisensteinCubic.O) : star (normPhase t z)=normPhase (-t) z := by
  by_cases hz : z=0
  · simp [hz]
  · simp only [normPhase_of_ne_zero _ z hz,SecondPassIntegration.logPhase_conjugate]

def normHeightTwist (Ψ : ActualEisensteinCubic.O →* ℂ) (t : ℝ) : ActualEisensteinCubic.O →* ℂ := Ψ*normPhase t

theorem normHeightTwist_norm_le (Ψ : ActualEisensteinCubic.O →* ℂ) (t : ℝ) (z : ActualEisensteinCubic.O) :
    ‖normHeightTwist Ψ t z‖≤‖Ψ z‖ := by
  simp only [normHeightTwist,MonoidHom.mul_apply,norm_mul]
  exact mul_le_of_le_one_right (norm_nonneg _) (normPhase_norm_le_one t z)

theorem normHeightTwist_twice (Ψ : ActualEisensteinCubic.O →* ℂ) (s t : ℝ) :
    normHeightTwist (normHeightTwist Ψ s) t=normHeightTwist Ψ (s+t) := by
  simp only [normHeightTwist,normPhase_add,mul_assoc]

theorem normHeightTwist_mul (Ψ Ξ : ActualEisensteinCubic.O →* ℂ) (t : ℝ) :
    normHeightTwist (Ψ*Ξ) t=normHeightTwist Ψ t*Ξ := by
  unfold normHeightTwist
  ac_rfl

variable {ι : Type*} [DecidableEq ι] (p : ι → ActualEisensteinCubic.O) (hp : ∀i,p i≠0)

include hp in
omit [DecidableEq ι] in
theorem logPhase_columnLog (X t : ℝ) (hX : 0<X) (S : Finset ι) :
    logPhase t (columnLog p X S)=
      logPhase t (-Real.log X)*normPhase t (∏i∈S,p i) := by
  rw [normPhase_of_ne_zero t _ (Finset.prod_ne_zero_iff.mpr (fun i _=>hp i))]
  rw [columnLog,Real.log_div (FirstPassCubeLabels.primeProductNorm_pos p hp S).ne' hX.ne']
  rw [sub_eq_add_neg,FourierBridge.logPhase_add]
  exact mul_comm _ _

variable [∀i,(Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
  (hg : ∀i,lambda∉Ideal.span {p i})

theorem canonicalSourceCoefficient_frequencyTwist (Ψ : ActualEisensteinCubic.O →* ℂ) (m f : ActualEisensteinCubic.O)
    (g : 𝓢(ℝ,ℂ)) (X t : ℝ) (hX : 0<X) (S : Finset ι) :
    canonicalSourceCoefficient p hp hcop hg Ψ m f
      (fun U=>frequencyTwist g t (columnLog p X U)) S=
    logPhase t (-Real.log X)*canonicalSourceCoefficient p hp hcop hg (normHeightTwist Ψ t) m f
      (fun U=>g (columnLog p X U)) S := by
  simp only [canonicalSourceCoefficient,JointLogSeparation.frequencyTwist_apply,
    logPhase_columnLog p hp X t hX S,normHeightTwist,MonoidHom.mul_apply]
  ring

theorem fixedChildRow_frequencyTwist (pool : Finset ι) (Ψ : ActualEisensteinCubic.O →* ℂ) (m f y : ActualEisensteinCubic.O)
    (g : 𝓢(ℝ,ℂ)) (X t : ℝ) (hX : 0<X) :
    fixedChildRow p hp hcop hg pool Ψ m (fun U=>frequencyTwist g t (columnLog p X U)) f y=
    logPhase t (-Real.log X)*fixedChildRow p hp hcop hg pool (normHeightTwist Ψ t) m
      (fun U=>g (columnLog p X U)) f y := by
  unfold fixedChildRow
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro S hS
  simp only [secondChildColumn,JointLogSeparation.frequencyTwist_apply,
    logPhase_columnLog p hp X t hX S,normHeightTwist,MonoidHom.mul_apply]
  ring

theorem fixedChildRow_frequencyTwist_norm (pool : Finset ι) (Ψ : ActualEisensteinCubic.O →* ℂ) (m f y : ActualEisensteinCubic.O)
    (g : 𝓢(ℝ,ℂ)) (X t : ℝ) (hX : 0<X) :
    ‖fixedChildRow p hp hcop hg pool Ψ m (fun U=>frequencyTwist g t (columnLog p X U)) f y‖=
    ‖fixedChildRow p hp hcop hg pool (normHeightTwist Ψ t) m
      (fun U=>g (columnLog p X U)) f y‖ := by
  rw [fixedChildRow_frequencyTwist p hp hcop hg pool Ψ m f y g X t hX,norm_mul,FourierBridge.logPhase_norm,one_mul]

end SecondPassArithmetic

section

open scoped BigOperators Classical
namespace SecondPassArithmetic
open ActualEisensteinCubic
open FourierBridge (logPhase)
open FirstPassCubeLabels (columnLog)

def secondSignedHeight (negative : Bool) (a b : ℝ) : ℝ :=
  if negative then b-a else a-b

variable {ι : Type*} [DecidableEq ι] (p : ι → ActualEisensteinCubic.O) (hp : ∀i,p i≠0)

include hp in
omit [DecidableEq ι] in
theorem fixedSecondTest_normPhase (V : ℝ → ℂ) (X a b : ℝ) (hX : 0<X)
    (negative : Bool) (S : Finset ι) :
    fixedSecondTest p V X a b negative S=
      logPhase (secondSignedHeight negative a b) (-Real.log X)*
      normPhase (secondSignedHeight negative a b) (∏i∈S,p i)*
      fixedSecondTest p V X 0 0 negative S := by
  have hz (x : ℝ) : logPhase 0 x=1 := by simp [FourierBridge.logPhase]
  cases negative <;>
    simp only [secondSignedHeight,fixedSecondTest,JointLogSeparation.fixedColumnTest,
      Bool.false_eq_true,ite_false,ite_true,sub_self,hz,mul_one,star_mul,
      SecondPassIntegration.logPhase_conjugate,neg_sub] <;>
    rw [logPhase_columnLog p hp X _ hX S] ; ring

variable [∀i,(Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
  (hg : ∀i,lambda∉Ideal.span {p i})

theorem fixedChildRow_secondTest_normPhase (pool : Finset ι) (Ψ : ActualEisensteinCubic.O →* ℂ) (m f y : ActualEisensteinCubic.O)
    (V : ℝ → ℂ) (X a b : ℝ) (hX : 0<X) (negative : Bool) :
    fixedChildRow p hp hcop hg pool Ψ m (fixedSecondTest p V X a b negative) f y=
      logPhase (secondSignedHeight negative a b) (-Real.log X)*
      fixedChildRow p hp hcop hg pool (normHeightTwist Ψ (secondSignedHeight negative a b)) m
        (fixedSecondTest p V X 0 0 negative) f y := by
  unfold fixedChildRow
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro S hS
  simp only [secondChildColumn,fixedSecondTest_normPhase p hp V X a b hX negative S,
    normHeightTwist,MonoidHom.mul_apply]
  ring

end SecondPassArithmetic

namespace SecondPassIntegration
open ActualEisensteinCubic SecondPassArithmetic

variable {ι : Type*} [DecidableEq ι] (p : ι → ActualEisensteinCubic.O) (hp : ∀i,p i≠0)
  [∀i,(Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
  (hg : ∀i,lambda∉Ideal.span {p i})

theorem childEnergy_normHeight (pool : Finset ι) (Ψ : ActualEisensteinCubic.O →* ℂ) (m : ActualEisensteinCubic.O)
    (T : Finset (Ideal ActualEisensteinCubic.O × ActualEisensteinCubic.O)) (V : ℝ → ℂ) (X a b : ℝ) (hX : 0<X)
    (testNegative rowNegative : Bool) :
    childEnergy p hp hcop hg pool Ψ m T V X testNegative rowNegative a b=
      childEnergy p hp hcop hg pool (normHeightTwist Ψ (secondSignedHeight testNegative a b))
        m T V X testNegative rowNegative 0 0 := by
  unfold childEnergy idealChildRow
  simp_rw [fixedChildRow_secondTest_normPhase p hp hcop hg pool Ψ m _ _ V X a b hX testNegative,
    norm_mul,FourierBridge.logPhase_norm,one_mul]

theorem childEnergy_previousNormHeight (pool : Finset ι) (Ψ : ActualEisensteinCubic.O →* ℂ) (m : ActualEisensteinCubic.O)
    (T : Finset (Ideal ActualEisensteinCubic.O × ActualEisensteinCubic.O)) (V : ℝ → ℂ) (X t a b : ℝ) (hX : 0<X)
    (testNegative rowNegative : Bool) :
    childEnergy p hp hcop hg pool (normHeightTwist Ψ t) m T V X testNegative rowNegative a b=
      childEnergy p hp hcop hg pool (normHeightTwist Ψ (t+secondSignedHeight testNegative a b))
        m T V X testNegative rowNegative 0 0 := by
  rw [childEnergy_normHeight p hp hcop hg pool (normHeightTwist Ψ t) m T V X a b hX
    testNegative rowNegative,normHeightTwist_twice]

end SecondPassIntegration

open scoped BigOperators Classical
open MeasureTheory
namespace SecondPassArithmetic
open ActualEisensteinCubic

theorem firstCoreTwist_normHeight (negative : Bool) (χ : RayFourExpansion.RayCharacter)
    (Ψ : ActualEisensteinCubic.O →* ℂ) (r : FirstCoreIndex) (t : ℝ) :
    firstCoreTwist negative χ (normHeightTwist Ψ t) r=
      normHeightTwist (firstCoreTwist negative χ Ψ r) t := by
  unfold firstCoreTwist normHeightTwist
  ac_rfl

theorem secondRayMinus_normHeight (Ψ : ActualEisensteinCubic.O →* ℂ) (r : SecondRayIndex) (t : ℝ) :
    secondRayMinus (normHeightTwist Ψ t) r=normHeightTwist (secondRayMinus Ψ r) t := by
  unfold secondRayMinus normHeightTwist
  ac_rfl

theorem secondRayPlus_normHeight (Ψ : ActualEisensteinCubic.O →* ℂ) (r : SecondRayIndex) (t : ℝ) :
    secondRayPlus (normHeightTwist Ψ t) r=normHeightTwist (secondRayPlus Ψ r) t := by
  unfold secondRayPlus normHeightTwist
  ac_rfl

end SecondPassArithmetic

namespace SecondPassIntegration
open ActualEisensteinCubic SecondPassArithmetic

private theorem sqrt_height_weight (B t : ℝ) (hB : 0≤B) (J : ℕ) :
    Real.sqrt (B*(1+‖t‖)^(2*J))=Real.sqrt B*(1+‖t‖)^J := by
  rw [show 2*J=J*2 from Nat.mul_comm _ _,pow_mul,Real.sqrt_mul hB,
    Real.sqrt_sq (pow_nonneg (by positivity : 0≤1+‖t‖) J)]

variable {ι : Type*} [DecidableEq ι] (p : ι → ActualEisensteinCubic.O) (hp : ∀i,p i≠0)
  [∀i,(Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
  (hg : ∀i,lambda∉Ideal.span {p i})

theorem densityChildEnergy_normHeight_polynomial
    (pool : Finset ι) (Ψ₁ Ψ₂ : ActualEisensteinCubic.O →* ℂ) (m : ActualEisensteinCubic.O) (T : Finset (Ideal ActualEisensteinCubic.O × ActualEisensteinCubic.O))
    (V₁ V₂ : ℝ → ℂ) (X₁ X₂ t₁ t₂ B₁ B₂ : ℝ) (J : ℕ)
    (hX₁ : 0<X₁) (hX₂ : 0<X₂) (hB₁ : 0≤B₁) (hB₂ : 0≤B₂)
    (h₁ : ∀t,childEnergy p hp hcop hg pool (normHeightTwist Ψ₁ t) m T V₁ X₁ true false 0 0≤
      B₁*(1+‖t‖)^(2*J))
    (h₂ : ∀t,childEnergy p hp hcop hg pool (normHeightTwist Ψ₂ t) m T V₂ X₂ false true 0 0≤
      B₂*(1+‖t‖)^(2*J)) :
    densityChildEnergy p hp hcop hg pool (normHeightTwist Ψ₁ t₁) (normHeightTwist Ψ₂ t₂)
      m T V₁ V₂ X₁ X₂ (2*J)≤
      Real.sqrt B₁*Real.sqrt B₂*(1+‖t₁‖)^J*(1+‖t₂‖)^J*
        (∫t : ℝ,FirstPassCubeLabels.firstLogDensity 0 t)^3 := by
  have ha₁ (a : ℝ) : childEnergy p hp hcop hg pool (normHeightTwist Ψ₁ t₁) m T V₁ X₁ true false a 0≤
      (B₁*(1+‖t₁‖)^(2*J))*(1+‖a‖)^(2*J) := by
    rw [childEnergy_previousNormHeight p hp hcop hg pool Ψ₁ m T V₁ X₁ t₁ a 0 hX₁ true false]
    simp only [secondSignedHeight,ite_true,zero_sub,←sub_eq_add_neg]
    calc
      _ ≤ B₁*(1+‖t₁-a‖)^(2*J) := h₁ (t₁-a)
      _ ≤ B₁*((1+‖t₁‖)*(1+‖a‖))^(2*J) :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity)
          (JointLogSeparation.one_add_norm_sub_le t₁ a) _) hB₁
      _ = _ := by rw [mul_pow]; ring
  have ha₂ (a : ℝ) : childEnergy p hp hcop hg pool (normHeightTwist Ψ₂ t₂) m T V₂ X₂ false true a 0≤
      (B₂*(1+‖t₂‖)^(2*J))*(1+‖a‖)^(2*J) := by
    rw [childEnergy_previousNormHeight p hp hcop hg pool Ψ₂ m T V₂ X₂ t₂ a 0 hX₂ false true]
    simp only [secondSignedHeight,Bool.false_eq_true,ite_false,sub_zero]
    have hsum : 1+‖t₂+a‖≤(1+‖t₂‖)*(1+‖a‖) := by
      simpa only [sub_neg_eq_add,norm_neg] using JointLogSeparation.one_add_norm_sub_le t₂ (-a)
    calc
      _ ≤ B₂*(1+‖t₂+a‖)^(2*J) := h₂ (t₂+a)
      _ ≤ B₂*((1+‖t₂‖)*(1+‖a‖))^(2*J) :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hsum _) hB₂
      _ = _ := by rw [mul_pow]; ring
  have hd := densityChildEnergy_polynomial_bound p hp hcop hg pool
    (normHeightTwist Ψ₁ t₁) (normHeightTwist Ψ₂ t₂) m T V₁ V₂ X₁ X₂ J
    (B₁*(1+‖t₁‖)^(2*J)) (B₂*(1+‖t₂‖)^(2*J))
    (mul_nonneg hB₁ (by positivity)) (mul_nonneg hB₂ (by positivity)) ha₁ ha₂
  rw [sqrt_height_weight B₁ t₁ hB₁ J,sqrt_height_weight B₂ t₂ hB₂ J] at hd
  exact hd.trans_eq (by ring)

end SecondPassIntegration
end

open scoped BigOperators Classical SchwartzMap
namespace SecondPassArithmetic

section
open ActualEisensteinCubic
open FirstPassCubeLabels (columnLog)
open FourierBridge (logPhase)
open JointLogSeparation (frequencyTwist)

variable {ι : Type*} [DecidableEq ι] (p : ι → ActualEisensteinCubic.O) (hp : ∀i,p i≠0)
  [∀i,(Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
  (hg : ∀i,lambda∉Ideal.span {p i})

theorem reopenedCanonicalRow_frequencyTwist (pool : Finset ι) (Q : Finset (ι→₀ℕ))
    (β : (ι→₀ℕ)→ℂ) (Ψ : ActualEisensteinCubic.O →* ℂ) (m f z : ActualEisensteinCubic.O) (g : 𝓢(ℝ,ℂ))
    (X t : ℝ) (hX : 0<X) :
    reopenedCanonicalRow p hp hcop hg pool Q β Ψ m f
      (fun S=>frequencyTwist g t (columnLog p X S)) z=
      logPhase t (-Real.log X)*reopenedCanonicalRow p hp hcop hg pool Q β (normHeightTwist Ψ t) m f
        (fun S=>g (columnLog p X S)) z := by
  unfold reopenedCanonicalRow
  simp_rw [canonicalSourceCoefficient_frequencyTwist p hp hcop hg Ψ m f g X t hX,
    Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro v hv
  apply Finset.sum_congr rfl
  intro S hS
  ring

theorem reopenedCanonicalRow_frequencyTwist_norm (pool : Finset ι) (Q : Finset (ι→₀ℕ))
    (β : (ι→₀ℕ)→ℂ) (Ψ : ActualEisensteinCubic.O →* ℂ) (m f z : ActualEisensteinCubic.O) (g : 𝓢(ℝ,ℂ))
    (X t : ℝ) (hX : 0<X) :
    ‖reopenedCanonicalRow p hp hcop hg pool Q β Ψ m f
      (fun S=>frequencyTwist g t (columnLog p X S)) z‖=
      ‖reopenedCanonicalRow p hp hcop hg pool Q β (normHeightTwist Ψ t) m f
        (fun S=>g (columnLog p X S)) z‖ := by
  rw [reopenedCanonicalRow_frequencyTwist p hp hcop hg pool Q β Ψ m f z g X t hX,
    norm_mul,FourierBridge.logPhase_norm,one_mul]

theorem reopenedSource_frequencyTwist
    (hinj : Function.Injective (fun i=>Ideal.span {p i}))
    (hpr : ∀i,lambda^2∣p i-1) (pool : Finset ι) (Q : Finset (ι→₀ℕ))
    (hQ : ∀v∈Q,v.support⊆pool) (labels : Finset (Ideal ActualEisensteinCubic.O))
    (β : Ideal ActualEisensteinCubic.O→(ι→₀ℕ)→ℂ) (Ψ : ActualEisensteinCubic.O →* ℂ) (m : ActualEisensteinCubic.O) (g W : 𝓢(ℝ,ℂ))
    (K X t : ℝ) (hK : 0<K) (hX : 0<X) :
    canonicalSourceTotal p hp hcop hg pool (reopenedCubeFamily Q) labels (reopenedPairCoefficient β)
      Ψ Ψ m m (frequencyTwist g t) (frequencyTwist g t) W K X=
    canonicalSourceTotal p hp hcop hg pool (reopenedCubeFamily Q) labels (reopenedPairCoefficient β)
      (normHeightTwist Ψ t) (normHeightTwist Ψ t) m m g g W K X := by
  rw [←reopenedCanonicalRow_smoothed_eq_source p hp hcop hg hinj hpr pool Q hQ labels β Ψ m
    (frequencyTwist g t) W K X hK,
    ←reopenedCanonicalRow_smoothed_eq_source p hp hcop hg hinj hpr pool Q hQ labels β
      (normHeightTwist Ψ t) m g W K X hK]
  apply Finset.sum_congr rfl
  intro I hI
  apply tsum_congr
  intro z
  rw [reopenedCanonicalRow_frequencyTwist_norm p hp hcop hg pool Q (β I) Ψ m _ z g X t hX]

end

open ActualEisensteinCubic FirstPassCubeLabels
open ConcreteTraceCRT (eisEmbedding)
open JointLogSeparation (frequencyTwist)

theorem reopenedCanonicalRow_twoPassage_uniform_height
    (W g V : 𝓢(ℝ,ℂ)) (M Nv : ℝ) (hM : 0≤M) (hNv : 0≤Nv)
    (hgM : ∀t,g t≠0→|t|≤M) (hV : ∀t,V t≠0→|t|≤Nv)
    (hWin : ∀t,g t≠0→V t=1)
    (ε deltaLoss : ℝ) (hε : 0<ε) (hδ : 0<deltaLoss) (A J N : ℕ) :
    ∃(windows₁ windows₂ : Fin 7→ℝ→ℂ) (Cfirst C₁ Cd₁ Ct₁ C₂ Cd₂ Ct₂ : ℝ),
      0≤Cfirst ∧ 0≤C₁ ∧ 0<Cd₁ ∧ 0<Ct₁ ∧ 0≤C₂ ∧ 0<Cd₂ ∧ 0<Ct₂ ∧
      (∀i,HasCompactSupport (windows₁ i)) ∧ (∀i,ContDiff ℝ ∞ (windows₁ i)) ∧
      (∀i t,windows₁ i t≠0→|t|≤M+6+1) ∧
      (∀i,HasCompactSupport (windows₂ i)) ∧ (∀i,ContDiff ℝ ∞ (windows₂ i)) ∧
      (∀i t,windows₂ i t≠0→|t|≤M+6+1) ∧
      ∀{ι:Type*} [DecidableEq ι]
      (p:ι→ActualEisensteinCubic.O) (hp:∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
      (_hinj:Function.Injective (fun i=>Ideal.span {p i}))
      (hcop:Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
      (hg:∀i,lambda∉Ideal.span {p i}) (_hc:∀i,ringChar (ActualEisensteinCubic.O⧸Ideal.span {p i})≠2)
      (_hpr:∀i,lambda^2∣p i-1)
      (pool:Finset ι) (Q:Finset (ι→₀ℕ)) (labels:Finset (Ideal ActualEisensteinCubic.O))
      (β:Ideal ActualEisensteinCubic.O→(ι→₀ℕ)→ℂ) (Ψ:ActualEisensteinCubic.O→*ℂ) (m:ActualEisensteinCubic.O) (Γ t Ksrc K ell B F H U:ℝ),
      0≤Γ → 0<Ksrc → 0<K → 0<ell → 1≤B → 0<F → 0≤H → 1≤U →
      ell*Real.exp M≤U → (∀u,‖Ψ u‖≤1) →
      (∀I∈labels,∀v∈Q,‖β I v‖≤Γ) → (∀v∈Q,v.support⊆pool) →
      (∀v∈Q,‖eisEmbedding (primeProduct p v.support v)‖^2≤B) →
      (∀I∈labels,Squarefree I) → (∀I∈labels,(Ideal.absNorm I:ℝ)≤F) →
      let Ψt:=normHeightTwist Ψ t
      let bs:=reopenedCubeFamily Q
      let a:=reopenedPairCoefficient β
      ‖(ell*B^2*F:ℂ)⁻¹*
        ((∑I∈labels,∑'z:ActualEisensteinCubic.O,W (‖eisEmbedding z‖^2/Ksrc)*
           (‖reopenedCanonicalRow p hp hcop hg pool Q (β I) Ψ m
             (ConcretePrimeRowBridge.idealGenerator I)
             (fun S=>frequencyTwist g t (columnLog p ell S)) z‖^2:ℝ))-
         canonicalSourceZero p hp hcop hg pool bs labels a Ψt Ψt m m g g W Ksrc ell-
         canonicalSourceTail p hp hcop hg pool bs labels a Ψt Ψt m m g g W Ksrc K ell)‖≤
      (Ksrc/K)*Cfirst*(globalFirstRowCap K ell B F)^deltaLoss*
        Real.sqrt (globalFirstQuantitativeBudget p hp hcop hg pool (canonicalSourceBlocks pool bs)
          Ψt m windows₁ C₁ Cd₁ Ct₁ (Γ^2) ε K ell B F M H U A J N true)*
        Real.sqrt (globalFirstQuantitativeBudget p hp hcop hg pool (canonicalSourceBlocks pool bs)
          Ψt m windows₂ C₂ Cd₂ Ct₂ (Γ^2) ε K ell B F M H U A J N false) := by
  obtain ⟨windows₁,windows₂,Cfirst,C₁,Cd₁,Ct₁,C₂,Cd₂,Ct₂,hCf,hC₁,hCd₁,hCt₁,hC₂,hCd₂,hCt₂,
    hw₁,hs₁,hb₁,hw₂,hs₂,hb₂,htransfer⟩:=
    canonicalSource_twoPassage_quantitative W g g V V M M Nv Nv hM hM hNv hNv
      hgM hgM hV hV hWin hWin ε deltaLoss hε hδ A J N
  refine ⟨windows₁,windows₂,Cfirst,C₁,Cd₁,Ct₁,C₂,Cd₂,Ct₂,hCf,hC₁,hCd₁,hCt₁,hC₂,hCd₂,hCt₂,
    hw₁,hs₁,hb₁,hw₂,hs₂,hb₂,?_⟩
  intro ι _ p hp _ hinj hcop hg hc hpr pool Q labels β Ψ m Γ t Ksrc K ell B F H U
    hΓ hKsrc hK hell hB hF hH hU hMU hΨ hβ hQ hQB hsf hf
  dsimp only
  rw [reopenedCanonicalRow_smoothed_eq_source p hp hcop hg hinj hpr pool Q hQ labels β Ψ m
    (frequencyTwist g t) W Ksrc ell hKsrc,
    reopenedSource_frequencyTwist p hp hcop hg hinj hpr pool Q hQ labels β Ψ m g W Ksrc ell t hKsrc hell]
  have hΨt : ∀u,‖normHeightTwist Ψ t u‖≤1 :=
    fun u=>(normHeightTwist_norm_le Ψ t u).trans (hΨ u)
  exact htransfer p hp hinj hcop hg hc hpr pool (reopenedCubeFamily Q) labels (reopenedPairCoefficient β)
    (normHeightTwist Ψ t) (normHeightTwist Ψ t) m m (Γ^2) Ksrc K ell B F H U
    (sq_nonneg Γ) hKsrc hK hell hB hF hH hU hMU hMU hΨt hΨt
    (fun b hb C hC I hI=>reopenedPairCoefficient_bound Q labels β Γ hΓ hβ b hb C I hI)
    (reopenedCubeFamily_admissible Q)
    (fun b hb=>(reopenedCubeFamily_cube_norms p Q B hQB b hb).1)
    (fun b hb=>(reopenedCubeFamily_cube_norms p Q B hQB b hb).2) hsf hf

end SecondPassArithmetic

open MeasureTheory
open scoped BigOperators Classical SchwartzMap FourierTransform ContDiff

namespace CanonicalCubeSeparation
open FourierBridge JointLogSeparation FirstPassCubeLabels

def columnWindowRadius (a b : ℝ) : ℝ := |Real.log a| + |Real.log b| + 3

lemma columnWindowRadius_nonneg (a b : ℝ) : 0 ≤ columnWindowRadius a b := by
  unfold columnWindowRadius
  positivity

def sourceLogProfile (W : ℝ → ℂ) (a b : ℝ) (ha : 0 < a)
    (hs : Function.support W ⊆ Set.Icc a b) (hW : ContDiff ℝ ∞ W) : 𝓢(ℝ,ℂ) := by
  have hc : HasCompactSupport (fun u : ℝ => W (Real.exp u)) := by
    apply HasCompactSupport.of_support_subset_isCompact
      (K := Set.Icc (Real.log a) (Real.log b)) isCompact_Icc
    intro u hu
    have hm := hs hu
    constructor
    · simpa only [Real.log_exp] using Real.log_le_log ha hm.1
    · simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos u) hm.2
  exact hc.toSchwartzMap (hW.comp Real.contDiff_exp)

@[simp] lemma sourceLogProfile_apply (W : ℝ → ℂ) (a b : ℝ) (ha : 0 < a)
    (hs : Function.support W ⊆ Set.Icc a b) (hW : ContDiff ℝ ∞ W) (u : ℝ) :
    sourceLogProfile W a b ha hs hW u = W (Real.exp u) := rfl

def reopeningCoefficient (W : ℝ → ℂ) (a b : ℝ) (ha : 0 < a)
    (hs : Function.support W ⊆ Set.Icc a b) (hW : ContDiff ℝ ∞ W) : 𝓢(ℝ,ℂ) :=
  𝓕 (sourceLogProfile W a b ha hs hW)

def cubeFrequencyFactor (t ξ : ℝ) : ℂ :=
  (Real.exp (t/2) : ℂ) * logPhase ξ (3*t)

@[simp] lemma cubeFrequencyFactor_norm (t ξ : ℝ) :
    ‖cubeFrequencyFactor t ξ‖ = Real.exp (t/2) := by
  simp only [cubeFrequencyFactor, norm_mul, logPhase_norm, mul_one,
    Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]

lemma cubeFrequencyFactor_bound (t ξ : ℝ) (ht : t ≤ 1) :
    ‖cubeFrequencyFactor t ξ‖ ≤ Real.exp (1/2) := by
  rw [cubeFrequencyFactor_norm]
  exact Real.exp_le_exp.mpr (by linarith)

lemma active_column_window (W : ℝ → ℂ) (a b : ℝ) (ha : 0 < a)
    (hs : Function.support W ⊆ Set.Icc a b) (t u : ℝ)
    (ht : t ∈ Set.Icc (0:ℝ) 1) (hWu : W (Real.exp (u+3*t)) ≠ 0) :
    |u| ≤ columnWindowRadius a b := by
  have hab := hs hWu
  have hlo : Real.log a ≤ u+3*t := by
    simpa only [Real.log_exp] using Real.log_le_log ha hab.1
  have hhi : u+3*t ≤ Real.log b := by
    simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos _) hab.2
  unfold columnWindowRadius
  rw [abs_le]
  constructor <;> linarith [neg_abs_le (Real.log a), le_abs_self (Real.log b),
    abs_nonneg (Real.log a), abs_nonneg (Real.log b), ht.1, ht.2]

lemma reopening_integrable (b V : 𝓢(ℝ,ℂ)) (t u : ℝ) :
    Integrable (fun ξ : ℝ => b ξ * cubeFrequencyFactor t ξ * frequencyTwist V ξ u) := by
  have hi : Integrable (fun ξ : ℝ =>
      b ξ * ((Real.exp (t/2) : ℂ) * logPhase ξ (3*t) * (logPhase ξ u * V u))) := by
    apply b.integrable.mul_bdd (c := Real.exp (t/2) * ‖V u‖)
    · exact (((logPhase_continuous_left (3*t)).const_mul _).mul
        ((logPhase_continuous_left u).mul_const _)).aestronglyMeasurable
    · exact Filter.Eventually.of_forall (fun ξ => by
        simp only [norm_mul, logPhase_norm, Complex.norm_real, Real.norm_eq_abs,
          abs_of_pos (Real.exp_pos _), one_mul, mul_one, le_refl])
  convert hi using 1
  funext ξ
  rw [frequencyTwist_apply]
  unfold cubeFrequencyFactor
  ring

theorem reopening_separation_with_window (W : ℝ → ℂ) (a b : ℝ) (ha : 0 < a)
    (hs : Function.support W ⊆ Set.Icc a b) (hW : ContDiff ℝ ∞ W)
    (V : 𝓢(ℝ,ℂ)) (hV : ∀ u, |u| ≤ columnWindowRadius a b → V u = 1)
    (t u : ℝ) (ht : t ∈ Set.Icc (0:ℝ) 1) :
    (Real.exp (t/2) : ℂ) * W (Real.exp (u+3*t)) =
      ∫ ξ : ℝ, reopeningCoefficient W a b ha hs hW ξ *
        cubeFrequencyFactor t ξ * frequencyTwist V ξ u := by
  have hwindow : V u * W (Real.exp (u+3*t)) = W (Real.exp (u+3*t)) := by
    by_cases hz : W (Real.exp (u+3*t)) = 0
    · simp [hz]
    · rw [hV u (active_column_window W a b ha hs t u ht hz), one_mul]
  have hinv := schwartz_phase_inversion
    (sourceLogProfile W a b ha hs hW) (u+3*t)
  change W (Real.exp (u+3*t)) =
    ∫ ξ : ℝ, logPhase ξ (u+3*t) * reopeningCoefficient W a b ha hs hW ξ at hinv
  calc
    _ = ((Real.exp (t/2) : ℂ) * V u) * W (Real.exp (u+3*t)) := by
      rw [mul_assoc, hwindow]
    _ = ∫ ξ : ℝ, ((Real.exp (t/2) : ℂ) * V u) *
        (logPhase ξ (u+3*t) * reopeningCoefficient W a b ha hs hW ξ) := by
      rw [hinv, integral_const_mul]
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [] with ξ
      rw [logPhase_add, frequencyTwist_apply]
      unfold cubeFrequencyFactor
      ring

theorem exists_reopening_separation (W : ℝ → ℂ) (a b : ℝ) (ha : 0 < a)
    (hs : Function.support W ⊆ Set.Icc a b) (hW : ContDiff ℝ ∞ W) :
    ∃ V : 𝓢(ℝ,ℂ), HasCompactSupport V ∧
      (∀ u, |u| ≤ columnWindowRadius a b → V u = 1) ∧
      (∀ u, V u ≠ 0 → |u| ≤ columnWindowRadius a b + 1) ∧
      (∀ t u : ℝ, t ∈ Set.Icc (0:ℝ) 1 →
        (Real.exp (t/2) : ℂ) * W (Real.exp (u+3*t)) =
          ∫ ξ : ℝ, reopeningCoefficient W a b ha hs hW ξ *
            cubeFrequencyFactor t ξ * frequencyTwist V ξ u) ∧
      (∀ t u : ℝ, Integrable (fun ξ : ℝ => reopeningCoefficient W a b ha hs hW ξ *
          cubeFrequencyFactor t ξ * frequencyTwist V ξ u)) ∧
      (∀ J : ℕ, ∃ C : ℝ, 0 < C ∧
        Integrable (fun ξ : ℝ => (1+‖ξ‖)^J * ‖reopeningCoefficient W a b ha hs hW ξ‖) ∧
        (∫ ξ : ℝ, (1+‖ξ‖)^J * ‖reopeningCoefficient W a b ha hs hW ξ‖) ≤ C ∧
        ∀ ξ : ℝ, ‖reopeningCoefficient W a b ha hs hW ξ‖ ≤ C * firstLogDensity J ξ) := by
  obtain ⟨v,hvc,hvs,hvone,hvsupp,_⟩ := exists_complex_smooth_cutoff
    (columnWindowRadius a b) (columnWindowRadius_nonneg a b)
  let V : 𝓢(ℝ,ℂ) := hvc.toSchwartzMap hvs
  have hVone : ∀ u, |u| ≤ columnWindowRadius a b → V u = 1 := hvone
  refine ⟨V,hvc,hVone,?_,?_,reopening_integrable _ V,?_⟩
  · intro u hu
    have hmem := hvsupp (subset_tsupport v hu)
    exact abs_le.mpr hmem
  · exact fun t u ht => reopening_separation_with_window W a b ha hs hW V hVone t u ht
  · intro J
    let g := sourceLogProfile W a b ha hs hW
    let c := fourierPointBound (J+2) (profileSourceBound g (J+2))
    let m := ∫ ξ : ℝ, (1+‖ξ‖)^J * ‖reopeningCoefficient W a b ha hs hW ξ‖
    have hc : 0 ≤ c := fourierPointBound_nonneg _ _ (profileSourceBound_nonneg _ _)
    have hm : 0 ≤ m := integral_nonneg (fun ξ => by positivity)
    refine ⟨1+c+m,by positivity,weighted_schwartz_integrable _ J,by dsimp [m]; linarith,?_⟩
    intro ξ
    exact (profile_fourier_envelope g J ξ).trans
      (mul_le_mul_of_nonneg_right (by linarith : c ≤ 1+c+m) (firstLogDensity_nonneg J ξ))

end CanonicalCubeSeparation

end

end OAI
