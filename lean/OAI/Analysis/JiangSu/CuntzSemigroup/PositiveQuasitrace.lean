import Mathlib
import OAI.Analysis.TracialSplitting.PreparedBlocks
import OAI.Analysis.JiangSu.DimensionFunctions.FiniteSpectralIntegralPositivity

namespace OAI


noncomputable section
namespace Pureness
open TraceCone
open scoped NNReal ENNReal ComplexOrder

structure PositiveQuasitrace (D : Type*) [CStarAlgebra D] [PartialOrder D] [StarOrderedRing D] where
  toFun : Positive D → ℝ
  nonneg : ∀ a, 0 ≤ toFun a
  map_zero : toFun Positive.zero = 0
  map_add_commute : ∀ a b, Commute a.1 b.1 → toFun (Positive.add a b) = toFun a+toFun b
  map_smul : ∀ (r : ℝ≥0) a, toFun (Positive.smul r a) = (r : ℝ)*toFun a
  polar : ∀ x : D, toFun (Positive.starMul x) = toFun (Positive.mulStar x)
  monotone : Monotone toFun

instance {D : Type*} [CStarAlgebra D] [PartialOrder D] [StarOrderedRing D] :
    CoeFun (PositiveQuasitrace D) (fun _ => Positive D → ℝ) := ⟨PositiveQuasitrace.toFun⟩

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

def finiteSpectralPositiveQuasitrace
    (d : finiteCuntzSubmonoid (A := A) →+ ℝ≥0∞) (hd : Monotone d)
    (hlsc : ∀ n, LowerSemicontinuous (fun M : Positive (FinMatrix A n) => d (finitePositiveClass n M)))
    (hfinite : ∀ x, d x ≠ ⊤) (n : ℕ) : PositiveQuasitrace (FinMatrix A n) where
  toFun M := (finiteSpectralIntegral d n M).toReal
  nonneg _ := ENNReal.toReal_nonneg
  map_zero := by rw [finiteSpectralIntegral_zero,ENNReal.toReal_zero]
  map_add_commute M N h := by
    rw [finiteSpectralIntegral_add_commute d hd hlsc hfinite n M N h,
      ENNReal.toReal_add (finiteSpectralIntegral_ne_top d hd n M (hfinite _))
        (finiteSpectralIntegral_ne_top d hd n N (hfinite _))]
  map_smul r M := by rw [finiteSpectralIntegral_smul d hd,ENNReal.toReal_mul,ENNReal.coe_toReal]
  polar x := congrArg ENNReal.toReal (finiteSpectralIntegral_polar d n x)
  monotone := fun M N h => (ENNReal.toReal_le_toReal
    (finiteSpectralIntegral_ne_top d hd n M (hfinite _))
    (finiteSpectralIntegral_ne_top d hd n N (hfinite _))).mpr (finiteSpectralIntegral_monotone d hd n h)

lemma finiteSpectralPositiveQuasitrace_inclusion
    (d : finiteCuntzSubmonoid (A := A) →+ ℝ≥0∞) (hd : Monotone d)
    (hlsc : ∀ n, LowerSemicontinuous (fun M : Positive (FinMatrix A n) => d (finitePositiveClass n M)))
    (hfinite : ∀ x, d x ≠ ⊤) {n m : ℕ} (h : n ≤ m) (M : Positive (FinMatrix A n)) :
    finiteSpectralPositiveQuasitrace d hd hlsc hfinite m (Positive.map (matrixInclusion h) M) =
      finiteSpectralPositiveQuasitrace d hd hlsc hfinite n M :=
  congrArg ENNReal.toReal (finiteSpectralIntegral_inclusion d h M)

lemma finiteSpectralPositiveQuasitrace_root_rank
    (d : finiteCuntzSubmonoid (A := A) →+ ℝ≥0∞) (hd : Monotone d)
    (hlsc : ∀ n, LowerSemicontinuous (fun M : Positive (FinMatrix A n) => d (finitePositiveClass n M)))
    (hfinite : ∀ x, d x ≠ ⊤) (n : ℕ) (M : Positive (FinMatrix A n)) :
    Filter.Tendsto (fun k => ENNReal.ofReal (finiteSpectralPositiveQuasitrace d hd hlsc hfinite n
      (Positive.power (Positive.rootExponent k) M))) Filter.atTop
      (nhds (d (finitePositiveClass n M))) := by
  have he (k : ℕ) : ENNReal.ofReal (finiteSpectralPositiveQuasitrace d hd hlsc hfinite n
      (Positive.power (Positive.rootExponent k) M)) = finiteSpectralIntegral d n (Positive.power (Positive.rootExponent k) M) :=
    ENNReal.ofReal_toReal (finiteSpectralIntegral_ne_top d hd n _ (hfinite _))
  simp only [he]
  exact finiteSpectralIntegral_roots_tendsto d hd hlsc n M

end Pureness
end


noncomputable section
namespace Pureness
open TraceCone
open scoped NNReal ENNReal ComplexOrder

variable {D : Type*} [CStarAlgebra D] [PartialOrder D] [StarOrderedRing D]

omit [PartialOrder D] [StarOrderedRing D] in
lemma commute_posPart_left {a b : D} (h : Commute a b) : Commute a⁺ b := h.cfcₙ_real _
omit [PartialOrder D] [StarOrderedRing D] in
lemma commute_negPart_left {a b : D} (h : Commute a b) : Commute a⁻ b := h.cfcₙ_real _
omit [PartialOrder D] [StarOrderedRing D] in
lemma commute_posPart_right {a b : D} (h : Commute a b) : Commute a b⁺ := (commute_posPart_left h.symm).symm
omit [PartialOrder D] [StarOrderedRing D] in
lemma commute_negPart_right {a b : D} (h : Commute a b) : Commute a b⁻ := (commute_negPart_left h.symm).symm

namespace PositiveQuasitrace
variable (T : PositiveQuasitrace D)

def selfAdjointValue (a : selfAdjoint D) : ℝ :=
  T ⟨a.1⁺,CFC.posPart_nonneg _⟩ - T ⟨a.1⁻,CFC.negPart_nonneg _⟩

lemma selfAdjointValue_sub (a : selfAdjoint D) (p q : Positive D)
    (hpq : a.1 = p.1-q.1) (hcomm : Commute p.1 q.1) :
    T.selfAdjointValue a = T p-T q := by
  have hb : Positive.add ⟨a.1⁺,CFC.posPart_nonneg _⟩ q =
      Positive.add p ⟨a.1⁻,CFC.negPart_nonneg _⟩ := by
    apply Subtype.ext
    exact sub_eq_sub_iff_add_eq_add.mp ((CFC.posPart_sub_negPart a.1 a.2).trans hpq)
  have haq : Commute a.1 q.1 := by rw [hpq]; exact hcomm.sub_left (Commute.refl _)
  have hap : Commute a.1 p.1 := by rw [hpq]; exact (Commute.refl _).sub_left hcomm.symm
  have hv := congrArg T.toFun hb
  rw [T.map_add_commute _ _ (commute_posPart_left haq),
    T.map_add_commute _ _ (commute_negPart_left hap).symm] at hv
  unfold selfAdjointValue
  linarith

lemma selfAdjointValue_add (a b : selfAdjoint D) (h : Commute a.1 b.1) :
    T.selfAdjointValue (a+b) = T.selfAdjointValue a+T.selfAdjointValue b := by
  let p := Positive.add (⟨a.1⁺,CFC.posPart_nonneg _⟩ : Positive D) ⟨b.1⁺,CFC.posPart_nonneg _⟩
  let q := Positive.add (⟨a.1⁻,CFC.negPart_nonneg _⟩ : Positive D) ⟨b.1⁻,CFC.negPart_nonneg _⟩
  have hrep : (a+b).1 = p.1-q.1 := by
    change a.1+b.1 = (a.1⁺+b.1⁺)-(a.1⁻+b.1⁻)
    rw [add_sub_add_comm,CFC.posPart_sub_negPart _ a.2,CFC.posPart_sub_negPart _ b.2]
  have hpq : Commute p.1 q.1 :=
    ((commute_negPart_right (commute_posPart_left (Commute.refl a.1))).add_right
      (commute_negPart_right (commute_posPart_left h))).add_left
    ((commute_negPart_right (commute_posPart_left h.symm)).add_right
      (commute_negPart_right (commute_posPart_left (Commute.refl b.1))))
  rw [T.selfAdjointValue_sub (a+b) p q hrep hpq]
  dsimp [p,q]
  rw [T.map_add_commute _ _ (commute_posPart_right (commute_posPart_left h)),
    T.map_add_commute _ _ (commute_negPart_right (commute_negPart_left h))]
  unfold selfAdjointValue
  ring

lemma selfAdjointValue_smul_nonneg (r : ℝ≥0) (a : selfAdjoint D) :
    T.selfAdjointValue ((r : ℝ) • a) = (r : ℝ)*T.selfAdjointValue a := by
  have he := T.selfAdjointValue_sub ((r : ℝ) • a)
    (Positive.smul r ⟨a.1⁺,CFC.posPart_nonneg _⟩)
    (Positive.smul r ⟨a.1⁻,CFC.negPart_nonneg _⟩) (by
      change (r : ℝ) • a.1 = (r : ℝ) • a.1⁺-(r : ℝ) • a.1⁻
      rw [← smul_sub,CFC.posPart_sub_negPart _ a.2])
    (((commute_negPart_right (commute_posPart_left (Commute.refl a.1))).smul_left (r : ℝ)).smul_right (r : ℝ))
  rw [he,T.map_smul,T.map_smul]
  unfold selfAdjointValue
  ring

lemma selfAdjointValue_neg (a : selfAdjoint D) : T.selfAdjointValue (-a) = -T.selfAdjointValue a := by
  unfold selfAdjointValue
  change T ⟨(-a.1)⁺,_⟩-T ⟨(-a.1)⁻,_⟩ = -(T ⟨a.1⁺,_⟩-T ⟨a.1⁻,_⟩)
  simp only [CFC.posPart_neg,CFC.negPart_neg]
  ring

lemma selfAdjointValue_smul (r : ℝ) (a : selfAdjoint D) :
    T.selfAdjointValue (r • a) = r*T.selfAdjointValue a := by
  by_cases hr : 0 ≤ r
  · exact T.selfAdjointValue_smul_nonneg ⟨r,hr⟩ a
  · have he := T.selfAdjointValue_smul_nonneg ⟨-r,by linarith⟩ a
    change T.selfAdjointValue ((-r) • a) = (-r)*T.selfAdjointValue a at he
    rw [neg_smul,T.selfAdjointValue_neg] at he
    linarith

lemma selfAdjointValue_positive (a : Positive D) :
    T.selfAdjointValue ⟨a.1,a.2.isSelfAdjoint⟩ = T a := by
  have he := T.selfAdjointValue_sub ⟨a.1,a.2.isSelfAdjoint⟩ a Positive.zero
    (by simp [Positive.zero]) (Commute.zero_right _)
  simpa only [T.map_zero,sub_zero] using he

lemma selfAdjointValue_zero : T.selfAdjointValue 0 = 0 := by
  exact (T.selfAdjointValue_positive Positive.zero).trans T.map_zero

end PositiveQuasitrace
end Pureness
end


noncomputable section
namespace Pureness
open TraceCone
open scoped NNReal ENNReal ComplexOrder ComplexStarModule IsMulCommutative

variable {D : Type*} [CStarAlgebra D] [PartialOrder D] [StarOrderedRing D]
namespace PositiveQuasitrace
variable (T : PositiveQuasitrace D)

def complexValue (x : D) : ℂ :=
  (T.selfAdjointValue (ℜ x) : ℂ) + Complex.I*(T.selfAdjointValue (ℑ x) : ℂ)

lemma complexValue_selfAdjoint (a : selfAdjoint D) :
    T.complexValue a.1 = (T.selfAdjointValue a : ℂ) := by
  have hr : ℜ a.1 = a := Subtype.ext a.2.coe_realPart
  simp only [complexValue,hr,a.2.imaginaryPart,T.selfAdjointValue_zero,Complex.ofReal_zero,mul_zero,add_zero]

lemma complexValue_positive (a : Positive D) : T.complexValue a.1 = (T a : ℂ) := by
  rw [T.complexValue_selfAdjoint ⟨a.1,a.2.isSelfAdjoint⟩,T.selfAdjointValue_positive]

lemma complexValue_polar (x : D) : T.complexValue (star x*x) = T.complexValue (x*star x) := by
  exact (T.complexValue_positive (Positive.starMul x)).trans
    ((congrArg Complex.ofReal (T.polar x)).trans (T.complexValue_positive (Positive.mulStar x)).symm)

lemma complexValue_square_nonneg (x : D) : 0 ≤ T.complexValue (star x*x) := by
  change 0 ≤ T.complexValue (Positive.starMul x).1
  rw [T.complexValue_positive]
  exact_mod_cast T.nonneg (Positive.starMul x)

lemma complexValue_real_add_I (a b : selfAdjoint D) :
    T.complexValue (a.1+Complex.I • b.1) = T.complexValue a.1+Complex.I*T.complexValue b.1 := by
  rw [T.complexValue_selfAdjoint a,T.complexValue_selfAdjoint b]
  unfold complexValue
  have hr : ℜ (a.1+Complex.I • b.1) = a := by
    apply Subtype.ext
    simp [_root_.map_add,realPart_smul,b.2.imaginaryPart]
  have hi : ℑ (a.1+Complex.I • b.1) = b := by
    apply Subtype.ext
    simp [_root_.map_add,imaginaryPart_smul,a.2.imaginaryPart,b.2.imaginaryPart]
  rw [hr,hi]

def subalgebraSelfAdjointMap (S : StarSubalgebra ℂ D) : selfAdjoint S →ₗ[ℝ] selfAdjoint D where
  toFun a := ⟨a.1.1,congrArg Subtype.val a.2⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def subalgebraRealLinear (S : StarSubalgebra ℂ D) [IsMulCommutative S] : selfAdjoint S →ₗ[ℝ] ℝ where
  toFun a := T.selfAdjointValue (subalgebraSelfAdjointMap S a)
  map_add' a b := by
    rw [map_add,T.selfAdjointValue_add]
    exact congrArg Subtype.val (mul_comm a.1 b.1)
  map_smul' r a := by
    rw [_root_.map_smul,T.selfAdjointValue_smul]
    rfl

def subalgebraComplexLinear (S : StarSubalgebra ℂ D) [IsMulCommutative S] : S →ₗ[ℂ] ℂ where
  toFun x := (T.subalgebraRealLinear S (ℜ x) : ℂ)+Complex.I*(T.subalgebraRealLinear S (ℑ x) : ℂ)
  map_add' x y := by simp only [map_add,Complex.ofReal_add]; ring
  map_smul' z x := by
    simp only [realPart_smul,imaginaryPart_smul,map_sub,map_add,_root_.map_smul,
      RingHom.id_apply,smul_eq_mul,Complex.ofReal_sub,Complex.ofReal_add,Complex.ofReal_mul]
    apply Complex.ext <;> simp

lemma subalgebraComplexLinear_eq (S : StarSubalgebra ℂ D) [IsMulCommutative S] (x : S) :
    T.subalgebraComplexLinear S x = T.complexValue x.1 := by
  rfl

end PositiveQuasitrace
end Pureness
end

end OAI
