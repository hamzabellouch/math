import Mathlib

namespace OAI

noncomputable section
open Filter Topology Classical
open scoped NNReal ENNReal

namespace TraceConeClassification
variable (A : Type*) [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

abbrev Positive := {a : A // 0 ≤ a}

namespace Positive
variable {A}
def zero : Positive A := ⟨0, le_rfl⟩
def add (a b : Positive A) : Positive A := ⟨a.1 + b.1, add_nonneg a.2 b.2⟩
def scale (r : ℝ≥0) (a : Positive A) : Positive A :=
  ⟨(r : ℝ) • a.1, smul_nonneg r.2 a.2⟩
def starMul (x : A) : Positive A := ⟨star x * x, star_mul_self_nonneg x⟩
def mulStar (x : A) : Positive A := ⟨x * star x, mul_star_self_nonneg x⟩
def cut (a : Positive A) (ε : ℝ≥0) : Positive A :=
  ⟨cfcₙ (fun t : ℝ => max (t - (ε : ℝ)) 0) a.1,
    cfcₙ_nonneg (fun _ _ => le_max_right _ _)⟩
end Positive

structure ExtendedTrace where
  toFun : Positive A → ℝ≥0∞
  map_zero : toFun Positive.zero = 0
  map_add : ∀ a b, toFun (Positive.add a b) = toFun a + toFun b
  map_scale : ∀ (r : ℝ≥0), 0 < r → ∀ a,
    toFun (Positive.scale r a) = (r : ℝ≥0∞) * toFun a
  tracial : ∀ x : A, toFun (Positive.starMul x) = toFun (Positive.mulStar x)
  lowerSemicontinuous : LowerSemicontinuous toFun

instance : CoeFun (ExtendedTrace A) (fun _ => Positive A → ℝ≥0∞) :=
  ⟨ExtendedTrace.toFun⟩

def CanonicalConvergence {ι : Type*} (l : Filter ι) (τ : ι → ExtendedTrace A)
    (σ : ExtendedTrace A) : Prop :=
  ∀ (a : Positive A) (ε : ℝ≥0), 0 < ε →
    Filter.limsup (fun i => τ i (Positive.cut a ε)) l ≤ σ a ∧
    σ a ≤ Filter.liminf (fun i => τ i a) l

variable {A}
namespace ExtendedTrace

def scale (r : ℝ≥0) (τ : ExtendedTrace A) : ExtendedTrace A where
  toFun a := (r : ℝ≥0∞) * τ a
  map_zero := by rw [τ.map_zero, mul_zero]
  map_add a b := by rw [τ.map_add, mul_add]
  map_scale s hs a := by rw [τ.map_scale s hs]; ac_rfl
  tracial x := by rw [τ.tracial x]
  lowerSemicontinuous :=
    (ENNReal.continuous_const_mul ENNReal.coe_ne_top).comp_lowerSemicontinuous
      τ.lowerSemicontinuous (fun _ _ h => mul_le_mul_of_nonneg_left h bot_le)

end ExtendedTrace

-- The proof obligations below make the ideal and equivalence constructions well typed.
theorem closed_ideal_weight_exists
    (I : NonUnitalStarSubalgebra ℂ A) (hI : IsClosed (I : Set A))
    (hleft : ∀ (x y : A), y ∈ I → x * y ∈ I)
    (hright : ∀ (x y : A), x ∈ I → x * y ∈ I) :
    ∃ τ : ExtendedTrace A, ∀ a : Positive A, τ a = if a.1 ∈ I then 0 else ∞ := by
  sorry

namespace ExtendedTrace
variable (τ : ExtendedTrace A)
def finiteSquareSet : Set A := {x | τ (Positive.starMul x) < ∞}
lemma zero_mem_finiteSquareSet : (0 : A) ∈ τ.finiteSquareSet := by sorry
lemma star_mem_finiteSquareSet {x : A} (hx : x ∈ τ.finiteSquareSet) :
    star x ∈ τ.finiteSquareSet := by sorry
lemma smul_mem_finiteSquareSet (c : ℂ) {x : A} (hx : x ∈ τ.finiteSquareSet) :
    c • x ∈ τ.finiteSquareSet := by sorry
lemma add_mem_finiteSquareSet {x y : A}
    (hx : x ∈ τ.finiteSquareSet) (hy : y ∈ τ.finiteSquareSet) :
    x + y ∈ τ.finiteSquareSet := by sorry
lemma mul_mem_finiteSquareSet_left (x : A) {y : A} (hy : y ∈ τ.finiteSquareSet) :
    x * y ∈ τ.finiteSquareSet := by sorry

def finiteSquareAlgebra : NonUnitalStarSubalgebra ℂ A where
  carrier := τ.finiteSquareSet
  zero_mem' := τ.zero_mem_finiteSquareSet
  add_mem' := τ.add_mem_finiteSquareSet
  smul_mem' := τ.smul_mem_finiteSquareSet
  mul_mem' := fun _ hy => τ.mul_mem_finiteSquareSet_left _ hy
  star_mem' := τ.star_mem_finiteSquareSet

def finiteIdeal : NonUnitalStarSubalgebra ℂ A := τ.finiteSquareAlgebra.topologicalClosure
lemma isClosed_finiteIdeal : IsClosed (τ.finiteIdeal : Set A) := by sorry
lemma mul_mem_finiteIdeal_left (x : A) {y : A} (hy : y ∈ τ.finiteIdeal) :
    x * y ∈ τ.finiteIdeal := by sorry
lemma mul_mem_finiteIdeal_right {x : A} (hx : x ∈ τ.finiteIdeal) (y : A) :
    x * y ∈ τ.finiteIdeal := by sorry
end ExtendedTrace

end TraceConeClassification

namespace TraceConeClassification
universe u v
variable {A : Type u} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

namespace ExtendedTrace
def add (τ σ : ExtendedTrace A) : ExtendedTrace A where
  toFun a := τ a + σ a
  map_zero := by rw [τ.map_zero, σ.map_zero, add_zero]
  map_add a b := by rw [τ.map_add, σ.map_add]; ac_rfl
  map_scale r hr a := by rw [τ.map_scale r hr, σ.map_scale r hr, mul_add]
  tracial x := by rw [τ.tracial x, σ.tracial x]
  lowerSemicontinuous := τ.lowerSemicontinuous.add σ.lowerSemicontinuous

def zero : ExtendedTrace A where
  toFun _ := 0
  map_zero := rfl
  map_add _ _ := (add_zero _).symm
  map_scale _ _ _ := (mul_zero _).symm
  tracial _ := rfl
  lowerSemicontinuous := lowerSemicontinuous_const

end ExtendedTrace

def ClosedIdeal (A : Type u) [NonUnitalCStarAlgebra A] [PartialOrder A]
    [StarOrderedRing A] :=
  {I : NonUnitalStarSubalgebra ℂ A // IsClosed (I : Set A) ∧
    (∀ (x y : A), y ∈ I → x * y ∈ I) ∧ (∀ (x y : A), x ∈ I → x * y ∈ I)}

namespace ExtendedTrace

def finIdeal (τ : ExtendedTrace A) : ClosedIdeal A :=
  ⟨τ.finiteIdeal, τ.isClosed_finiteIdeal, fun x _ hy => τ.mul_mem_finiteIdeal_left x hy,
    fun _ y hx => τ.mul_mem_finiteIdeal_right hx y⟩

lemma lowerSemicontinuous_supportWeight (τ : ExtendedTrace A) :
    LowerSemicontinuous (fun a : Positive A => if τ a = 0 then (0 : ℝ≥0∞) else ∞) := by sorry

def supportWeight (τ : ExtendedTrace A) : ExtendedTrace A where
  toFun a := if τ a = 0 then 0 else ∞
  map_zero := by simp [τ.map_zero]
  map_add a b := by
    rw [τ.map_add]
    by_cases ha : τ a = 0 <;> by_cases hb : τ b = 0 <;> simp [ha, hb]
  map_scale r hr a := by
    rw [τ.map_scale r hr]
    by_cases ha : τ a = 0 <;> simp [ha, ENNReal.coe_ne_zero.mpr hr.ne']
  tracial x := by rw [τ.tracial x]
  lowerSemicontinuous := τ.lowerSemicontinuous_supportWeight

def zeroIdeal (τ : ExtendedTrace A) : ClosedIdeal A := τ.supportWeight.finIdeal
end ExtendedTrace


namespace ClosedIdeal
instance : PartialOrder (ClosedIdeal A) := inferInstanceAs (PartialOrder (Subtype _))
def weight (I : ClosedIdeal A) : ExtendedTrace A :=
  (closed_ideal_weight_exists I.1 I.2.1 I.2.2.1 I.2.2.2).choose
theorem weight_idempotent (I : ClosedIdeal A) : I.weight.add I.weight = I.weight := by sorry
theorem finiteIdeal_weight (I : ClosedIdeal A) : I.weight.finiteIdeal = I.1 := by sorry
theorem le_iff_add_weight (I J : ClosedIdeal A) :
    I ≤ J ↔ I.weight.add J.weight = I.weight := by sorry
end ClosedIdeal

namespace ExtendedTrace
theorem idempotent_eq_weight {τ : ExtendedTrace A} (hτ : τ.add τ = τ) :
    τ.finIdeal.weight = τ := by sorry
end ExtendedTrace

def IdempotentTrace (A : Type u) [NonUnitalCStarAlgebra A] [PartialOrder A]
    [StarOrderedRing A] := {τ : ExtendedTrace A // τ.add τ = τ}

def closedIdealEquivIdempotent : ClosedIdeal A ≃ IdempotentTrace A where
  toFun I := ⟨I.weight, I.weight_idempotent⟩
  invFun τ := τ.1.finIdeal
  left_inv I := Subtype.ext (ClosedIdeal.finiteIdeal_weight I)
  right_inv τ := Subtype.ext (ExtendedTrace.idempotent_eq_weight τ.2)

variable {B : Type v} [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]

def idempotentTraceEquiv (e : ExtendedTrace A ≃ ExtendedTrace B)
    (he : ∀ τ σ, e (τ.add σ) = (e τ).add (e σ)) : IdempotentTrace A ≃ IdempotentTrace B where
  toFun τ := ⟨e τ.1, by rw [← he, τ.2]⟩
  invFun σ := ⟨e.symm σ.1, by
    apply e.injective
    rw [he, e.apply_symm_apply, σ.2]⟩
  left_inv τ := Subtype.ext (e.symm_apply_apply τ.1)
  right_inv σ := Subtype.ext (e.apply_symm_apply σ.1)

def closedIdealEquivOfAdditive (e : ExtendedTrace A ≃ ExtendedTrace B)
    (he : ∀ τ σ, e (τ.add σ) = (e τ).add (e σ)) : ClosedIdeal A ≃ ClosedIdeal B :=
  closedIdealEquivIdempotent.trans ((idempotentTraceEquiv e he).trans
    closedIdealEquivIdempotent.symm)

lemma closedIdealEquivOfAdditive_weight (e : ExtendedTrace A ≃ ExtendedTrace B)
    (he : ∀ τ σ, e (τ.add σ) = (e τ).add (e σ)) (I : ClosedIdeal A) :
    (closedIdealEquivOfAdditive e he I).weight = e I.weight := by sorry

def closedIdealOrderEquivOfAdditive (e : ExtendedTrace A ≃ ExtendedTrace B)
    (he : ∀ τ σ, e (τ.add σ) = (e τ).add (e σ)) : ClosedIdeal A ≃o ClosedIdeal B where
  toEquiv := closedIdealEquivOfAdditive e he
  map_rel_iff' := by
    intro I J
    rw [ClosedIdeal.le_iff_add_weight, ClosedIdeal.le_iff_add_weight,
      closedIdealEquivOfAdditive_weight, closedIdealEquivOfAdditive_weight, ← he]
    exact e.injective.eq_iff

def PreservesCanonicalConvergence (f : ExtendedTrace A → ExtendedTrace B) : Prop :=
  ∀ (l : Filter (ExtendedTrace A)) (σ : ExtendedTrace A),
    CanonicalConvergence A l id σ → CanonicalConvergence B l f (f σ)

structure TraceConeEquiv (A : Type u) [NonUnitalCStarAlgebra A] [PartialOrder A]
    [StarOrderedRing A] (B : Type v) [NonUnitalCStarAlgebra B] [PartialOrder B]
    [StarOrderedRing B] where
  toEquiv : ExtendedTrace A ≃ ExtendedTrace B
  map_add : ∀ τ σ, toEquiv (τ.add σ) = (toEquiv τ).add (toEquiv σ)
  map_zero : toEquiv ExtendedTrace.zero = ExtendedTrace.zero
  map_scale : ∀ (r : ℝ≥0), 0 < r → ∀ τ, toEquiv (τ.scale r) = (toEquiv τ).scale r
  continuous_toFun : PreservesCanonicalConvergence toEquiv
  continuous_invFun : PreservesCanonicalConvergence toEquiv.symm

namespace TraceConeEquiv
variable (F : TraceConeEquiv A B)
def idealOrderIso : ClosedIdeal A ≃o ClosedIdeal B :=
  closedIdealOrderEquivOfAdditive F.toEquiv F.map_add

theorem idealOrderIso_finIdeal (τ : ExtendedTrace A) :
    F.idealOrderIso τ.finIdeal = (F.toEquiv τ).finIdeal := by
  sorry

theorem idealOrderIso_zeroIdeal (τ : ExtendedTrace A) :
    F.idealOrderIso τ.zeroIdeal = (F.toEquiv τ).zeroIdeal := by
  sorry

end TraceConeEquiv
end TraceConeClassification
end

end OAI
