import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Topology.Instances.ENNReal.Lemmas
import Mathlib.Topology.Semicontinuity.Basic

namespace OAI
noncomputable section
open scoped ENNReal NNReal
namespace CuntzTrace
variable (A : Type*) [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
abbrev Positive := {a : A // 0 ≤ a}
namespace Positive
variable {A}
def zero : Positive A := ⟨0, le_rfl⟩
def add (a b : Positive A) : Positive A := ⟨a.1 + b.1, add_nonneg a.2 b.2⟩
def smul (r : ℝ≥0) (a : Positive A) : Positive A :=
  ⟨(r : ℝ) • a.1, smul_nonneg r.2 a.2⟩
def starMul (x : A) : Positive A := ⟨star x * x, star_mul_self_nonneg x⟩
def mulStar (x : A) : Positive A := ⟨x * star x, mul_star_self_nonneg x⟩
def sum {ι : Type*} (s : Finset ι) (a : ι → Positive A) : Positive A :=
  ⟨∑ i ∈ s, (a i).1, Finset.sum_nonneg fun i _ => (a i).2⟩
end Positive

structure ExtendedTrace where
  toFun : Positive A → ℝ≥0∞
  map_zero : toFun (Positive.zero) = 0
  map_add (a b : Positive A) : toFun (Positive.add a b) = toFun a + toFun b
  map_smul (r : ℝ≥0) (a : Positive A) :
    toFun (Positive.smul r a) = (r : ℝ≥0∞) * toFun a
  tracial (x : A) : toFun (Positive.starMul x) = toFun (Positive.mulStar x)
  lowerSemicontinuous : LowerSemicontinuous toFun

namespace ExtendedTrace
variable {A}
instance : CoeFun (ExtendedTrace A) (fun _ => Positive A → ℝ≥0∞) := ⟨toFun⟩

@[ext] theorem ext {τ σ : ExtendedTrace A} (h : ∀ a, τ a = σ a) : τ = σ := by
  cases τ
  cases σ
  congr
  exact funext h

instance : Zero (ExtendedTrace A) := ⟨{
  toFun := fun _ => 0
  map_zero := rfl
  map_add := fun _ _ => (zero_add 0).symm
  map_smul := fun _ _ => (mul_zero _).symm
  tracial := fun _ => rfl
  lowerSemicontinuous := lowerSemicontinuous_const }⟩

instance : Add (ExtendedTrace A) := ⟨fun τ σ => {
  toFun := fun a => τ a + σ a
  map_zero := by rw [τ.map_zero, σ.map_zero, add_zero]
  map_add := by
    intro a b
    rw [τ.map_add, σ.map_add]
    ac_rfl
  map_smul := by
    intro r a
    rw [τ.map_smul, σ.map_smul, mul_add]
  tracial := by
    intro x
    rw [τ.tracial, σ.tracial]
  lowerSemicontinuous := τ.lowerSemicontinuous.add σ.lowerSemicontinuous }⟩

@[simp] theorem zero_apply (a : Positive A) : (0 : ExtendedTrace A) a = 0 := rfl
@[simp] theorem add_apply (τ σ : ExtendedTrace A) (a : Positive A) :
    (τ + σ) a = τ a + σ a := rfl

instance : AddCommMonoid (ExtendedTrace A) where
  add_assoc a b c := ext fun x => add_assoc (a x) (b x) (c x)
  zero_add a := ext fun x => zero_add (a x)
  add_zero a := ext fun x => add_zero (a x)
  add_comm a b := ext fun x => add_comm (a x) (b x)
  nsmul := nsmulRec

theorem monotone (τ : ExtendedTrace A) : Monotone (fun a : Positive A => τ a) := by
  intro a b hab
  change τ a ≤ τ b
  let c : Positive A := ⟨b.1 - a.1, sub_nonneg.mpr hab⟩
  have heq : Positive.add a c = b := Subtype.ext (add_sub_cancel _ _)
  have h := τ.map_add a c
  rw [heq] at h
  rw [h]
  exact le_self_add

theorem zero_of_le (τ : ExtendedTrace A) {a b : Positive A} (hab : a ≤ b)
    (hb : τ b = 0) : τ a = 0 := by
  apply le_antisymm _ bot_le
  simpa [hb] using τ.monotone hab

theorem map_sum (τ : ExtendedTrace A) {ι : Type*} (s : Finset ι)
    (a : ι → Positive A) : τ (Positive.sum s a) = ∑ i ∈ s, τ (a i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa [Positive.sum, Positive.zero] using τ.map_zero
  | @insert i s hi ih =>
    have hs : Positive.sum (insert i s) a = Positive.add (a i) (Positive.sum s a) := by
      apply Subtype.ext
      simp [Positive.sum, Positive.add, hi]
    rw [hs, τ.map_add, ih, Finset.sum_insert hi]

theorem finite_positive_partition (τ : ExtendedTrace A) {ι : Type*}
    (s : Finset ι) (y : ι → A) (a b : Positive A)
    (ha : ∑ i ∈ s, star (y i) * y i = a.1)
    (hb : ∑ i ∈ s, y i * star (y i) = b.1) : τ a = τ b := by
  have ha' : Positive.sum s (fun i => Positive.starMul (y i)) = a := Subtype.ext ha
  have hb' : Positive.sum s (fun i => Positive.mulStar (y i)) = b := Subtype.ext hb
  rw [← ha', ← hb', τ.map_sum, τ.map_sum]
  exact Finset.sum_congr rfl fun i _ => τ.tracial (y i)

end ExtendedTrace
end CuntzTrace

end

end OAI
