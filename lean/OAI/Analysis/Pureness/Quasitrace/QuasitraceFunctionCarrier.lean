import OAI.Analysis.Pureness.Quasitrace.ComplexQuasitraceBounds
import Mathlib.Analysis.Convex.Function

namespace OAI
noncomputable section
namespace CuntzPureness
open scoped ComplexOrder ComplexStarModule IsMulCommutative
variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

def complexQuasitraceCarrier : Set (A → ℂ) :=
  {f | (∀ x, f (star x * x) = f (x * star x)) ∧
    (∀ x, 0 ≤ f (star x * x)) ∧
    (∀ a b : selfAdjoint A, f (a.1 + Complex.I • b.1) = f a.1 + Complex.I * f b.1) ∧
    (∀ (S : NonUnitalStarSubalgebra ℂ A) (_ : IsMulCommutative S) (x y : S),
      f (x.1 + y.1) = f x.1 + f y.1) ∧
    (∀ (S : NonUnitalStarSubalgebra ℂ A) (_ : IsMulCommutative S) (c : ℂ) (x : S),
      f (c • x.1) = c * f x.1)}

omit [PartialOrder A] [StarOrderedRing A] in
lemma ComplexQuasitrace.mem_carrier (T : ComplexQuasitrace A) :
    T.toFun ∈ complexQuasitraceCarrier := by
  refine ⟨T.polar, T.square_nonneg, T.real_add_I, ?_, ?_⟩
  · intro S hS x y
    obtain ⟨f, hf⟩ := T.abelian_linear S
    have h := f.map_add x y
    simp only [hf] at h
    exact h
  · intro S hS c x
    obtain ⟨f, hf⟩ := T.abelian_linear S
    have h := f.map_smul c x
    simp only [hf, smul_eq_mul] at h
    exact h

def complexQuasitraceFromCarrier (f : A → ℂ) (hf : f ∈ complexQuasitraceCarrier) :
    ComplexQuasitrace A where
  toFun := f
  polar := hf.1
  square_nonneg := hf.2.1
  real_add_I := hf.2.2.1
  abelian_linear S hS := ⟨{
    toFun := fun x => f x.1
    map_add' := hf.2.2.2.1 S hS
    map_smul' := fun c x => hf.2.2.2.2 S hS c x }, fun _ => rfl⟩

omit [PartialOrder A] [StarOrderedRing A] in
lemma range_complexQuasitrace_toFun :
    Set.range (ComplexQuasitrace.toFun (D := A)) = complexQuasitraceCarrier := by
  ext f
  exact ⟨fun ⟨T, hT⟩ => hT ▸ T.mem_carrier,
    fun hf => ⟨complexQuasitraceFromCarrier f hf, rfl⟩⟩

lemma isClosed_forall_pointwise {X : Type*} [TopologicalSpace X] {ι : Sort*}
    (P : ι → X → Prop) (hP : ∀ i, IsClosed {x | P i x}) :
    IsClosed {x | ∀ i, P i x} := by
  simpa only [Set.ofPred_forall] using isClosed_iInter hP

omit [PartialOrder A] [StarOrderedRing A] in
lemma isClosed_complexQuasitraceCarrier : IsClosed (complexQuasitraceCarrier (A := A)) := by
  unfold complexQuasitraceCarrier
  refine IsClosed.inter ?_ (IsClosed.inter ?_ (IsClosed.inter ?_ (IsClosed.inter ?_ ?_)))
  · exact isClosed_forall_pointwise _ fun x =>
      isClosed_eq (continuous_apply (star x * x)) (continuous_apply (x * star x))
  · exact isClosed_forall_pointwise _ fun x =>
      isClosed_le continuous_const (continuous_apply (star x * x))
  · exact isClosed_forall_pointwise _ fun a => isClosed_forall_pointwise _ fun b =>
      isClosed_eq (continuous_apply _) ((continuous_apply a.1).add (continuous_const.mul (continuous_apply b.1)))
  · exact isClosed_forall_pointwise _ fun S => isClosed_forall_pointwise _ fun _ =>
      isClosed_forall_pointwise _ fun x => isClosed_forall_pointwise _ fun y =>
      isClosed_eq (continuous_apply _) ((continuous_apply x.1).add (continuous_apply y.1))
  · exact isClosed_forall_pointwise _ fun S => isClosed_forall_pointwise _ fun _ =>
      isClosed_forall_pointwise _ fun c => isClosed_forall_pointwise _ fun x =>
      isClosed_eq (continuous_apply _) (continuous_const.mul (continuous_apply _))

omit [PartialOrder A] [StarOrderedRing A] in
lemma convex_complexQuasitraceCarrier : Convex ℝ (complexQuasitraceCarrier (A := A)) := by
  intro f hf g hg a b ha hb hab
  change (fun x => (a : ℂ) * f x + (b : ℂ) * g x) ∈ complexQuasitraceCarrier
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro x
    dsimp only
    rw [hf.1, hg.1]
  · intro x
    exact add_nonneg (mul_nonneg (by exact_mod_cast ha) (hf.2.1 x))
      (mul_nonneg (by exact_mod_cast hb) (hg.2.1 x))
  · intro x y
    dsimp only
    rw [hf.2.2.1, hg.2.2.1]
    ring
  · intro S hS x y
    dsimp only
    rw [hf.2.2.2.1 S hS x y, hg.2.2.2.1 S hS x y]
    ring
  · intro S hS c x
    dsimp only
    rw [hf.2.2.2.2 S hS c x, hg.2.2.2.2 S hS c x]
    ring
end CuntzPureness

end

end OAI
