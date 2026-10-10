import Mathlib

namespace OAI

noncomputable section

section

noncomputable section

open scoped Topology ComplexOrder

namespace Kadison.WeakDualHull

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

local instance : AddCommGroup (WeakDual ℂ E) := inferInstanceAs (AddCommGroup (E →L[ℂ] ℂ))

local instance : Module ℝ (WeakDual ℂ E) := inferInstanceAs (Module ℝ (E →L[ℂ] ℂ))

def hull (S : Set (WeakDual ℂ E)) : Set (WeakDual ℂ E) := closure (convexHull ℝ S)

lemma subset_hull (S : Set (WeakDual ℂ E)) : S⊆hull S :=
  (subset_convexHull ℝ S).trans subset_closure

lemma convex_hull (S : Set (WeakDual ℂ E)) : Convex ℝ (hull S) :=
  (convex_convexHull ℝ S).closure

lemma eval_norm_le {S : Set (WeakDual ℂ E)} (a : E) (R : ℝ)
    (h : ∀ f∈S,‖f a‖≤R) {f : WeakDual ℂ E} (hf : f∈hull S) : ‖f a‖≤R := by
  have hc : IsClosed {f : WeakDual ℂ E | ‖f a‖≤R} :=
    isClosed_le (WeakDual.eval_continuous a).norm continuous_const
  have hv : Convex ℝ {f : WeakDual ℂ E | ‖f a‖≤R} := by
    intro g hg k hk s t hs ht hst
    change ‖s • g a+t • k a‖≤R
    calc
      _ ≤ ‖s • g a‖+‖t • k a‖ := norm_add_le _ _
      _ = s*‖g a‖+t*‖k a‖ := by
        rw [norm_smul,norm_smul,Real.norm_eq_abs,Real.norm_eq_abs,
          abs_of_nonneg hs,abs_of_nonneg ht]
      _ ≤ s*R+t*R := add_le_add (mul_le_mul_of_nonneg_left hg hs)
        (mul_le_mul_of_nonneg_left hk ht)
      _ = R := by rw [←add_mul,hst,one_mul]
  exact closure_minimal (convexHull_min h hv) hc hf

lemma norm_le {S : Set (WeakDual ℂ E)} (R : ℝ) (hR : 0≤R)
    (h : ∀ f∈S,‖f.toStrongDual‖≤R) {f : WeakDual ℂ E} (hf : f∈hull S) :
    ‖f.toStrongDual‖≤R := by
  apply ContinuousLinearMap.opNorm_le_bound _ hR
  intro a
  exact eval_norm_le a (R*‖a‖) (fun g hg =>
    (g.toStrongDual.le_opNorm a).trans (mul_le_mul_of_nonneg_right (h g hg) (norm_nonneg a))) hf

lemma compact_hull {S : Set (WeakDual ℂ E)} (R : ℝ) (hR : 0≤R)
    (h : ∀ f∈S,‖f.toStrongDual‖≤R) : IsCompact (hull S) := by
  apply (WeakDual.isCompact_closedBall (0 : StrongDual ℂ E) R).of_isClosed_subset isClosed_closure
  intro f hf
  simpa only [Set.mem_preimage,Metric.mem_closedBall,dist_zero_right] using norm_le R hR h hf

lemma eval_eq {S : Set (WeakDual ℂ E)} (a : E) (c : ℂ)
    (h : ∀ f∈S,f a=c) {f : WeakDual ℂ E} (hf : f∈hull S) : f a=c := by
  have hc : IsClosed {f : WeakDual ℂ E | f a=c} :=
    isClosed_eq (WeakDual.eval_continuous a) continuous_const
  have hv : Convex ℝ {f : WeakDual ℂ E | f a=c} := by
    intro g hg k hk s t _ _ hst
    change (s • g a+t • k a)=c
    rw [hg,hk,←add_smul,hst,one_smul]
  exact closure_minimal (convexHull_min h hv) hc hf

lemma eval_nonneg {S : Set (WeakDual ℂ E)} (a : E)
    (h : ∀ f∈S,0≤f a) {f : WeakDual ℂ E} (hf : f∈hull S) : 0≤f a := by
  have hc : IsClosed {f : WeakDual ℂ E | 0≤f a} :=
    isClosed_le continuous_const (WeakDual.eval_continuous a)
  have hv : Convex ℝ {f : WeakDual ℂ E | 0≤f a} := by
    intro g hg k hk s t hs ht _
    change 0 ≤ s • g a+t • k a
    exact add_nonneg (smul_nonneg hs (show 0≤g a from hg))
      (smul_nonneg ht (show 0≤k a from hk))
  exact closure_minimal (convexHull_min h hv) hc hf

end Kadison.WeakDualHull

end

end
end

end OAI
