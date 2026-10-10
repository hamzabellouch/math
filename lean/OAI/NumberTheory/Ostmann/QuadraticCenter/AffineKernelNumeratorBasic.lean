import OAI.NumberTheory.Ostmann.QuadraticCenter.BiasSelectionWindows
import OAI.NumberTheory.Ostmann.QuadraticCenter.KernelFunctions

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.QuadraticCenter
open Ostmann.Preliminaries

theorem positiveIntegerWindow_int_bounds {S : Set ℕ} {X : ℕ} {x : ℤ}
    (hx : x∈positiveIntegerWindow S X) : 0≤x ∧ x≤(X:ℤ) := by
  obtain ⟨n,hn,rfl⟩ := Finset.mem_map.mp hx
  change 0≤(n:ℤ) ∧ (n:ℤ)≤(X:ℤ)
  exact ⟨Nat.cast_nonneg n,by exact_mod_cast (mem_upperWindow.mp hn).2.1⟩

theorem negativeIntegerWindow_int_bounds {S : Set ℕ} {X : ℕ} {x : ℤ}
    (hx : x∈negativeIntegerWindow S X) : -(X:ℤ)≤x ∧ x≤0 := by
  obtain ⟨n,hn,rfl⟩ := Finset.mem_map.mp hx
  change -(X:ℤ)≤-(n:ℤ) ∧ -(n:ℤ)≤0
  exact ⟨neg_le_neg (by exact_mod_cast (mem_upperWindow.mp hn).2.1),
    neg_nonpos.mpr (Nat.cast_nonneg n)⟩

theorem integerWindows_natAbs_le {A B : Set ℕ} {X : ℕ} {x : ℤ}
    (hx : x∈positiveIntegerWindow A X∪negativeIntegerWindow B X) : x.natAbs≤X := by
  have hb : -(X:ℤ)≤x ∧ x≤(X:ℤ) := by
    rcases Finset.mem_union.mp hx with hx | hx
    · have h := positiveIntegerWindow_int_bounds hx
      exact ⟨by linarith [Nat.cast_nonneg (α := ℤ) X],h.2⟩
    · have h := negativeIntegerWindow_int_bounds hx
      exact ⟨h.1,by linarith [Nat.cast_nonneg (α := ℤ) X]⟩
  have hcast : (x.natAbs:ℤ)≤(X:ℤ) := by
    simpa only [Int.natCast_natAbs] using abs_le.mpr hb
  exact_mod_cast hcast

theorem affine_numerator_natAbs_le {A B : Set ℕ} {X m : ℕ} {h x : ℤ}
    (hx : x∈positiveIntegerWindow A X∪negativeIntegerWindow B X) :
    ((m:ℤ)*x-h).natAbs ≤ m*X+h.natAbs := by
  have hxabs := integerWindows_natAbs_le hx
  have ht : |(m:ℤ)*x-h|≤(m:ℤ)*|x|+|h| := by
    simpa only [abs_mul,abs_of_nonneg (Nat.cast_nonneg (α := ℤ) m)] using abs_sub ((m:ℤ)*x) h
  have hb : ((m:ℤ)*x-h).natAbs ≤ m*x.natAbs+h.natAbs := by
    exact_mod_cast (show (((m:ℤ)*x-h).natAbs:ℤ)≤(m:ℤ)*(x.natAbs:ℤ)+(h.natAbs:ℤ) by
      simpa only [Int.natCast_natAbs] using ht)
  exact hb.trans (Nat.add_le_add_right (Nat.mul_le_mul_left m hxabs) _)

theorem positiveIntegerWindow_diameter {A : Set ℕ} {X : ℕ} {x y : ℤ}
    (hx : x∈positiveIntegerWindow A X) (hy : y∈positiveIntegerWindow A X) :
    |(x:ℝ)-(y:ℝ)|≤X := by
  have hx' := positiveIntegerWindow_int_bounds hx
  have hy' := positiveIntegerWindow_int_bounds hy
  have hb : |x-y|≤(X:ℤ) := abs_le.mpr ⟨by omega,by omega⟩
  exact_mod_cast hb

theorem negativeIntegerWindow_diameter {B : Set ℕ} {X : ℕ} {x y : ℤ}
    (hx : x∈negativeIntegerWindow B X) (hy : y∈negativeIntegerWindow B X) :
    |(x:ℝ)-(y:ℝ)|≤X := by
  have hx' := negativeIntegerWindow_int_bounds hx
  have hy' := negativeIntegerWindow_int_bounds hy
  have hb : |x-y|≤(X:ℤ) := abs_le.mpr ⟨by omega,by omega⟩
  exact_mod_cast hb

theorem positiveWindow_canonicalKernelRoots_diameter {A : Set ℕ} {X m : ℕ}
    {S : Finset ℤ} (hS : S⊆positiveIntegerWindow A X) (h u : ℤ) (hu : u≠0) :
    ∀r∈canonicalKernelRoots S m h u,∀s∈canonicalKernelRoots S m h u,
      |(r:ℝ)-(s:ℝ)|≤Real.sqrt ((m:ℝ)*X/|(u:ℝ)|) :=
  canonicalKernelRoots_diameter hu (Nat.cast_nonneg X)
    (fun _ hx _ hy => positiveIntegerWindow_diameter (hS hx) (hS hy))

theorem negativeWindow_canonicalKernelRoots_diameter {B : Set ℕ} {X m : ℕ}
    {S : Finset ℤ} (hS : S⊆negativeIntegerWindow B X) (h u : ℤ) (hu : u≠0) :
    ∀r∈canonicalKernelRoots S m h u,∀s∈canonicalKernelRoots S m h u,
      |(r:ℝ)-(s:ℝ)|≤Real.sqrt ((m:ℝ)*X/|(u:ℝ)|) :=
  canonicalKernelRoots_diameter hu (Nat.cast_nonneg X)
    (fun _ hx _ hy => negativeIntegerWindow_diameter (hS hx) (hS hy))

end Ostmann.QuadraticCenter

end

end OAI
