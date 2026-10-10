import OAI.NumberTheory.Ostmann.Supply.KernelEmpirical
import OAI.NumberTheory.Ostmann.Supply.WeightPointwiseBound

namespace OAI

noncomputable section
namespace Ostmann.Supply
open scoped BigOperators

def naturalKernelWeight (p : ℕ→ℕ) [∀i,NeZero (p i)]
    (S : ∀i,Finset (ZMod (p i))) (n K k : ℕ) : ℝ :=
  truncatedWeight (Finset.range n) (fun i => localKernel (S i) sparseKernelScale (k:ZMod (p i))) K

theorem naturalKernelWeight_nonneg (p : ℕ→ℕ) [∀i,NeZero (p i)]
    (S : ∀i,Finset (ZMod (p i))) (n K k : ℕ) : 0≤naturalKernelWeight p S n K k :=
  truncatedWeight_nonneg _ _ _

theorem naturalKernelWeight_le (p : ℕ→ℕ) [∀i,NeZero (p i)]
    (S : ∀i,Finset (ZMod (p i))) (n K k : ℕ) :
    naturalKernelWeight p S n K k≤(K+1:ℝ)^2*(n+1:ℝ)^(2*K) := by
  simpa only [naturalKernelWeight,Finset.card_range] using
    truncatedKernelWeight_pointwise_le (Finset.range n) p S (fun i => (k:ZMod (p i))) K

theorem kernelAverageWeight_natural (p : ℕ→ℕ) [∀i,NeZero (p i)]
    (S : ∀i,Finset (ZMod (p i))) (A B : Finset ℕ) (n K : ℕ) :
    kernelAverageWeight p S A B (fun a i => (a:ZMod (p i)))
      (fun b i => -(b:ZMod (p i))) n K =
      (A.card:ℝ)⁻¹*(B.card:ℝ)⁻¹*∑a∈A,∑b∈B,naturalKernelWeight p S n K (a+b) := by
  simp only [kernelAverageWeight,naturalKernelWeight,sub_neg_eq_add,Nat.cast_add]

theorem naturalKernelWeight_pair_sum (p : ℕ→ℕ) [∀i,NeZero (p i)]
    (S : ∀i,Finset (ZMod (p i))) (A B : Finset ℕ) (n K : ℕ)
    (hA : A.Nonempty) (hB : B.Nonempty) :
    (∑a∈A,∑b∈B,naturalKernelWeight p S n K (a+b)) =
      ((A.card:ℝ)*(B.card:ℝ))*kernelAverageWeight p S A B
        (fun a i => (a:ZMod (p i))) (fun b i => -(b:ZMod (p i))) n K := by
  have hA0 : (A.card:ℝ)≠0 := Nat.cast_ne_zero.mpr (Finset.card_ne_zero.mpr hA)
  have hB0 : (B.card:ℝ)≠0 := Nat.cast_ne_zero.mpr (Finset.card_ne_zero.mpr hB)
  rw [kernelAverageWeight_natural]
  field_simp

end Ostmann.Supply

end

end OAI
