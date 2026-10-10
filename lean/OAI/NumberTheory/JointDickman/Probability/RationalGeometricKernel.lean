import OAI.NumberTheory.JointDickman.Probability.CyclicKernelSum
import OAI.NumberTheory.JointDickman.Probability.GeometricSquareKernel

namespace OAI

/-! # The geometric kernel at reduced rational frequencies -/
namespace JointDickman
open Finset

lemma cyclic_kernel_as_real_phase {q : ℕ} [NeZero q] (N h : ℕ) (u : (ZMod q)ˣ) :
    cyclicGeometricKernel N ((h:ZMod q)*(u:ZMod q)) =
      geometricSquareKernel N (((u:ZMod q).val:ℝ)/q*h) := by
  unfold cyclicGeometricKernel geometricSquareKernel
  congr 1
  congr 1
  apply sum_congr rfl
  intro j hj
  rw [show ((h:ZMod q)*(u:ZMod q))*(j:ZMod q) =
      (u:ZMod q)*((h*j:ℕ):ZMod q) by push_cast; ring,unit_nat_phase]
  congr 1
  push_cast
  ring

/-- A complete period has only one quadratic peak. All nonzero frequencies
together cost O(Nq), and the same estimate controls an arbitrary prefix. -/
theorem rational_geometric_kernel_sum {q : ℕ} [NeZero q]
    (N L : ℕ) (u : (ZMod q)ˣ) :
    (∑ h ∈ Icc 1 L, geometricSquareKernel N (((u:ZMod q).val:ℝ)/q*h)) ≤
      (N:ℝ)^2*(L:ℝ)/q + (N:ℝ)*((L:ℝ)+2*q) := by
  simp_rw [←cyclic_kernel_as_real_phase]
  exact cyclic_kernel_sum_bound N L u

lemma cyclic_kernel_coprime_numerator {q : ℕ} [NeZero q]
    (N h a : ℕ) (ha : a.Coprime q) :
    cyclicGeometricKernel N ((h:ZMod q)*(ZMod.unitOfCoprime a ha:ZMod q)) =
      geometricSquareKernel N ((a:ℝ)/q*h) := by
  unfold cyclicGeometricKernel geometricSquareKernel
  congr 1
  congr 1
  apply sum_congr rfl
  intro j hj
  rw [ZMod.coe_unitOfCoprime]
  have he : ((h:ZMod q)*(a:ZMod q))*(j:ZMod q) = ((a*h*j:ℕ):ZMod q) := by
    push_cast
    ring
  rw [he,stdAddChar_as_additivePhase]
  congr 1
  push_cast
  ring

theorem rational_geometric_kernel_sum_coprime {q : ℕ} [NeZero q]
    (N L a : ℕ) (ha : a.Coprime q) :
    (∑ h ∈ Icc 1 L, geometricSquareKernel N ((a:ℝ)/q*h)) ≤
      (N:ℝ)^2*(L:ℝ)/q + (N:ℝ)*((L:ℝ)+2*q) := by
  simp_rw [←cyclic_kernel_coprime_numerator N _ a ha]
  exact cyclic_kernel_sum_bound N L (ZMod.unitOfCoprime a ha)

end JointDickman

end OAI
