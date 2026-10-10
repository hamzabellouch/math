import Mathlib.Algebra.Module.Torsion.Basic
import Mathlib.RingTheory.Noetherian.Basic

namespace OAI

/-! # A uniform exponent for integral torsion in a noetherian module

The coefficient ring may be a group ring. Only its noetherian module condition
is used to choose finitely many generators of the integral torsion submodule.
-/

noncomputable section
namespace PolycyclicRecognition
open scoped nonZeroDivisors
variable (R M : Type) [CommRing R] [AddCommGroup M] [Module R M] [IsNoetherian R M]

theorem noetherian_integral_torsion_exponent :
    ∃ z : ℤ, z ≠ 0 ∧ ∀ x ∈ Submodule.torsion' R M ℤ⁰, z • x = 0 := by
  classical
  let T := Submodule.torsion' R M ℤ⁰
  obtain ⟨s, hs⟩ := (show T.FG from IsNoetherian.noetherian T)
  have ht (x : s) : ∃ z : ℤ, z ≠ 0 ∧ z • (x : M) = 0 := by
    have hx : (x : M) ∈ T := hs ▸ Submodule.subset_span x.property
    change ∃ z : ℤ⁰, z • (x : M) = 0 at hx
    obtain ⟨z, hz⟩ := hx
    exact ⟨z, mem_nonZeroDivisors_iff_ne_zero.mp z.property, hz⟩
  choose z hz0 hzx using ht
  let a : ℤ := ∏ i : s, z i
  have ha : a ≠ 0 := Finset.prod_ne_zero_iff.mpr (fun i _ => hz0 i)
  refine ⟨a, ha, ?_⟩
  intro x hx
  have hx' : x ∈ Submodule.span R (s : Set M) := hs.symm ▸ hx
  clear hx
  induction hx' using Submodule.span_induction with
  | mem y hy =>
    have hd : z ⟨y, hy⟩ ∣ a := Finset.dvd_prod_of_mem z (Finset.mem_univ _)
    obtain ⟨c, hc⟩ := hd
    rw [hc, mul_comm, mul_smul, hzx ⟨y, hy⟩, smul_zero]
  | zero => exact smul_zero a
  | add x y _ _ hx hy => rw [smul_add, hx, hy, add_zero]
  | smul r x _ hx => rw [smul_comm, hx, smul_zero]

end PolycyclicRecognition

end

end OAI
