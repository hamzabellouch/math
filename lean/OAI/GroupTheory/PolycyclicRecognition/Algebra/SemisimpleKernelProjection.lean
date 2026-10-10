import Mathlib.Basic.Real.Basic
import Mathlib.LinearAlgebra.Semisimple
import OAI.GroupTheory.PolycyclicRecognition.Algebra.LinearInvariantInverse
import Mathlib.LinearAlgebra.Projection
import Mathlib.Tactic.Abel

namespace OAI

/-! # The canonical fixed-space projection preserves invariant filtrations

For a semisimple operator, its kernel and range are complementary. The
projection to the kernel preserves every invariant subspace, including the
lower central series when the operator is A - 1.
-/

noncomputable section
namespace PolycyclicRecognition
variable {L : Type*} [AddCommGroup L] [Module ℝ L] [FiniteDimensional ℝ L]

theorem semisimple_kernel_range_isCompl (B : Module.End ℝ L) (hB : B.IsSemisimple) :
    IsCompl B.ker B.range := by
  have hker : B.ker ∈ B.invtSubmodule := by
    change ∀ x ∈ B.ker, B x ∈ B.ker
    intro x hx
    change B (B x) = 0
    rw [LinearMap.mem_ker.mp hx, map_zero]
  obtain ⟨W, hW, hKW⟩ := Module.End.isSemisimple_iff.mp hB B.ker hker
  have hW' : ∀ x ∈ W, B x ∈ W := hW
  let f : W →ₗ[ℝ] W := B.restrict hW'
  have hi : Function.Injective f := by
    intro x y hxy
    apply Subtype.ext
    apply sub_eq_zero.mp
    apply Submodule.disjoint_def.mp hKW.disjoint
    · change B ((x : L) - (y : L)) = 0
      rw [map_sub]
      exact sub_eq_zero.mpr (congrArg Subtype.val hxy)
    · exact W.sub_mem x.property y.property
  have hs : Function.Surjective f := LinearMap.injective_iff_surjective.mp hi
  have hr : B.range = W := by
    apply le_antisymm
    · rintro _ ⟨x, rfl⟩
      have hx : x ∈ B.ker ⊔ W := by rw [hKW.sup_eq_top]; trivial
      obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.mp hx
      rw [← hab, map_add, LinearMap.mem_ker.mp ha, zero_add]
      exact hW' b hb
    · intro x hx
      obtain ⟨y, hy⟩ := hs ⟨x, hx⟩
      exact ⟨y, congrArg Subtype.val hy⟩
  rw [hr]
  exact hKW

omit [FiniteDimensional ℝ L] in
theorem semisimple_sub_one (B : Module.End ℝ L) (hB : B.IsSemisimple) :
    Module.End.IsSemisimple (B - 1) := by
  have h := (Module.End.isSemisimple_sub_algebraMap_iff (f := B) (μ := (1 : ℝ))).mpr hB
  simpa only [map_one] using h

def semisimpleKernelProjection (B : Module.End ℝ L) (hB : B.IsSemisimple) : Module.End ℝ L :=
  B.ker.projection B.range (semisimple_kernel_range_isCompl B hB)

theorem semisimpleKernelProjection_mem (B : Module.End ℝ L) (hB : B.IsSemisimple) (x : L) :
    semisimpleKernelProjection B hB x ∈ B.ker :=
  Submodule.projection_apply_mem _ _

theorem semisimpleKernelProjection_preserves (B : Module.End ℝ L) (hB : B.IsSemisimple)
    (U : Submodule ℝ L) (hU : ∀ x ∈ U, B x ∈ U) {x : L} (hx : x ∈ U) :
    semisimpleKernelProjection B hB x ∈ U := by
  let f : U →ₗ[ℝ] U := B.restrict hU
  have hf : Module.End.IsSemisimple f := hB.restrict hU
  have hc := semisimple_kernel_range_isCompl f hf
  have hx' : (⟨x, hx⟩ : U) ∈ f.ker ⊔ f.range := by rw [hc.sup_eq_top]; trivial
  obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.mp hx'
  have ha' : (a : L) ∈ B.ker := congrArg Subtype.val (LinearMap.mem_ker.mp ha)
  have hb' : (b : L) ∈ B.range := by
    obtain ⟨y, hy⟩ := hb
    exact ⟨y, congrArg Subtype.val hy⟩
  have he : (a : L) + (b : L) = x := congrArg Subtype.val hab
  rw [← he, map_add]
  change B.ker.projection B.range (semisimple_kernel_range_isCompl B hB) a +
    B.ker.projection B.range (semisimple_kernel_range_isCompl B hB) b ∈ U
  rw [Submodule.projection_apply_of_mem_left _ ha',
    Submodule.projection_apply_of_mem_right _ hb', add_zero]
  exact a.property

theorem semisimpleKernelProjection_commute (B T : Module.End ℝ L)
    (hB : B.IsSemisimple) (hBT : Commute B T) :
    Commute (semisimpleKernelProjection B hB) T := by
  let P := semisimpleKernelProjection B hB
  apply LinearMap.ext
  intro x
  have hp : T (P x) ∈ B.ker := by
    change B (T (P x)) = 0
    have he := LinearMap.congr_fun hBT.eq (P x)
    change B (T (P x)) = T (B (P x)) at he
    rw [he, LinearMap.mem_ker.mp (semisimpleKernelProjection_mem B hB x), map_zero]
  have hq : T (x - P x) ∈ B.range := by
    obtain ⟨y, hy⟩ := Submodule.sub_projection_mem (semisimple_kernel_range_isCompl B hB) x
    refine ⟨T y, ?_⟩
    have he := LinearMap.congr_fun hBT.eq y
    change B (T y) = T (B y) at he
    rw [he, hy]
    rfl
  have hs : x = P x + (x - P x) := by abel
  change P (T x) = T (P x)
  conv_lhs => rw [hs, map_add, map_add]
  have hpp : P (T (P x)) = T (P x) := Submodule.projection_apply_of_mem_left _ hp
  have hpq : P (T (x - P x)) = 0 := Submodule.projection_apply_of_mem_right _ hq
  rw [hpp, hpq, add_zero]

theorem semisimple_add_kernelProjection_bijective (B : Module.End ℝ L)
    (hB : B.IsSemisimple) : Function.Bijective (B + semisimpleKernelProjection B hB) := by
  let P := semisimpleKernelProjection B hB
  have hz (x : L) (hx : (B + P) x = 0) : x = 0 := by
    have hPB : P (B x) = 0 := Submodule.projection_apply_of_mem_right _ ⟨x, rfl⟩
    have hPP : P (P x) = P x :=
      Submodule.projection_apply_of_mem_left _ (semisimpleKernelProjection_mem B hB x)
    have hp := congrArg P hx
    change P (B x + P x) = P 0 at hp
    rw [map_add, hPB, hPP, map_zero, zero_add] at hp
    have hBx : B x = 0 := by
      change B x + P x = 0 at hx
      rwa [hp, add_zero] at hx
    have hPx : P x = x := Submodule.projection_apply_of_mem_left _ hBx
    exact hPx.symm.trans hp
  have hi : Function.Injective (B + P) := by
    intro x y hxy
    apply sub_eq_zero.mp
    apply hz
    rw [map_sub, hxy, sub_self]
  exact ⟨hi, LinearMap.injective_iff_surjective.mp hi⟩

/-- A vector whose image lies in an invariant subspace differs from its fixed
component by a vector in that subspace. -/
theorem semisimple_sub_projection_mem_of_apply_mem
    (B : Module.End ℝ L) (hB : B.IsSemisimple)
    (U : Submodule ℝ L) (hU : ∀ x ∈ U, B x ∈ U) {x : L} (hx : B x ∈ U) :
    x - semisimpleKernelProjection B hB x ∈ U := by
  let P := semisimpleKernelProjection B hB
  let e : L ≃ₗ[ℝ] L := LinearEquiv.ofBijective (B + P)
    (semisimple_add_kernelProjection_bijective B hB)
  have he : e (x - P x) = B x := by
    have hBP : B (P x) = 0 := semisimpleKernelProjection_mem B hB x
    have hPP : P (P x) = P x := Submodule.projection_apply_of_mem_left _
      (semisimpleKernelProjection_mem B hB x)
    change B (x - P x) + P (x - P x) = B x
    rw [map_sub, map_sub, hBP, hPP]
    abel
  have hp : e.symm (B x) ∈ U := inverse_mem_of_preserves_submodule e U
    (fun y hy => U.add_mem (hU y hy) (semisimpleKernelProjection_preserves B hB U hU hy)) hx
  rwa [← he, e.symm_apply_apply] at hp

end PolycyclicRecognition

end

end OAI
