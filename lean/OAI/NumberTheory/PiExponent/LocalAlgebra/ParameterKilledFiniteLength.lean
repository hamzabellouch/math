import Mathlib.Algebra.Module.Torsion.Basic
import Mathlib.RingTheory.Finiteness.Basic
import Mathlib.RingTheory.OrderOfVanishing.Noetherian

namespace OAI

namespace PiExponentJets.W06

variable {A : Type*} [CommRing A] [IsNoetherianRing A] [Ring.KrullDimLE 1 A]

theorem isArtinianRing_quotient_parameter {x : A} (hx : x ∈ nonZeroDivisors A) :
    IsArtinianRing (A ⧸ Ideal.span {x}) := by
  have hlength : IsFiniteLength A (A ⧸ Ideal.span {x}) :=
    isFiniteLength_quotient_span_singleton A hx
  have hart : IsArtinian A (A ⧸ Ideal.span {x}) :=
    (isFiniteLength_iff_isNoetherian_isArtinian.mp hlength).2
  exact isArtinian_of_tower A hart

variable {M : Type*} [AddCommGroup M] [Module A M]

theorem isFiniteLength_of_parameter_killed [Module.Finite A M]
    {x : A} (hx : x ∈ nonZeroDivisors A) (hkill : ∀ m : M, x • m = 0) :
    IsFiniteLength A M := by
  have ht : Module.IsTorsionBy A M x := fun {m} => hkill m
  have hs : Module.IsTorsionBySet A M (Ideal.span {x}) :=
    (Module.isTorsionBySet_span_singleton_iff x).mpr ht
  let : Module (A ⧸ Ideal.span {x}) M := hs.module
  let : IsScalarTower A (A ⧸ Ideal.span {x}) M := hs.isScalarTower
  let : IsArtinianRing (A ⧸ Ideal.span {x}) := isArtinianRing_quotient_parameter hx
  let : Module.Finite (A ⧸ Ideal.span {x}) M :=
    Module.Finite.of_restrictScalars_finite A (A ⧸ Ideal.span {x}) M
  let : IsArtinian (A ⧸ Ideal.span {x}) M := inferInstance
  have hart : IsArtinian A M :=
    isArtinian_of_surjective_algebraMap (R := A ⧸ Ideal.span {x}) (S := A)
      (M := M) (Ideal.Quotient.mk_surjective (I := Ideal.span {x}))
  exact isFiniteLength_iff_isNoetherian_isArtinian.mpr ⟨inferInstance, hart⟩

theorem length_ne_top_of_parameter_killed [Module.Finite A M]
    {x : A} (hx : x ∈ nonZeroDivisors A) (hkill : ∀ m : M, x • m = 0) :
    Module.length A M ≠ ⊤ :=
  Module.length_ne_top_iff.mpr (isFiniteLength_of_parameter_killed hx hkill)

omit [IsNoetherianRing A] [Ring.KrullDimLE 1 A] in

theorem parameter_kills_mul_kernel (x : A) :
    ∀ m : LinearMap.ker (x • (LinearMap.id : M →ₗ[A] M)), x • m = 0 := by
  intro m
  apply Subtype.ext
  change x • (m : M) = 0
  simpa only [LinearMap.mem_ker, LinearMap.smul_apply, LinearMap.id_apply] using m.property

omit [IsNoetherianRing A] [Ring.KrullDimLE 1 A] in

theorem parameter_kills_mul_cokernel (x : A) :
    ∀ m : M ⧸ LinearMap.range (x • (LinearMap.id : M →ₗ[A] M)), x • m = 0 := by
  have ht : Module.IsTorsionBy A
      (M ⧸ LinearMap.range (x • (LinearMap.id : M →ₗ[A] M))) x :=
    (Module.isTorsionBy_quotient_iff _ x).mpr (fun m => ⟨m, rfl⟩)
  exact fun m => @ht m

theorem isFiniteLength_ker_parameter_mul [Module.Finite A M]
    {x : A} (hx : x ∈ nonZeroDivisors A) :
    IsFiniteLength A (LinearMap.ker (x • (LinearMap.id : M →ₗ[A] M))) := by
  let : IsNoetherian A M := inferInstance
  let : Module.Finite A (LinearMap.ker (x • (LinearMap.id : M →ₗ[A] M))) := inferInstance
  exact isFiniteLength_of_parameter_killed hx (parameter_kills_mul_kernel x)

theorem isFiniteLength_coker_parameter_mul [Module.Finite A M]
    {x : A} (hx : x ∈ nonZeroDivisors A) :
    IsFiniteLength A (M ⧸ LinearMap.range (x • (LinearMap.id : M →ₗ[A] M))) := by
  exact isFiniteLength_of_parameter_killed hx (parameter_kills_mul_cokernel x)

theorem kernel_cokernel_parameter_lengths_ne_top [Module.Finite A M]
    {x : A} (hx : x ∈ nonZeroDivisors A) :
    Module.length A (LinearMap.ker (x • (LinearMap.id : M →ₗ[A] M))) ≠ ⊤ ∧
    Module.length A (M ⧸ LinearMap.range (x • (LinearMap.id : M →ₗ[A] M))) ≠ ⊤ :=
  ⟨Module.length_ne_top_iff.mpr (isFiniteLength_ker_parameter_mul hx),
    Module.length_ne_top_iff.mpr (isFiniteLength_coker_parameter_mul hx)⟩

end PiExponentJets.W06

end OAI
