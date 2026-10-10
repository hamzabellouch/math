import Mathlib
import OAI.Combinatorics.Chromatic.Walls.CompletedInverse
import OAI.Combinatorics.Chromatic.Walls.LaurentCompletion

namespace OAI

section
namespace ElementaryPositivity.QuantumTorus
open PowerSeries
noncomputable section
variable {M I : Type*} [AddCommGroup M] [Fintype I] [DecidableEq I]
variable (u : (LaurentSeries ℚ)ˣ) (Ω : M →+ M →+ ℤ)
variable (C : (I → ℤ) →+ M) (coord : M →+ (I → ℤ))
variable (hcoord : ∀d,coord (C d)=d) (pc : I)
local instance completedBiUnitRing : Ring (Torus u Ω) := Torus.instRing u Ω
local instance completedBiUnitAddCommMonoid : AddCommMonoid (Torus u Ω) :=
  (Torus.instRing u Ω).toAddCommMonoid
local instance completedBiUnitAddGroup : AddGroup (Torus u Ω) := (Torus.instRing u Ω).toAddGroup
local instance completedBiUnitNonUnitalSemiring : NonUnitalSemiring (Torus u Ω) :=
  (Torus.instRing u Ω).toNonUnitalSemiring
local instance completedBiUnitNonUnitalNonAssocSemiring : NonUnitalNonAssocSemiring (Torus u Ω) :=
  (Torus.instRing u Ω).toNonUnitalNonAssocSemiring

def completedBiUnit (F : CompletedPositive u Ω C) :
    (biSupportedSubring u Ω (nonpDegree coord pc) (pureDegree coord pc))ˣ where
  val:=⟨F.val,completed_biSupported u Ω C coord hcoord pc F⟩
  inv:=⟨(completedInverse u Ω C F).val,
    completed_biSupported u Ω C coord hcoord pc (completedInverse u Ω C F)⟩
  val_inv:=Subtype.ext (mul_completedInverse u Ω C F)
  inv_val:=Subtype.ext (completedInverse_mul u Ω C F)

@[simp] lemma completedBiUnit_val (F : CompletedPositive u Ω C) :
    (completedBiUnit u Ω C coord hcoord pc F).val.val=F.val := rfl
@[simp] lemma completedBiUnit_inv (F : CompletedPositive u Ω C) :
    (completedBiUnit u Ω C coord hcoord pc F).inv.val=invOfUnit F.val 1 := rfl
end
end ElementaryPositivity.QuantumTorus

end

end OAI
