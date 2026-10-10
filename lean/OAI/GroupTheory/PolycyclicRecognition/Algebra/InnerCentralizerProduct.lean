import OAI.GroupTheory.PolycyclicRecognition.Geometry.InnerCentralizerLieSubalgebra
import OAI.GroupTheory.PolycyclicRecognition.Algebra.PolynomialSubalgebraGroup
import OAI.GroupTheory.PolycyclicRecognition.Algebra.PolynomialCommutingProduct

namespace OAI

/-! # A direct product decomposition of the semisimple inner centralizer

The moving factor is central and the other factor is fixed pointwise. Both
projections preserve the actual polynomial group law.
-/

noncomputable section
namespace PolycyclicRecognition
attribute [local instance] LieRing.ofAssociativeRing polynomialSubalgebraGroup
variable {L : Type} [RealNormedLieAlgebra L] [FiniteDimensional ℝ L]

def semisimpleFixedSubalgebra (S : L ≃ₗ⁅ℝ⁆ L) : LieSubalgebra ℝ L where
  toSubmodule := (S.toLinearMap - 1).ker
  lie_mem' := by
    intro x y hx hy
    change S x - x = 0 at hx
    change S y - y = 0 at hy
    change S ⁅x, y⁆ - ⁅x, y⁆ = 0
    rw [S.map_lie, sub_eq_zero.mp hx, sub_eq_zero.mp hy, sub_self]

def semisimpleMovingCenter (S : L ≃ₗ⁅ℝ⁆ L) : LieSubalgebra ℝ L where
  toSubmodule := (LieAlgebra.ad ℝ L).ker.toSubmodule ⊓ (S.toLinearMap - 1).range
  lie_mem' := by
    intro x y hx _
    have hz : ⁅x, y⁆ = 0 := LinearMap.congr_fun hx.1 y
    rw [hz]
    exact ⟨map_zero _, Submodule.zero_mem _⟩

omit [FiniteDimensional ℝ L] in
theorem fixed_mem_innerCentralizer (S : L ≃ₗ⁅ℝ⁆ L) {x : L}
    (hx : x ∈ semisimpleFixedSubalgebra S) : x ∈ innerCentralizerLieSubalgebra S := by
  change LieAlgebra.ad ℝ L (S x - x) = 0
  rw [show S x - x = 0 from hx, map_zero]

omit [FiniteDimensional ℝ L] in
theorem movingCenter_mem_innerCentralizer (S : L ≃ₗ⁅ℝ⁆ L) {x : L}
    (hx : x ∈ semisimpleMovingCenter S) : x ∈ innerCentralizerLieSubalgebra S := by
  have hSx : LieAlgebra.ad ℝ L (S x) = 0 := by
    apply LinearMap.ext
    intro y
    have hh : ⁅x, S.symm y⁆ = 0 := LinearMap.congr_fun hx.1 (S.symm y)
    change ⁅S x, y⁆ = 0
    rw [← S.apply_symm_apply y, ← S.map_lie, hh, map_zero]
  change LieAlgebra.ad ℝ L (S x - x) = 0
  rw [map_sub, hSx, show LieAlgebra.ad ℝ L x = 0 from hx.1, sub_self]

variable [P : PolynomialExponentialCoordinates L]

def innerCentralizerFixedGroupProjection (S : L ≃ₗ⁅ℝ⁆ L)
    (hS : Module.End.IsSemisimple S.toLinearMap) :
    innerCentralizerLieSubalgebra S →* semisimpleFixedSubalgebra S :=
  polynomialSubalgebraMap _ _ (innerCentralizerFixedProjection S hS)
    (fun x => semisimpleKernelProjection_mem _ (semisimple_sub_one S.toLinearMap hS) x)

def innerCentralizerMovingGroupProjection (S : L ≃ₗ⁅ℝ⁆ L)
    (hS : Module.End.IsSemisimple S.toLinearMap) :
    innerCentralizerLieSubalgebra S →* semisimpleMovingCenter S :=
  polynomialSubalgebraMap _ _ (innerCentralizerCentralProjection S hS) (fun x =>
    ⟨innerCentralizerCentralProjection_central S hS x,
      Submodule.sub_projection_mem (semisimple_kernel_range_isCompl _
        (semisimple_sub_one S.toLinearMap hS)) x⟩)

def innerCentralizerProductHom (S : L ≃ₗ⁅ℝ⁆ L)
    (hS : Module.End.IsSemisimple S.toLinearMap) :
    innerCentralizerLieSubalgebra S →*
      semisimpleFixedSubalgebra S × semisimpleMovingCenter S :=
  (innerCentralizerFixedGroupProjection S hS).prod
    (innerCentralizerMovingGroupProjection S hS)

theorem innerCentralizerProductHom_bijective (S : L ≃ₗ⁅ℝ⁆ L)
    (hS : Module.End.IsSemisimple S.toLinearMap) :
    Function.Bijective (innerCentralizerProductHom S hS) := by
  let p := semisimpleOneProjection S.toLinearMap hS
  constructor
  · intro x y h
    have hf : p x = p y := congrArg (fun z => (z.1 : L)) h
    have hm : (x : L) - p x = (y : L) - p y := congrArg (fun z => (z.2 : L)) h
    apply Subtype.ext
    calc
      (x : L) = p x + ((x : L) - p x) := by abel
      _ = p y + ((y : L) - p y) := by rw [hm, hf]
      _ = y := by abel
  · rintro ⟨x, z⟩
    have hx := fixed_mem_innerCentralizer S x.property
    have hz := movingCenter_mem_innerCentralizer S z.property
    let w : innerCentralizerLieSubalgebra S := ⟨(x : L) + z,
      (innerCentralizerLieSubalgebra S).add_mem hx hz⟩
    have hpx : p x = x := Submodule.projection_apply_of_mem_left _ x.property
    have hpz : p z = 0 := Submodule.projection_apply_of_mem_right _ z.property.2
    refine ⟨w, Prod.ext (Subtype.ext ?_) (Subtype.ext ?_)⟩
    · change p ((x : L) + z) = x
      rw [map_add, hpx, hpz, add_zero]
    · change (x : L) + z - p ((x : L) + z) = z
      rw [map_add, hpx, hpz, add_zero, add_sub_cancel_left]

def innerCentralizerProductEquiv (S : L ≃ₗ⁅ℝ⁆ L)
    (hS : Module.End.IsSemisimple S.toLinearMap) :
    innerCentralizerLieSubalgebra S ≃*
      semisimpleFixedSubalgebra S × semisimpleMovingCenter S :=
  MulEquiv.ofBijective (innerCentralizerProductHom S hS)
    (innerCentralizerProductHom_bijective S hS)

def innerCentralizerMovingInclusion (S : L ≃ₗ⁅ℝ⁆ L) :
    semisimpleMovingCenter S →* innerCentralizerLieSubalgebra S :=
  polynomialSubalgebraMap _ _ (semisimpleMovingCenter S).incl
    (fun x => movingCenter_mem_innerCentralizer S x.property)

theorem innerCentralizerMovingProjection_section (S : L ≃ₗ⁅ℝ⁆ L)
    (hS : Module.End.IsSemisimple S.toLinearMap) (x : semisimpleMovingCenter S) :
    innerCentralizerMovingGroupProjection S hS (innerCentralizerMovingInclusion S x) = x := by
  apply Subtype.ext
  change (x : L) - semisimpleOneProjection S.toLinearMap hS x = x
  have hp : semisimpleOneProjection S.toLinearMap hS x = 0 :=
    Submodule.projection_apply_of_mem_right _ x.property.2
  rw [hp, sub_zero]

theorem innerCentralizerMovingProjection_eq_one_iff (S : L ≃ₗ⁅ℝ⁆ L)
    (hS : Module.End.IsSemisimple S.toLinearMap) (x : innerCentralizerLieSubalgebra S) :
    innerCentralizerMovingGroupProjection S hS x = 1 ↔ S x = x := by
  let p := semisimpleOneProjection S.toLinearMap hS
  constructor
  · intro h
    have he : (x : L) - p x = 0 := by
      have hh := congrArg Subtype.val h
      change (x : L) - p x = (1 : L) at hh
      rwa [P.one_eq_zero] at hh
    have hp : S (p x) = p x := sub_eq_zero.mp
      (semisimpleKernelProjection_mem _ (semisimple_sub_one S.toLinearMap hS) x)
    have hx : (x : L) = p x := sub_eq_zero.mp he
    rw [hx, hp]
  · intro hx
    apply Subtype.ext
    have hp : p x = x := Submodule.projection_apply_of_mem_left _ (sub_eq_zero.mpr hx)
    change (x : L) - p x = (1 : L)
    rw [hp, sub_self, P.one_eq_zero]

end PolycyclicRecognition

end

end OAI
