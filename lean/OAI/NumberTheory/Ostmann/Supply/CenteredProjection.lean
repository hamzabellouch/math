import Mathlib

namespace OAI

noncomputable section
namespace Ostmann.Supply
open scoped BigOperators ComplexConjugate
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
local notation "H" => EuclideanSpace ℂ ι

def centeredSpace (S : Finset ι) : Submodule ℂ H where
  carrier := {v | (∀ x, x ∉ S → v x = 0) ∧ ∑ x ∈ S, v x = 0}
  zero_mem' := by simp
  add_mem' := by
    intro v w hv hw
    constructor
    · intro x hx
      simp [hv.1 x hx, hw.1 x hx]
    · simp only [PiLp.add_apply, Finset.sum_add_distrib, hv.2, hw.2, add_zero]
  smul_mem' := by
    intro c v hv
    constructor
    · intro x hx
      simp [hv.1 x hx]
    · simp only [PiLp.smul_apply, smul_eq_mul, ← Finset.mul_sum, hv.2, mul_zero]

def centeredProjection (S : Finset ι) : H →L[ℂ] H := (centeredSpace S).starProjection

def uniformVector (S : Finset ι) : H :=
  WithLp.toLp 2 (fun x => if x ∈ S then (S.card : ℂ)⁻¹ else 0)

omit [Fintype ι] in
@[simp] theorem uniformVector_apply (S : Finset ι) (x : ι) :
    uniformVector S x = if x ∈ S then (S.card : ℂ)⁻¹ else 0 := rfl

omit [Fintype ι] in
theorem sum_uniformVector (S : Finset ι) (hS : S.Nonempty) :
    ∑ x ∈ S, uniformVector S x = 1 := by
  have hs : (S.card : ℂ) ≠ 0 := by exact_mod_cast Finset.card_ne_zero.mpr hS
  simp only [uniformVector_apply, Finset.sum_ite_mem, Finset.inter_self, Finset.sum_const,
    nsmul_eq_mul, mul_inv_cancel₀ hs]

theorem uniformVector_inner (S : Finset ι) (v : H) :
    inner ℂ (uniformVector S) v = (S.card : ℂ)⁻¹ * ∑ x ∈ S, v x := by
  simp only [PiLp.inner_apply, RCLike.inner_apply, uniformVector_apply,
    apply_ite, map_inv₀, map_natCast, map_zero, mul_zero]
  rw [Finset.sum_ite_mem, Finset.univ_inter, ← Finset.sum_mul, mul_comm]

theorem uniformVector_orthogonal (S : Finset ι) :
    uniformVector S ∈ (centeredSpace S)ᗮ := by
  apply (Submodule.mem_orthogonal' _ _).mpr
  intro v hv
  rw [uniformVector_inner, hv.2, mul_zero]

omit [Fintype ι] in
theorem point_sub_uniform_mem (S : Finset ι) (x : ι) (hx : x ∈ S) :
    EuclideanSpace.single x (1 : ℂ) - uniformVector S ∈ centeredSpace S := by
  constructor
  · intro y hy
    have hxy : y ≠ x := by rintro rfl; exact hy hx
    simp [PiLp.sub_apply, hxy, hy]
  · have hs := sum_uniformVector S ⟨x,hx⟩
    simp only [PiLp.sub_apply, Finset.sum_sub_distrib, hs,
      PiLp.single_apply, Finset.sum_ite_eq', hx, ite_true, sub_self]

theorem centeredProjection_single (S : Finset ι) (x : ι) (hx : x ∈ S) :
    centeredProjection S (EuclideanSpace.single x (1 : ℂ)) =
      EuclideanSpace.single x (1 : ℂ) - uniformVector S := by
  apply Submodule.eq_starProjection_of_mem_orthogonal'
    (point_sub_uniform_mem S x hx) (uniformVector_orthogonal S)
  exact (sub_add_cancel _ _).symm

omit [DecidableEq ι] in
theorem centeredProjection_norm_le (S : Finset ι) : ‖centeredProjection S‖ ≤ 1 :=
  (centeredSpace S).starProjection_norm_le

theorem centeredProjection_gram (S : Finset ι) (x y : ι)
    (hx : x ∈ S) (hy : y ∈ S) :
    inner ℂ (centeredProjection S (EuclideanSpace.single x (1 : ℂ)))
      (centeredProjection S (EuclideanSpace.single y (1 : ℂ))) =
      (if x = y then 1 else 0) - (S.card : ℂ)⁻¹ := by
  rw [centeredProjection_single S x hx, inner_sub_left]
  have hv : centeredProjection S (EuclideanSpace.single y (1 : ℂ)) ∈ centeredSpace S :=
    (centeredSpace S).starProjection_apply_mem _
  rw [uniformVector_inner, hv.2, mul_zero, sub_zero,
    EuclideanSpace.inner_single_left]
  simp only [map_one, one_mul, centeredProjection_single S y hy,
    PiLp.sub_apply, PiLp.single_apply, uniformVector_apply, hx, ite_true]

end Ostmann.Supply

end

end OAI
