import Mathlib.GroupTheory.Schreier
import Mathlib.GroupTheory.Subgroup.Centralizer

namespace OAI

/-! # The centralizer of a finite-index subgroup has finite commutator -/
noncomputable section
namespace PolycyclicRecognition
open scoped commutatorElement
variable {G : Type} [Group G]

theorem commutatorElement_center_mul_left (z a b : G) (hz : z ∈ Subgroup.center G) :
    ⁅z * a, b⁆ = ⁅a, b⁆ := by
  rw [commutatorElement_mul_left_eq_conj_mul]
  have hzb : ⁅z, b⁆ = 1 := commutatorElement_eq_one_iff_mul_comm.mpr
    ((Subgroup.mem_center_iff.mp hz b).symm)
  rw [hzb, mul_one, ← Subgroup.mem_center_iff.mp hz ⁅a, b⁆, mul_inv_cancel_right]

theorem commutatorElement_center_mul_right (z a b : G) (hz : z ∈ Subgroup.center G) :
    ⁅a, z * b⁆ = ⁅a, b⁆ := by
  rw [commutatorElement_mul_right_eq_mul_conj]
  have haz : ⁅a, z⁆ = 1 := commutatorElement_eq_one_iff_mul_comm.mpr
    (Subgroup.mem_center_iff.mp hz a)
  rw [haz, one_mul, ← Subgroup.mem_center_iff.mp hz ⁅a, b⁆, mul_inv_cancel_right]

theorem commutator_finite_of_center_finiteIndex [(Subgroup.center G).FiniteIndex] :
    Finite (commutator G) := by
  classical
  let q := QuotientGroup.mk' (Subgroup.center G)
  let rep : G ⧸ Subgroup.center G → G := Quotient.out
  have hrep (g : G) : g * (rep (q g))⁻¹ ∈ Subgroup.center G := by
    apply (QuotientGroup.eq_one_iff _).mp
    change q (g * (rep (q g))⁻¹) = 1
    rw [map_mul, map_inv]
    have hr : q (rep (q g)) = q g := Quotient.out_eq' (q g)
    rw [hr, mul_inv_cancel]
  have he (g h : G) : ⁅g, h⁆ = ⁅rep (q g), rep (q h)⁆ := by
    calc
      ⁅g, h⁆ = ⁅(g * (rep (q g))⁻¹) * rep (q g), h⁆ := by simp
      _ = ⁅rep (q g), h⁆ := commutatorElement_center_mul_left _ _ _ (hrep g)
      _ = ⁅rep (q g), (h * (rep (q h))⁻¹) * rep (q h)⁆ := by simp
      _ = ⁅rep (q g), rep (q h)⁆ := commutatorElement_center_mul_right _ _ _ (hrep h)
  let f : (G ⧸ Subgroup.center G) × (G ⧸ Subgroup.center G) → G :=
    fun p => ⁅rep p.1, rep p.2⁆
  have hs : (commutatorSet G).Finite := (Set.finite_range f).subset (by
    rintro x ⟨g, h, rfl⟩
    exact ⟨(q g, q h), (he g h).symm⟩)
  let : Finite (commutatorSet G) := Set.finite_coe_iff.mpr hs
  infer_instance

theorem centralizer_commutator_finite (F : Subgroup G) [F.FiniteIndex] :
    Finite (commutator (Subgroup.centralizer (F : Set G))) := by
  let C := Subgroup.centralizer (F : Set G)
  have hle : F.subgroupOf C ≤ Subgroup.center C := by
    intro x hx
    apply Subgroup.mem_center_iff.mpr
    intro y
    apply Subtype.ext
    exact (y.property x hx).symm
  let : (Subgroup.center C).FiniteIndex := Subgroup.finiteIndex_of_le hle
  exact commutator_finite_of_center_finiteIndex

end PolycyclicRecognition

end

end OAI
