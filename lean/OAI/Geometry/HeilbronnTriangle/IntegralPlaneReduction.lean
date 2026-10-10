import OAI.Geometry.HeilbronnTriangle.PlaneReduction
import OAI.Geometry.HeilbronnTriangle.EqualCoordinatePlane
import OAI.Geometry.HeilbronnTriangle.PlaneLines

namespace OAI


noncomputable section
namespace Problem355.IntegralPlaneReduction

abbrev Vector := Fin 3 → ℤ

def integralNormal (x : Vector) : Vector →ₗ[ℤ] ℤ := dotProductBilin ℤ ℤ x

def integralPlane (Λ : Submodule ℤ Vector) (x : Vector) : Submodule ℤ Vector :=
  Λ ⊓ (integralNormal x).ker

def reducedNormal (q : ℕ) (x : Vector) : Fin 3 → ZMod q := fun i => (x i : ZMod q)

@[simp] theorem mem_integralPlane (Λ : Submodule ℤ Vector) (x v : Vector) :
    v ∈ integralPlane Λ x ↔ v ∈ Λ ∧ dotProduct x v = 0 := Iff.rfl

def reductionHom (q : ℕ) [Fact q.Prime] (Λ : Submodule ℤ Vector) (x : Vector) :
    integralPlane Λ x →+ (PlaneLines.normalMap (reducedNormal q x)).ker where
  toFun v := ⟨fun i => ((v : Vector) i : ZMod q), by
    change dotProduct (reducedNormal q x) (fun i => ((v : Vector) i : ZMod q)) = 0
    have h := congrArg (fun z : ℤ => (z : ZMod q)) v.property.2
    simpa [integralNormal, reducedNormal, dotProduct] using h⟩
  map_zero' := by ext i; simp
  map_add' u v := by ext i; simp

@[simp] theorem reductionHom_apply (q : ℕ) [Fact q.Prime] (Λ : Submodule ℤ Vector) (x : Vector)
    (v : integralPlane Λ x) (i : Fin 3) :
    ((reductionHom q Λ x v : (PlaneLines.normalMap (reducedNormal q x)).ker) :
      Fin 3 → ZMod q) i = ((v : Vector) i : ZMod q) := rfl

theorem reductionHom_surjective (q : ℕ) [Fact q.Prime] (Λ : Submodule ℤ Vector) (x z : Vector)
    (hz : dotProduct x z = 1) (E : ℤ) (hE : IsUnit (E : ZMod q))
    (hΛ : ∀ w : Vector, E • w ∈ Λ) :
    Function.Surjective (reductionHom q Λ x) := by
  intro v
  obtain ⟨w, hwΛ, hwx, hwred⟩ := PlaneReduction.lift_orthogonal_mem q x z hz E hE Λ hΛ
    (v : Fin 3 → ZMod q) v.property
  refine ⟨⟨w, hwΛ, hwx⟩, ?_⟩
  apply Subtype.ext
  exact funext hwred

theorem reducedNormal_ne_zero (q : ℕ) [Nontrivial (ZMod q)] (x z : Vector)
    (hz : dotProduct x z = 1) : reducedNormal q x ≠ 0 :=
  PlaneReduction.normal_reduction_ne_zero q x z hz

open scoped LinearAlgebra.Projectivization

def lineLattice (q : ℕ) [Fact q.Prime] (Λ : Submodule ℤ Vector) (x : Vector)
    (p : ℙ (ZMod q) (PlaneLines.normalMap (reducedNormal q x)).ker) :
    AddSubgroup (integralPlane Λ x) :=
  p.submodule.toAddSubgroup.comap (reductionHom q Λ x)

theorem lineLattice_index (q : ℕ) [Fact q.Prime] (Λ : Submodule ℤ Vector) (x z : Vector)
    (hz : dotProduct x z = 1) (E : ℤ) (hE : IsUnit (E : ZMod q))
    (hΛ : ∀ w : Vector, E • w ∈ Λ)
    (p : ℙ (ZMod q) (PlaneLines.normalMap (reducedNormal q x)).ker) :
    (lineLattice q Λ x p).index = q := by
  have h := PlaneLines.line_preimage_index
    (PlaneLines.normal_plane_finrank (reducedNormal q x) (reducedNormal_ne_zero q x z hz))
    (reductionHom q Λ x) (reductionHom_surjective q Λ x z hz E hE hΛ) p
  simpa [lineLattice, Nat.card_eq_fintype_card, ZMod.card] using h

theorem card_lines (q : ℕ) [Fact q.Prime] (x z : Vector) (hz : dotProduct x z = 1) :
    Nat.card (ℙ (ZMod q) (PlaneLines.normalMap (reducedNormal q x)).ker) = q + 1 := by
  simpa [Nat.card_eq_fintype_card, ZMod.card] using
    PlaneLines.card_normal_plane_lines (reducedNormal q x) (reducedNormal_ne_zero q x z hz)

theorem equalCoordinate_index (q : ℕ) [Fact q.Prime] (Λ : Submodule ℤ Vector)
    (x z : Vector) (hz : dotProduct x z = 1) (E : ℤ) (hE : IsUnit (E : ZMod q))
    (hΛ : ∀ w : Vector, E • w ∈ Λ) (i j : Fin 3) (hij : i ≠ j)
    (hspan : ¬ ∃ a : ZMod q,
      reducedNormal q x = a • PlaneFunctional.coordinateDifference i j) :
    (PlaneFunctional.equalCoordinateSubgroup q (integralPlane Λ x).toAddSubgroup i j).index = q := by
  apply PlaneFunctional.equalCoordinateSubgroup_index q (reducedNormal q x)
    (reducedNormal_ne_zero q x z hz) i j hij hspan
  intro v hv
  obtain ⟨w, hwΛ, hwx, hwred⟩ :=
    PlaneReduction.lift_orthogonal_mem q x z hz E hE Λ hΛ v hv
  exact ⟨⟨w, hwΛ, hwx⟩, hwred⟩

end Problem355.IntegralPlaneReduction

end

end OAI
