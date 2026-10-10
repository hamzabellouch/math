import OAI.Geometry.HeilbronnTriangle.RowLattice
import OAI.Geometry.HeilbronnTriangle.PlaneReduction
import OAI.Geometry.HeilbronnTriangle.PlaneFunctional
import OAI.Geometry.HeilbronnTriangle.EqualCoordinatePlane
import OAI.Geometry.HeilbronnTriangle.PlaneLines

namespace OAI


noncomputable section

namespace Problem355.RowLattice

def integerDotHom (x : Fin 3 → ℤ) : (Fin 3 → ℤ) →+ ℤ where
  toFun v := x ⬝ᵥ v
  map_zero' := by simp
  map_add' v w := by simp [dotProduct_add]

def integerPlane (h : ℕ) (C : Matrix (Fin 3) (Fin 3) (ZMod h))
    (x : Fin 3 → ℤ) : AddSubgroup (Fin 3 → ℤ) :=
  integerRowLattice h C ⊓ (integerDotHom x).ker

lemma integerPlane_toIntSubmodule (h : ℕ)
    (C : Matrix (Fin 3) (Fin 3) (ZMod h)) (x : Fin 3 → ℤ) :
    (integerPlane h C x).toIntSubmodule =
      (integerRowLattice h C).toIntSubmodule ⊓ (dotProductBilin ℤ ℤ x).ker := by
  ext v
  rfl

@[simp] lemma mem_integerPlane (h : ℕ)
    (C : Matrix (Fin 3) (Fin 3) (ZMod h)) (x v : Fin 3 → ℤ) :
    v ∈ integerPlane h C x ↔ v ∈ integerRowLattice h C ∧ x ⬝ᵥ v = 0 := Iff.rfl

theorem integerPlane_reduction_surjective
    (B k b e q : ℕ) (hbe : b ≤ e)
    (C : Matrix (Fin 3) (Fin 3) (ZMod (B ^ k)))
    (P Q : Matrix.GeneralLinearGroup (Fin 3) (ZMod (B ^ k)))
    (hC : C = (P : Matrix (Fin 3) (Fin 3) (ZMod (B ^ k))) *
      DiagonalStabilizer.diagonal3 (R := ZMod (B ^ k)) (B ^ b) (B ^ e) *
      (Q : Matrix (Fin 3) (Fin 3) (ZMod (B ^ k))))
    (hBq : IsUnit (B : ZMod q))
    (x z : Fin 3 → ℤ) (hz : x ⬝ᵥ z = 1)
    (v : Fin 3 → ZMod q) (hv : reduction q x ⬝ᵥ v = 0) :
    ∃ w : integerPlane (B ^ k) C x, ∀ i, ((w.val i : ℤ) : ZMod q) = v i := by
  have hcontain : ∀ w : Fin 3 → ℤ, ((B ^ e : ℕ) : ℤ) • w ∈
      (integerRowLattice (B ^ k) C).toIntSubmodule := by
    intro w
    change ((B ^ e : ℕ) : ℤ) • w ∈ integerRowLattice (B ^ k) C
    simpa only [natCast_zsmul] using
      nsmul_mem_integerRowLattice_prime_power B k b e hbe C P Q hC w
  have hE : IsUnit (((B ^ e : ℕ) : ℤ) : ZMod q) := by
    simpa using hBq.pow e
  obtain ⟨w, hw, horth, hred⟩ := PlaneReduction.lift_orthogonal_mem q x z hz
    (B ^ e : ℕ) hE (integerRowLattice (B ^ k) C).toIntSubmodule hcontain v hv
  exact ⟨⟨w, hw, horth⟩, hred⟩

theorem integerPlane_extra_equation_index
    (B k b e q : ℕ) [Fact q.Prime] (hbe : b ≤ e)
    (C : Matrix (Fin 3) (Fin 3) (ZMod (B ^ k)))
    (P Q : Matrix.GeneralLinearGroup (Fin 3) (ZMod (B ^ k)))
    (hC : C = (P : Matrix (Fin 3) (Fin 3) (ZMod (B ^ k))) *
      DiagonalStabilizer.diagonal3 (R := ZMod (B ^ k)) (B ^ b) (B ^ e) *
      (Q : Matrix (Fin 3) (Fin 3) (ZMod (B ^ k))))
    (hBq : IsUnit (B : ZMod q))
    (x z : Fin 3 → ℤ) (hz : x ⬝ᵥ z = 1) (δ : Fin 3 → ZMod q)
    (hδ : ¬ ∃ a : ZMod q, δ = a • reduction q x) :
    (((PlaneFunctional.modularDotHom q δ).comp
      (integerPlane (B ^ k) C x).subtype).ker).index = q := by
  have hx : reduction q x ≠ 0 :=
    PlaneReduction.normal_reduction_ne_zero q x z hz
  exact PlaneFunctional.modular_equation_index q (reduction q x) δ hx hδ
    (integerPlane (B ^ k) C x)
    (integerPlane_reduction_surjective B k b e q hbe C P Q hC hBq x z hz)

theorem integerPlane_equalCoordinate_index
    (B k b e q : ℕ) [Fact q.Prime] (hbe : b ≤ e)
    (C : Matrix (Fin 3) (Fin 3) (ZMod (B ^ k)))
    (P Q : Matrix.GeneralLinearGroup (Fin 3) (ZMod (B ^ k)))
    (hC : C = (P : Matrix (Fin 3) (Fin 3) (ZMod (B ^ k))) *
      DiagonalStabilizer.diagonal3 (R := ZMod (B ^ k)) (B ^ b) (B ^ e) *
      (Q : Matrix (Fin 3) (Fin 3) (ZMod (B ^ k))))
    (hBq : IsUnit (B : ZMod q))
    (x z : Fin 3 → ℤ) (hz : x ⬝ᵥ z = 1) (i j : Fin 3) (hij : i ≠ j)
    (hspan : ¬ ∃ a : ZMod q,
      reduction q x = a • PlaneFunctional.coordinateDifference i j) :
    (PlaneFunctional.equalCoordinateSubgroup q (integerPlane (B ^ k) C x) i j).index = q := by
  exact integerPlane_extra_equation_index B k b e q hbe C P Q hC hBq x z hz
    (PlaneFunctional.coordinateDifference i j)
    (PlaneFunctional.not_exists_smul_swap _ _
      (PlaneFunctional.coordinateDifference_ne_zero hij) hspan)

def planeReductionHom (h q : ℕ) [Fact q.Prime]
    (C : Matrix (Fin 3) (Fin 3) (ZMod h)) (x : Fin 3 → ℤ) :
    integerPlane h C x →+ (PlaneLines.normalMap (reduction q x)).ker where
  toFun v := ⟨reduction q v.val, by
    have hv : x ⬝ᵥ v.val = 0 := v.property.2
    change reduction q x ⬝ᵥ reduction q v.val = 0
    simpa [dotProduct, reduction] using congrArg (fun z : ℤ => (z : ZMod q)) hv⟩
  map_zero' := by apply Subtype.ext; exact (reduction q).map_zero
  map_add' v w := by apply Subtype.ext; exact (reduction q).map_add v.val w.val

theorem planeReductionHom_surjective
    (B k b e q : ℕ) [Fact q.Prime] (hbe : b ≤ e)
    (C : Matrix (Fin 3) (Fin 3) (ZMod (B ^ k)))
    (P Q : Matrix.GeneralLinearGroup (Fin 3) (ZMod (B ^ k)))
    (hC : C = (P : Matrix (Fin 3) (Fin 3) (ZMod (B ^ k))) *
      DiagonalStabilizer.diagonal3 (R := ZMod (B ^ k)) (B ^ b) (B ^ e) *
      (Q : Matrix (Fin 3) (Fin 3) (ZMod (B ^ k))))
    (hBq : IsUnit (B : ZMod q))
    (x z : Fin 3 → ℤ) (hz : x ⬝ᵥ z = 1) :
    Function.Surjective (planeReductionHom (B ^ k) q C x) := by
  intro v
  obtain ⟨w, hw⟩ := integerPlane_reduction_surjective B k b e q hbe C P Q hC hBq
    x z hz v.val v.property
  exact ⟨w, Subtype.ext (funext hw)⟩

open scoped LinearAlgebra.Projectivization

theorem planeReductionHom_line_preimage_index
    (B k b e q : ℕ) [Fact q.Prime] (hbe : b ≤ e)
    (C : Matrix (Fin 3) (Fin 3) (ZMod (B ^ k)))
    (P Q : Matrix.GeneralLinearGroup (Fin 3) (ZMod (B ^ k)))
    (hC : C = (P : Matrix (Fin 3) (Fin 3) (ZMod (B ^ k))) *
      DiagonalStabilizer.diagonal3 (R := ZMod (B ^ k)) (B ^ b) (B ^ e) *
      (Q : Matrix (Fin 3) (Fin 3) (ZMod (B ^ k))))
    (hBq : IsUnit (B : ZMod q))
    (x z : Fin 3 → ℤ) (hz : x ⬝ᵥ z = 1)
    (p : ℙ (ZMod q) (PlaneLines.normalMap (reduction q x)).ker) :
    (p.submodule.toAddSubgroup.comap (planeReductionHom (B ^ k) q C x)).index = q := by
  have hx : reduction q x ≠ 0 :=
    PlaneReduction.normal_reduction_ne_zero q x z hz
  simpa only [Nat.card_zmod] using PlaneLines.line_preimage_index
    (PlaneLines.normal_plane_finrank (reduction q x) hx)
    (planeReductionHom (B ^ k) q C x)
    (planeReductionHom_surjective B k b e q hbe C P Q hC hBq x z hz) p

end Problem355.RowLattice

end

end OAI
