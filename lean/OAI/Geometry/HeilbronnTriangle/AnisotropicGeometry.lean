import OAI.Geometry.HeilbronnTriangle.CrossNormal
import OAI.Geometry.HeilbronnTriangle.NormalGroupCount
import OAI.Geometry.HeilbronnTriangle.LatticeReciprocal

namespace OAI


noncomputable section

namespace Problem355.Anisotropic

open Matrix
open scoped Matrix
open PrimitiveNormal

abbrev IntVector := Fin 3 → ℤ

abbrev length (v : IntVector) : ℝ := ‖LatticeBox.realVector v‖

structure PlaneData (y : IntVector) where
  first : ℝ
  second : ℝ
  one_le_first : 1 ≤ first
  first_le_second : first ≤ second
  second_le_length : second ≤ length y
  first_le : ∀ v : IntVector, v ⬝ᵥ y = 0 → v ≠ 0 → first ≤ length v
  second_le : ∀ v w : IntVector, v ⬝ᵥ y = 0 → w ⬝ᵥ y = 0 →
    v ⨯₃ w ≠ 0 → second ≤ max (length v) (length w)
  shortest : ∃ z : IntVector, IsPrimitive z ∧ z ⬝ᵥ y = 0 ∧ length z = first
  large_count : ∀ (S : Finset IntVector) (R : ℝ), second ≤ R →
    (∀ v ∈ S, v ⬝ᵥ y = 0 ∧ length v ≤ R) →
    (S.card : ℝ) ≤ 9 * Real.pi * R ^ 2 / length y
  small_count : ∀ (S : Finset IntVector) (R : ℝ), first ≤ R → R < second →
    (∀ v ∈ S, v ⬝ᵥ y = 0 ∧ length v ≤ R) →
    (S.card : ℝ) ≤ 3 * R / first

theorem affine_plane_card_le (y : IntVector) (d : PlaneData y)
    (S : Finset IntVector) (center : EuclideanSpace ℝ (Fin 3))
    (R : ℝ) (hR : d.second ≤ R)
    (hsize : ∀ v ∈ S, ‖LatticeBox.realVector v - center‖ ≤ R)
    (hplane : ∀ v ∈ S, ∀ w ∈ S, (v - w) ⬝ᵥ y = 0) :
    (S.card : ℝ) ≤ 36 * Real.pi * R ^ 2 / length y := by
  classical
  have hR0 : 0 ≤ R := (show (0 : ℝ) ≤ 1 by norm_num).trans
    (d.one_le_first.trans (d.first_le_second.trans hR))
  by_cases hS : S.Nonempty
  · obtain ⟨w, hw⟩ := hS
    let T := S.image (fun v => v - w)
    have hcard : T.card = S.card := Finset.card_image_of_injective _
      (fun _ _ h => sub_left_inj.mp h)
    have hT (v : IntVector) (hv : v ∈ T) :
        v ⬝ᵥ y = 0 ∧ length v ≤ 2 * R := by
      obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hv
      refine ⟨hplane u hu w hw, ?_⟩
      have hcast : LatticeBox.realVector (u - w) =
          LatticeBox.realVector u - LatticeBox.realVector w := by
        ext i
        simp [LatticeBox.realVector]
      change ‖LatticeBox.realVector (u - w)‖ ≤ 2 * R
      rw [hcast]
      rw [show LatticeBox.realVector u - LatticeBox.realVector w =
        (LatticeBox.realVector u - center) - (LatticeBox.realVector w - center) by abel]
      exact (norm_sub_le _ _).trans (by linarith [hsize u hu, hsize w hw])
    have h := d.large_count T (2 * R) (by linarith) hT
    rw [hcard] at h
    convert h using 1; ring
  · have hzero : S = ∅ := Finset.not_nonempty_iff_eq_empty.mp hS
    rw [hzero]
    simp only [Finset.card_empty, Nat.cast_zero]
    positivity

end Problem355.Anisotropic

end

end OAI
