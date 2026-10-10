import OAI.Geometry.TriangularCovering.Main
import OAI.Geometry.CylinderCovering.Angular.FamilyDefinitions

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped BigOperators

namespace TriangularCovering.AngularFamily

variable {n : ℕ}

def family (ε : ℝ) (a b A B R : Fin n → ℝ)
    (hab : ∀ j, a j < b j) (hR : ∀ j, 0 < R j) : Fin (2 * n) → TriCylinder :=
  (Fin.append
    (fun j => lowerCylinder (hab j) (hR j) ε (A j) (B j))
    (fun j => upperCylinder (hab j) (hR j) ε (A j) (B j))) ∘
      Fin.cast (two_mul n)

theorem total_area (ε : ℝ) (a b A B R : Fin n → ℝ)
    (hab : ∀ j, a j < b j) (hR : ∀ j, 0 < R j) :
    totalArea (family ε a b A B R hab hR) / H =
      ∑ j : Fin n, (b j - a j) * (R j)^2 /
        Real.sqrt (1 + ε^2 * ((A j)^2 + 2 * (B j)^2)) := by
  have hs : totalArea (family ε a b A B R hab hR) =
      (∑ j : Fin n, area (lowerCylinder (hab j) (hR j) ε (A j) (B j)).base) +
      (∑ j : Fin n, area (upperCylinder (hab j) (hR j) ε (A j) (B j)).base) := by
    change (∑ i : Fin (2 * n),
      (fun k : Fin (n + n) => area (Fin.append
        (fun j => lowerCylinder (hab j) (hR j) ε (A j) (B j))
        (fun j => upperCylinder (hab j) (hR j) ε (A j) (B j)) k).base)
          ((finCongr (two_mul n)) i)) = _
    rw [Equiv.sum_comp (finCongr (two_mul n))
      (fun k => area (Fin.append
        (fun j => lowerCylinder (hab j) (hR j) ε (A j) (B j))
        (fun j => upperCylinder (hab j) (hR j) ε (A j) (B j)) k).base)]
    rw [Fin.sum_univ_add]
    simp only [Fin.append_left, Fin.append_right]
  rw [hs, ← Finset.sum_add_distrib, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro j _
  rw [lowerCylinder_area, upperCylinder_area]
  field_simp [H_ne_zero]
  ring

theorem family_prescribed (ε : ℝ) (a b A B R : Fin n → ℝ)
    (hab : ∀ j, a j < b j) (hR : ∀ j, 0 < R j) :
    PrescribedFamily (family ε a b A B R hab hR) ε a b A B R := by
  constructor
  · intro j
    simp only [family,Function.comp_apply,Fin.cast_cast,Fin.cast_eq_self,Fin.append_left]
    exact ⟨rfl,rfl⟩
  · intro j
    simp only [family,Function.comp_apply,Fin.cast_cast,Fin.cast_eq_self,Fin.append_right]
    exact ⟨rfl,rfl⟩

theorem covers_of_coordinate_hits (ε : ℝ) (a b A B R : Fin n → ℝ)
    (hab : ∀ j, a j < b j) (hR : ∀ j, 0 < R j)
    (hcover : ∀ x y t : ℝ, |x| ≤ 1 - t → |y| ≤ t →
      (∃ j, LowerHit ε (a j) (b j) (A j) (B j) (R j) x y t) ∨
      (∃ j, UpperHit ε (a j) (b j) (A j) (B j) (R j) x y t)) :
    Covers (family ε a b A B R hab hR) := by
  rintro z ⟨x, y, t, _ht0, _ht1, hx, hy, rfl⟩
  rcases hcover x y t hx hy with ⟨j, hj⟩ | ⟨j, hj⟩
  · refine ⟨Fin.cast (two_mul n).symm (Fin.castAdd n j), ?_⟩
    simp only [family, Function.comp_apply, Fin.cast_cast, Fin.cast_eq_self,
      Fin.append_left]
    exact lowerCylinder_hit _ _ _ _ _ _ _ _ hj.1 hj.2.1 hj.2.2.1 hj.2.2.2
  · refine ⟨Fin.cast (two_mul n).symm (Fin.natAdd n j), ?_⟩
    simp only [family, Function.comp_apply, Fin.cast_cast, Fin.cast_eq_self,
      Fin.append_right]
    exact upperCylinder_hit _ _ _ _ _ _ _ _ hj.1 hj.2.1 hj.2.2.1 hj.2.2.2

theorem strict_bounds (ε : ℝ) (a b A B R : Fin n → ℝ)
    (hab : ∀ j, a j < b j) (hR : ∀ j, 0 < R j)
    (hcost : (∑ j : Fin n, (b j - a j) * (R j)^2 /
      Real.sqrt (1 + ε^2 * ((A j)^2 + 2 * (B j)^2))) < 1 / 2) :
    totalArea (family ε a b A B R hab hR) < A_min / 2 ∧
      relativeCost (family ε a b A B R hab hR) < 1 / 2 := by
  have hratio : totalArea (family ε a b A B R hab hR) / H < 1/2 := by
    rw [total_area]
    exact hcost
  constructor
  · rw [projection_minimum]
    have h := (div_lt_iff₀ H_pos).mp hratio
    linarith only [h]
  · exact (relativeCost_le_totalArea _).trans_lt hratio

end TriangularCovering.AngularFamily

end

end OAI
