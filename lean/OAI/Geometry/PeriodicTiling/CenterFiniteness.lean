import OAI.Geometry.PeriodicTiling.EuclideanBasic
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Data.Int.Interval
import Mathlib.Data.Pi.Interval
import Mathlib.Data.Set.Countable
import Mathlib.Tactic.Linarith

namespace OAI

noncomputable section

namespace PeriodicTilingThree

def centerBoxIndex {n : ℕ} (r : ℝ) (x : Space n) : Lattice n :=
  fun i => ⌊x i / r⌋

theorem norm_sub_lt_of_centerBoxIndex_eq {n : ℕ} {r : ℝ} (hr : 0 < r)
    {x y : Space n} (hxy : centerBoxIndex r x = centerBoxIndex r y) :
    ‖x - y‖ < r := by
  apply (pi_norm_lt_iff hr).mpr
  intro i
  have heq : ⌊x i / r⌋ = ⌊y i / r⌋ := congrFun hxy i
  have hxl := Int.floor_le (x i / r)
  have hxu := Int.lt_floor_add_one (x i / r)
  have hyl := Int.floor_le (y i / r)
  have hyu := Int.lt_floor_add_one (y i / r)
  rw [← heq] at hyl hyu
  have hxl' := (le_div_iff₀ hr).mp hxl
  have hxu' := (div_lt_iff₀ hr).mp hxu
  have hyl' := (le_div_iff₀ hr).mp hyl
  have hyu' := (div_lt_iff₀ hr).mp hyu
  simp only [Pi.sub_apply, Real.norm_eq_abs]
  apply abs_lt.mpr
  constructor <;> nlinarith

theorem centerBoxIndex_injOn {n : ℕ} {C : Set (Space n)} {r : ℝ}
    (hr : 0 < r) (hsep : C.Pairwise (fun x y => r ≤ ‖x - y‖)) :
    Set.InjOn (centerBoxIndex r) C := by
  intro x hx y hy hxy
  by_contra hne
  exact (not_lt_of_ge (hsep hx hy hne)) (norm_sub_lt_of_centerBoxIndex_eq hr hxy)

theorem centers_countable {n : ℕ} {C : Set (Space n)} {r : ℝ}
    (hr : 0 < r) (hsep : C.Pairwise (fun x y => r ≤ ‖x - y‖)) : C.Countable := by
  apply Set.countable_of_injective_of_countable_image (centerBoxIndex_injOn hr hsep)
  exact Set.to_countable _

theorem centerBoxIndex_image_finite {n : ℕ} {r : ℝ} (hr : 0 < r)
    {K : Set (Space n)} (hK : Bornology.IsBounded K) :
    (centerBoxIndex r '' K).Finite := by
  obtain ⟨R, hR⟩ := hK.exists_norm_le
  let lo : Lattice n := fun _ => ⌊-R / r⌋
  let hi : Lattice n := fun _ => ⌊R / r⌋
  apply (Set.finite_Icc lo hi).subset
  rintro z ⟨x, hx, rfl⟩
  have hcoord (i : Fin n) : |x i| ≤ R := by
    calc
      |x i| = ‖x i‖ := by simp only [Real.norm_eq_abs]
      _ ≤ ‖x‖ := norm_le_pi_norm x i
      _ ≤ R := hR x hx
  constructor
  · intro i
    change ⌊-R / r⌋ ≤ ⌊x i / r⌋
    exact Int.floor_mono (div_le_div_of_nonneg_right (abs_le.mp (hcoord i)).1 hr.le)
  · intro i
    change ⌊x i / r⌋ ≤ ⌊R / r⌋
    exact Int.floor_mono (div_le_div_of_nonneg_right (abs_le.mp (hcoord i)).2 hr.le)

theorem centers_finite_on_bounded {n : ℕ} {C K : Set (Space n)} {r : ℝ}
    (hr : 0 < r) (hsep : C.Pairwise (fun x y => r ≤ ‖x - y‖))
    (hK : Bornology.IsBounded K) : (C ∩ K).Finite := by
  have hfin : (centerBoxIndex r '' (C ∩ K)).Finite :=
    (centerBoxIndex_image_finite hr hK).subset (Set.image_mono Set.inter_subset_right)
  exact hfin.of_finite_image ((centerBoxIndex_injOn hr hsep).mono Set.inter_subset_left)

end PeriodicTilingThree

end

end OAI
