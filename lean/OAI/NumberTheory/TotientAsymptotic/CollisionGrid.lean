import OAI.NumberTheory.TotientAsymptotic.CollisionSlack
import Mathlib.Algebra.Order.Floor.Semiring

namespace OAI

/-! Finite interval choices for the paired normalized largest factors. -/

noncomputable section
open scoped BigOperators

namespace TotientAsymptotic

def collisionGridIndex (δ u v : ℝ) : ℕ := ⌊min u v/δ⌋₊

def collisionGridLower (δ : ℝ) (n : ℕ) : ℝ := δ*n

def collisionGridUpper (δ : ℝ) (J n : ℕ) : ℝ := δ*(n+2*J+3 : ℕ)

lemma collision_grid_lower_bounds {δ u v : ℝ} (hδ : 0 < δ) (hu : 0 ≤ u) (hv : 0 ≤ v) :
    collisionGridLower δ (collisionGridIndex δ u v) ≤ min u v ∧
    min u v < collisionGridLower δ (collisionGridIndex δ u v)+δ := by
  have hmin : 0 ≤ min u v := le_min hu hv
  have hlo := Nat.floor_le (div_nonneg hmin hδ.le)
  have hhi := Nat.lt_floor_add_one (min u v/δ)
  constructor
  · simpa only [collisionGridLower,collisionGridIndex,mul_comm] using (le_div_iff₀ hδ).mp hlo
  · have hh := (div_lt_iff₀ hδ).mp hhi
    rw [add_mul,one_mul] at hh
    simpa only [collisionGridLower,collisionGridIndex,mul_comm] using hh

/-- The paired largest factors fit in one of finitely many grid intervals.
The width retains the full alignment error and one rounding cell. -/
theorem collision_grid_enclosure {δ u v : ℝ} {J : ℕ}
    (hδ : 0 < δ) (hu : 0 ≤ u) (hv : 0 ≤ v)
    (hclose : |u-v| ≤ (2*(J : ℝ)+1)*δ) :
    let n := collisionGridIndex δ u v
    collisionGridLower δ n ≤ u ∧ collisionGridLower δ n ≤ v ∧
    u < collisionGridUpper δ J n ∧ v < collisionGridUpper δ J n ∧
    collisionGridUpper δ J n ≤ u+(2*(J : ℝ)+3)*δ := by
  dsimp only
  obtain ⟨hlo,hhi⟩ := collision_grid_lower_bounds hδ hu hv
  have hmax : max u v ≤ min u v+(2*(J : ℝ)+1)*δ := by
    rcases le_total u v with h | h
    · rw [min_eq_left h,max_eq_right h]
      linarith [(abs_le.mp hclose).1]
    · rw [min_eq_right h,max_eq_left h]
      linarith [(abs_le.mp hclose).2]
  have he : collisionGridUpper δ J (collisionGridIndex δ u v) =
      collisionGridLower δ (collisionGridIndex δ u v)+(2*(J : ℝ)+3)*δ := by
    simp only [collisionGridUpper,collisionGridLower,Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat]
    ring
  rw [he]
  exact ⟨hlo.trans (min_le_left _ _),hlo.trans (min_le_right _ _),
    by linarith [le_max_left u v],by linarith [le_max_right u v],
    by linarith [min_le_left u v]⟩

lemma collisionGridIndex_le {δ u v : ℝ} (hδ : 0 < δ) (hu : u ≤ 1) :
    collisionGridIndex δ u v ≤ ⌊1/δ⌋₊ := by
  exact Nat.floor_mono (div_le_div_of_nonneg_right ((min_le_left u v).trans hu) hδ.le)

/-- Disjoint largest-factor bands remain strictly ordered after gridding,
provided their gap exceeds the explicit alignment and rounding costs. -/
lemma collision_grid_separated {δ u v u' v' : ℝ} {J : ℕ}
    (hδ : 0 < δ) (hu : 0 ≤ u) (hv : 0 ≤ v) (hu' : 0 ≤ u') (hv' : 0 ≤ v')
    (hclose' : |u'-v'| ≤ (2*(J : ℝ)+1)*δ)
    (hgap : max u' v'+(2*(J : ℝ)+4)*δ < min u v) :
    collisionGridUpper δ J (collisionGridIndex δ u' v') <
      collisionGridLower δ (collisionGridIndex δ u v) := by
  have hprev := (collision_grid_lower_bounds hδ hu hv).2
  have hnext := (collision_grid_enclosure hδ hu' hv' hclose').2.2.2.2
  linarith [le_max_left u' v']

def collisionGridFamilies (δ : ℝ) (b : ℕ) : Finset (Fin b → ℕ) :=
  Fintype.piFinset (fun _ => Finset.range (⌊1/δ⌋₊+1))

lemma collisionGridFamilies_card (δ : ℝ) (b : ℕ) :
    (collisionGridFamilies δ b).card = (⌊1/δ⌋₊+1)^b := by
  simp [collisionGridFamilies]

lemma collisionGridFamilies_mem {δ : ℝ} {b : ℕ} (hδ : 0 < δ) (u v : Fin b → ℝ)
    (hu : ∀ j, u j ≤ 1) :
    (fun j => collisionGridIndex δ (u j) (v j)) ∈ collisionGridFamilies δ b := by
  apply Fintype.mem_piFinset.mpr
  intro j
  exact Finset.mem_range.mpr (Nat.lt_succ_of_le (collisionGridIndex_le hδ (hu j)))

end TotientAsymptotic

end

end OAI
