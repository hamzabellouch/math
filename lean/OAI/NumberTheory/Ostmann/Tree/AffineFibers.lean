import Mathlib

namespace OAI

namespace Ostmann.FiniteField
noncomputable section
open scoped BigOperators
variable {F : Type*} [Field F]

def affinePair (r s : Fˣ) : F × F :=
  (((s : F) / r)^2, (s : F) - (s : F)^2 / r)

def affineRatio (rs : Fˣ × Fˣ) : F := (rs.2 : F) / rs.1

theorem affinePair_shift (r s : Fˣ) :
    (affinePair r s).2 = (r : F) * (affineRatio (r,s) - affineRatio (r,s)^2) := by
  dsimp [affinePair, affineRatio]
  field_simp

theorem affineRatio_ne_zero (rs : Fˣ × Fˣ) : affineRatio rs ≠ 0 :=
  div_ne_zero (Units.ne_zero _) (Units.ne_zero _)

theorem affinePair_eq_identity_of_ratio_one {r s : Fˣ}
    (h : affineRatio (r,s) = 1) : affinePair r s = (1,0) := by
  apply Prod.ext
  · change affineRatio (r,s)^2 = 1
    rw [h, one_pow]
  · rw [affinePair_shift, h]
    ring

theorem affinePair_ratio_injective {K : F × F} (hK : K ≠ (1,0))
    {rs rt : Fˣ × Fˣ} (hs : affinePair rs.1 rs.2 = K)
    (ht : affinePair rt.1 rt.2 = K) (hz : affineRatio rs = affineRatio rt) : rs = rt := by
  have hone : affineRatio rs ≠ 1 := by
    intro h
    exact hK (hs.symm.trans (affinePair_eq_identity_of_ratio_one h))
  have hz0 := affineRatio_ne_zero rs
  have hfactor : affineRatio rs - affineRatio rs ^ 2 ≠ 0 := by
    intro h
    have : affineRatio rs * (1 - affineRatio rs) = 0 := by
      calc
        affineRatio rs * (1 - affineRatio rs) = affineRatio rs - affineRatio rs ^ 2 := by ring
        _ = 0 := h
    rcases mul_eq_zero.mp this with he | he
    · exact hz0 he
    · exact hone (sub_eq_zero.mp he).symm
  have hshift := congrArg Prod.snd (hs.trans ht.symm)
  rw [affinePair_shift, affinePair_shift, ← hz] at hshift
  have hr : (rs.1 : F) = rt.1 := (mul_right_cancel₀ hfactor) hshift
  have hsval : (rs.2 : F) = rt.2 := by
    dsimp [affineRatio] at hz
    rw [hr] at hz
    exact (div_left_inj' (Units.ne_zero rt.1)).mp hz
  exact Prod.ext (Units.ext hr) (Units.ext hsval)

theorem affinePair_fiber_card_le_two (S : Finset (Fˣ × Fˣ)) (K : F × F)
    (hK : K ≠ (1,0)) (hS : ∀ rs ∈ S, affinePair rs.1 rs.2 = K) : S.card ≤ 2 := by
  classical
  by_cases he : S.Nonempty
  · obtain ⟨rs, hrs⟩ := he
    have hi : Set.InjOn affineRatio (↑S : Set (Fˣ × Fˣ)) := by
      intro x hx y hy hxy
      exact affinePair_ratio_injective hK (hS x hx) (hS y hy) hxy
    have hc : S.card = (S.image affineRatio).card := (Finset.card_image_of_injOn hi).symm
    rw [hc]
    calc
      (S.image affineRatio).card ≤ ({affineRatio rs, -affineRatio rs} : Finset F).card := by
        apply Finset.card_le_card
        intro z hz
        obtain ⟨rt, hrt, rfl⟩ := Finset.mem_image.mp hz
        have hh := congrArg Prod.fst ((hS rt hrt).trans (hS rs hrs).symm)
        change affineRatio rt ^ 2 = affineRatio rs ^ 2 at hh
        rcases sq_eq_sq_iff_eq_or_eq_neg.mp hh with h | h <;> simp [h]
      _ ≤ 2 := Finset.card_le_two
  · simp [Finset.not_nonempty_iff_eq_empty.mp he]

def affineUnitSubstitution (r : Fˣ) (x : F) : F := (r : F) - (r : F)^2*x

def inverseAffineUnitSubstitution (r : Fˣ) (x : F) : F :=
  ((r : F) - x) / (r : F)^2

theorem affineUnitSubstitution_inverse (r : Fˣ) (x : F) :
    affineUnitSubstitution r (inverseAffineUnitSubstitution r x) = x := by
  dsimp [affineUnitSubstitution, inverseAffineUnitSubstitution]
  field_simp
  ring

theorem inverseAffineUnitSubstitution_affine (r : Fˣ) (x : F) :
    inverseAffineUnitSubstitution r (affineUnitSubstitution r x) = x := by
  dsimp [affineUnitSubstitution, inverseAffineUnitSubstitution]
  field_simp
  ring

theorem affineUnitSubstitution_composition (r s : Fˣ) (x : F) :
    affineUnitSubstitution s (inverseAffineUnitSubstitution r x) =
      (affinePair r s).1*x + (affinePair r s).2 := by
  dsimp [affineUnitSubstitution, inverseAffineUnitSubstitution, affinePair]
  field_simp
  ring

end
end Ostmann.FiniteField

end OAI
