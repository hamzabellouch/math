import OAI.Analysis.GroupDeterminants.ProductSupport

namespace OAI

universe uH

noncomputable section
open scoped BigOperators Pointwise

namespace LampDraft
variable (H : Type uH) [Group H]
local instance : DecidableEq H := Classical.decEq H
abbrev FullLamp := Multiplicative (ZMod 3) ≀ᵣ H

def coordinate (h : H) : FullLamp H := by
  classical
  exact ⟨fun t => if t = h then Multiplicative.ofAdd 1 else 1, 1⟩

def lampSubgroup : Subgroup (FullLamp H) :=
  (RegularWreathProduct.inl : H →* FullLamp H).range ⊔
    Subgroup.closure {coordinate H 1}

abbrev LampGroup := lampSubgroup H

instance lampGroup_fg [Group.FG H] : Group.FG (LampGroup H) := by
  apply (Group.fg_iff_subgroup_fg _).mpr
  apply Subgroup.FG.sup
  · exact (Group.fg_iff_subgroup_fg _).mp inferInstance
  · exact ⟨{coordinate H 1}, by simp⟩

def shift : H →* LampGroup H :=
  (RegularWreathProduct.inl : H →* FullLamp H).codRestrict (lampSubgroup H)
    (fun h => (show (RegularWreathProduct.inl : H →* FullLamp H).range ≤ lampSubgroup H from le_sup_left) (show RegularWreathProduct.inl h ∈
      (RegularWreathProduct.inl : H →* FullLamp H).range from ⟨h, rfl⟩))

def lampSeed : LampGroup H := ⟨coordinate H 1,
  (show Subgroup.closure {coordinate H 1} ≤ lampSubgroup H from le_sup_right)
    (Subgroup.subset_closure (Set.mem_singleton _))⟩

def lamp (h : H) : LampGroup H := shift H h * lampSeed H * (shift H h)⁻¹

@[simp] theorem shift_coe (h : H) : (shift H h : FullLamp H) = RegularWreathProduct.inl h := rfl

@[simp] theorem lamp_coe (h : H) : (lamp H h : FullLamp H) = coordinate H h := by
  classical
  apply RegularWreathProduct.ext
  · funext t
    simp only [lamp, Subgroup.coe_mul, Subgroup.coe_inv, shift_coe, lampSeed,
      RegularWreathProduct.mul_left, RegularWreathProduct.mul_right,
      RegularWreathProduct.left_inl, RegularWreathProduct.right_inl,
      RegularWreathProduct.inv_left, Pi.mul_apply, Pi.one_apply,
      Pi.inv_apply, inv_one, mul_one, one_mul, coordinate, inv_mul_eq_one, eq_comm]
  · simp [lamp, lampSeed, coordinate]

theorem lamp_commute (g h : H) : Commute (lamp H g) (lamp H h) := by
  classical
  apply Subtype.ext
  ext t <;> simp [lamp_coe, coordinate, mul_comm]

theorem lamp_cube (h : H) : lamp H h ^ 3 = 1 := by
  classical
  apply Subtype.ext
  simp only [Subgroup.coe_pow, lamp_coe, Subgroup.coe_one]
  simp only [pow_succ, pow_zero, one_mul]
  ext t
  · by_cases ht : t = h
    · subst t
      norm_num [coordinate]
      decide
    · simp [coordinate, ht]
  · simp [coordinate]

theorem shift_conjugate_lamp (s h : H) :
    shift H s * lamp H h * (shift H s)⁻¹ = lamp H (s * h) := by
  simp only [lamp, map_mul, mul_inv_rev]
  group

theorem shift_injective : Function.Injective (shift H) := by
  intro a b hab
  exact congrArg (fun g : LampGroup H => (g : FullLamp H).right) hab

def lampRight : LampGroup H →* H :=
  (RegularWreathProduct.rightHom : FullLamp H →* H).comp (lampSubgroup H).subtype

abbrev BaseGroup := (lampRight H).ker

instance baseGroup_commGroup : CommGroup (BaseGroup H) :=
  { (inferInstance : Group (BaseGroup H)) with
    mul_comm := by
      intro a b
      apply Subtype.ext
      apply Subtype.ext
      apply RegularWreathProduct.ext
      · funext t
        have ha : ((a : LampGroup H) : FullLamp H).right = 1 := a.property
        have hb : ((b : LampGroup H) : FullLamp H).right = 1 := b.property
        simp [RegularWreathProduct.mul_left, ha, hb, mul_comm]
      · change ((a : LampGroup H) : FullLamp H).right * ((b : LampGroup H) : FullLamp H).right =
          ((b : LampGroup H) : FullLamp H).right * ((a : LampGroup H) : FullLamp H).right
        have ha : ((a : LampGroup H) : FullLamp H).right = 1 := a.property
        have hb : ((b : LampGroup H) : FullLamp H).right = 1 := b.property
        rw [ha, hb] }

def baseLamp (h : H) : BaseGroup H := ⟨lamp H h, by
  change ((lamp H h : LampGroup H) : FullLamp H).right = 1
  rw [lamp_coe]; rfl⟩

def baseCoordinate (h : H) : BaseGroup H →* Multiplicative (ZMod 3) where
  toFun a := ((a : LampGroup H) : FullLamp H).left h
  map_one' := rfl
  map_mul' a b := by
    have ha : ((a : LampGroup H) : FullLamp H).right = 1 := a.property
    change (((a : LampGroup H) : FullLamp H).left h *
      ((b : LampGroup H) : FullLamp H).left (((a : LampGroup H) : FullLamp H).right⁻¹ * h)) = _
    simp [ha]

@[simp] lemma baseCoordinate_baseLamp (h t : H) :
    baseCoordinate H t (baseLamp H h) = if t = h then Multiplicative.ofAdd 1 else 1 := by
  classical
  change (lamp H h : FullLamp H).left t = _
  rw [lamp_coe]; rfl

lemma baseCoordinate_injective {a b : BaseGroup H}
    (h : ∀ t, baseCoordinate H t a = baseCoordinate H t b) : a = b := by
  apply Subtype.ext
  apply Subtype.ext
  apply RegularWreathProduct.ext
  · exact funext h
  · exact a.property.trans b.property.symm

lemma baseLamp_cube (h : H) : baseLamp H h ^ 3 = 1 := by
  apply Subtype.ext
  exact lamp_cube H h

lemma baseLamp_ne_one (h : H) : baseLamp H h ≠ 1 := by
  intro he
  have he' := congrArg (baseCoordinate H h) he
  norm_num at he'

lemma baseLamp_sq_ne_one (h : H) : baseLamp H h * baseLamp H h ≠ 1 := by
  intro he
  have he' := congrArg (baseCoordinate H h) he
  norm_num at he'
  exact (by decide : Multiplicative.ofAdd (1 : ZMod 3) * Multiplicative.ofAdd 1 ≠ 1) he'

end LampDraft

end

end OAI
