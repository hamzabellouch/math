import OAI.Probability.ClassicalON.SpinBonds

namespace OAI

universe uE uV

noncomputable section
open scoped BigOperators Classical
namespace ClassicalON

variable {V : Type uV} {E : Type uE} [Fintype V]

def pinRestriction (B : Set V) : (V → SignField) →ₗ[SignField] (B → SignField) where
  toFun s := fun v => s v
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def bondPinRank (left right : E → V) (B : Set V) (η : E → Bool) : ℕ :=
  Module.finrank SignField ((bondSubspace left right η).map (pinRestriction B))

def bondPinFactor (left right : E → V) (B : Set V) (η : E → Bool) : ℝ :=
  (2^bondPinRank left right B η)⁻¹

omit [Fintype V] in
theorem bondPinFactor_pos (left right : E → V) (B : Set V) (η : E → Bool) :
    0 < bondPinFactor left right B η := by unfold bondPinFactor; positivity

theorem bondPinRank_antitone (left right : E → V) (B : Set V) :
    Antitone (bondPinRank left right B) := by
  intro η ξ h
  apply Submodule.finrank_mono
  exact Submodule.map_mono (bondSubspace_antitone left right h)

theorem bondPinFactor_monotone (left right : E → V) (B : Set V) :
    Monotone (bondPinFactor left right B) := by
  intro η ξ h
  apply inv_anti₀ (by positivity : 0 < (2:ℝ)^bondPinRank left right B ξ)
  exact pow_le_pow_right₀ (by norm_num) (bondPinRank_antitone left right B h)

def pinnedBondSubspace (left right : E → V) (B : Set V) (η : E → Bool) :
    Submodule SignField (V → SignField) :=
  bondSubspace left right η⊓LinearMap.ker (pinRestriction B)

theorem pinnedBond_rank_add (left right : E → V) (B : Set V) (η : E → Bool) :
    Module.finrank SignField (pinnedBondSubspace left right B η)+bondPinRank left right B η =
      bondRank left right η := by
  let K := bondSubspace left right η
  let f := (pinRestriction B).domRestrict K
  have hk : LinearMap.ker f=(pinnedBondSubspace left right B η).comap K.subtype := by
    ext s
    simp [f,pinnedBondSubspace,K]
  have hh := LinearMap.finrank_range_add_finrank_ker f
  rw [show LinearMap.range f=K.map (pinRestriction B) from LinearMap.range_domRestrict K _,hk,
    (Submodule.comapSubtypeEquivOfLe (show pinnedBondSubspace left right B η ≤ K from inf_le_left)).finrank_eq] at hh
  exact (Nat.add_comm _ _).trans hh

theorem pinnedBond_card (left right : E → V) (B : Set V) (η : E → Bool) :
    (Fintype.card (pinnedBondSubspace left right B η) : ℝ)=
      clusterWeight left right η*bondPinFactor left right B η := by
  rw [Module.card_eq_pow_finrank (K := SignField)]
  simp only [SignField,ZMod.card,Nat.cast_pow,Nat.cast_ofNat]
  unfold clusterWeight bondPinFactor
  rw [← pinnedBond_rank_add left right B η,pow_add,mul_assoc,mul_inv_cancel₀ (by positivity),mul_one]

end ClassicalON

end

end OAI
