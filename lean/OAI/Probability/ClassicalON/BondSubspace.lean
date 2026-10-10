import OAI.Probability.ClassicalON.PinnedCylinder

namespace OAI

universe uE uV

noncomputable section
open scoped BigOperators
namespace ClassicalON

abbrev SignField := ZMod 2

variable {V : Type uV} {E : Type uE}

def bondSubspace (left right : E → V) (η : E → Bool) : Submodule SignField (V → SignField) where
  carrier := {s | ∀ e,η e=true → s (left e)=s (right e)}
  zero_mem' := by simp
  add_mem' := by intro f g hf hg e he; simp only [Pi.add_apply,hf e he,hg e he]
  smul_mem' := by intro c f hf e he; simp only [Pi.smul_apply,hf e he]

@[simp] theorem mem_bondSubspace (left right : E → V) (η : E → Bool) (s : V → SignField) :
    s∈bondSubspace left right η ↔ ∀ e,η e=true → s (left e)=s (right e) := Iff.rfl

theorem bondSubspace_antitone (left right : E → V) : Antitone (bondSubspace left right) := by
  intro η ξ h s hs e he
  apply hs e
  have hh := h e
  rw [he] at hh
  exact le_antisymm (show ξ e ≤ true from Bool.le_true _) hh

theorem bondSubspace_sup (left right : E → V) (η ξ : E → Bool) :
    bondSubspace left right (η⊔ξ)=bondSubspace left right η⊓bondSubspace left right ξ := by
  apply le_antisymm
  · exact le_inf (bondSubspace_antitone left right le_sup_left) (bondSubspace_antitone left right le_sup_right)
  · intro s hs e he
    have ht : η e=true ∨ ξ e=true := by simpa using he
    rcases ht with ht | ht
    · exact hs.1 e ht
    · exact hs.2 e ht

variable [Fintype V]

def bondRank (left right : E → V) (η : E → Bool) : ℕ :=
  Module.finrank SignField (bondSubspace left right η)

theorem bondRank_supermodular (left right : E → V) (η ξ : E → Bool) :
    bondRank left right η+bondRank left right ξ≤
      bondRank left right (η⊓ξ)+bondRank left right (η⊔ξ) := by
  unfold bondRank
  rw [bondSubspace_sup,← Submodule.finrank_sup_add_finrank_inf_eq]
  apply Nat.add_le_add_right
  apply Submodule.finrank_mono
  exact sup_le (bondSubspace_antitone left right inf_le_left) (bondSubspace_antitone left right inf_le_right)

def clusterWeight (left right : E → V) (η : E → Bool) : ℝ :=
  2^bondRank left right η

omit [Fintype V] in
theorem clusterWeight_pos (left right : E → V) (η : E → Bool) : 0<clusterWeight left right η := by
  unfold clusterWeight; positivity

theorem clusterWeight_supermodular (left right : E → V) (η ξ : E → Bool) :
    clusterWeight left right η*clusterWeight left right ξ≤
      clusterWeight left right (η⊓ξ)*clusterWeight left right (η⊔ξ) := by
  unfold clusterWeight
  rw [← pow_add,← pow_add]
  exact pow_le_pow_right₀ (by norm_num) (bondRank_supermodular left right η ξ)

end ClassicalON

end

end OAI
