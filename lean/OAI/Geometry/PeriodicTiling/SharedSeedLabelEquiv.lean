import OAI.Geometry.PeriodicTiling.SharedSeedLabels
import OAI.Geometry.PeriodicTiling.SharedSeedInactive

namespace OAI

universe uK uΔ

noncomputable section

namespace PeriodicTilingThree.SharedSeed

variable {K : Type uK} {Δ : Type uΔ} [AddCommGroup K] {m b : ℕ}

def oneLabelEquiv (S : BlockShiftData Δ 2 b) (x : ℤ) (k : K)
    (B : ZMod 3 → (K × Δ) ≃ ((ZMod 2 × ZMod b) × K)) :
    ((K × Δ) × LabelledResidue m) ≃ (((ZMod 2 × ZMod b) × K) × LabelledResidue m) where
  toFun
    | (v, Sum.inl y) => (B y v, Sum.inl (y + (x : ZMod 3)))
    | (v, Sum.inr (Sum.inl (c, y))) =>
        let w := inactiveEquiv S (x : ZMod 2) k (v, y)
        (w.1, Sum.inr (Sum.inl (c, w.2)))
    | (v, Sum.inr (Sum.inr (c, y, z))) =>
        let w := inactiveEquiv S (x : ZMod 2) k (v, y)
        (w.1, Sum.inr (Sum.inr (c, w.2, z + (x : ZMod 3))))
  invFun
    | (v, Sum.inl q) => ((B (q - (x : ZMod 3))).symm v, Sum.inl (q - (x : ZMod 3)))
    | (v, Sum.inr (Sum.inl (c, q))) =>
        let w := (inactiveEquiv S (x : ZMod 2) k).symm (v, q)
        (w.1, Sum.inr (Sum.inl (c, w.2)))
    | (v, Sum.inr (Sum.inr (c, q, r))) =>
        let w := (inactiveEquiv S (x : ZMod 2) k).symm (v, q)
        (w.1, Sum.inr (Sum.inr (c, w.2, r - (x : ZMod 3))))
  left_inv v := by
    rcases v with ⟨v, y | (⟨c, y⟩ | ⟨c, y, z⟩)⟩
    · simp only [add_sub_cancel_right, Equiv.symm_apply_apply]
    · simp only [Prod.mk.eta, Equiv.symm_apply_apply]
    · simp only [Prod.mk.eta, Equiv.symm_apply_apply, add_sub_cancel_right]
  right_inv v := by
    rcases v with ⟨v, q | (⟨c, q⟩ | ⟨c, q, r⟩)⟩
    · simp only [Equiv.apply_symm_apply, sub_add_cancel]
    · simp only [Prod.mk.eta, Equiv.apply_symm_apply]
    · simp only [Prod.mk.eta, Equiv.apply_symm_apply, sub_add_cancel]

def twoLabelEquiv (S : BlockShiftData Δ 3 b) (x : ℤ) (k : K)
    (B : (Fin 2 × ZMod 2) → (K × Δ) ≃ ((ZMod 3 × ZMod b) × K)) :
    ((K × Δ) × LabelledResidue m) ≃ (((ZMod 3 × ZMod b) × K) × LabelledResidue m) where
  toFun
    | (v, Sum.inl y) =>
        let w := inactiveEquiv S (x : ZMod 3) k (v, y)
        (w.1, Sum.inl w.2)
    | (v, Sum.inr (Sum.inl (c, y))) =>
        (B (c, y) v, Sum.inr (Sum.inl (c, y + (x : ZMod 2))))
    | (v, Sum.inr (Sum.inr (c, y, z))) =>
        let w := inactiveEquiv S (x : ZMod 3) k (v, z)
        (w.1, Sum.inr (Sum.inr (c, y + (x : ZMod 2), w.2)))
  invFun
    | (v, Sum.inl q) =>
        let w := (inactiveEquiv S (x : ZMod 3) k).symm (v, q)
        (w.1, Sum.inl w.2)
    | (v, Sum.inr (Sum.inl (c, q))) =>
        ((B (c, q - (x : ZMod 2))).symm v,
          Sum.inr (Sum.inl (c, q - (x : ZMod 2))))
    | (v, Sum.inr (Sum.inr (c, q, r))) =>
        let w := (inactiveEquiv S (x : ZMod 3) k).symm (v, r)
        (w.1, Sum.inr (Sum.inr (c, q - (x : ZMod 2), w.2)))
  left_inv v := by
    rcases v with ⟨v, y | (⟨c, y⟩ | ⟨c, y, z⟩)⟩
    · simp only [Prod.mk.eta, Equiv.symm_apply_apply]
    · simp only [add_sub_cancel_right, Equiv.symm_apply_apply]
    · simp only [Prod.mk.eta, Equiv.symm_apply_apply, add_sub_cancel_right]
  right_inv v := by
    rcases v with ⟨v, q | (⟨c, q⟩ | ⟨c, q, r⟩)⟩
    · simp only [Prod.mk.eta, Equiv.apply_symm_apply]
    · simp only [Equiv.apply_symm_apply, sub_add_cancel]
    · simp only [Prod.mk.eta, Equiv.apply_symm_apply, sub_add_cancel]

end PeriodicTilingThree.SharedSeed

end

end OAI
