import OAI.Geometry.PeriodicTiling.BlockActivationInverse
import Mathlib.Tactic.Abel

namespace OAI

universe uK uΔ

noncomputable section

namespace PeriodicTilingThree.SharedSeed

variable {K : Type uK} {Δ : Type uΔ} [AddCommGroup K] {a b : ℕ}

def inactiveForward (S : BlockShiftData Δ a b) (x : ZMod a) (k : K)
    (v : (K × Δ) × ZMod a) : ((ZMod a × ZMod b) × K) × ZMod a :=
  ((((v.2 + (S.e v.1.2).1), (S.e v.1.2).2), k - v.1.1),
    v.2 + x - S.rhoA v.1.2)

def inactiveInverse (S : BlockShiftData Δ a b) (x : ZMod a) (k : K)
    (v : ((ZMod a × ZMod b) × K) × ZMod a) : (K × Δ) × ZMod a :=
  let δ := S.orderA.symm (v.1.1.2, v.1.1.1 + x - v.2)
  ((k - v.1.2, δ), v.1.1.1 - (S.e δ).1)

theorem inactiveInverse_forward (S : BlockShiftData Δ a b) (x : ZMod a) (k : K)
    (v : (K × Δ) × ZMod a) :
    inactiveInverse S x k (inactiveForward S x k v) = v := by
  rcases v with ⟨⟨l, δ⟩, y⟩
  have hd : S.orderA.symm ((S.e δ).2,
      (y + (S.e δ).1) + x - (y + x - S.rhoA δ)) = δ := by
    apply S.orderA.injective
    rw [Equiv.apply_symm_apply, S.orderA_apply]
    apply Prod.ext
    · rfl
    · abel_nf
  dsimp [inactiveInverse, inactiveForward]
  rw [hd]
  simp

theorem inactiveForward_inverse (S : BlockShiftData Δ a b) (x : ZMod a) (k : K)
    (v : ((ZMod a × ZMod b) × K) × ZMod a) :
    inactiveForward S x k (inactiveInverse S x k v) = v := by
  rcases v with ⟨⟨⟨α, ξ⟩, β⟩, q⟩
  let δ := S.orderA.symm (ξ, α + x - q)
  have hd : ((S.e δ).2, (S.e δ).1 + S.rhoA δ) = (ξ, α + x - q) := by
    rw [← S.orderA_apply]
    exact S.orderA.apply_symm_apply _
  have hb : (S.e δ).2 = ξ := congrArg Prod.fst hd
  have ha : (S.e δ).1 + S.rhoA δ = α + x - q := congrArg Prod.snd hd
  have hq : α - (S.e δ).1 + x - S.rhoA δ = q := by
    calc
      α - (S.e δ).1 + x - S.rhoA δ = α + x - ((S.e δ).1 + S.rhoA δ) := by abel
      _ = α + x - (α + x - q) := by rw [ha]
      _ = q := by abel
  change ((((α - (S.e δ).1 + (S.e δ).1), (S.e δ).2), k - (k - β)),
    α - (S.e δ).1 + x - S.rhoA δ) = (((α, ξ), β), q)
  simp only [sub_add_cancel, sub_sub_cancel, hb, hq]

def inactiveEquiv (S : BlockShiftData Δ a b) (x : ZMod a) (k : K) :
    ((K × Δ) × ZMod a) ≃ (((ZMod a × ZMod b) × K) × ZMod a) where
  toFun := inactiveForward S x k
  invFun := inactiveInverse S x k
  left_inv := inactiveInverse_forward S x k
  right_inv := inactiveForward_inverse S x k

end PeriodicTilingThree.SharedSeed

end

end OAI
