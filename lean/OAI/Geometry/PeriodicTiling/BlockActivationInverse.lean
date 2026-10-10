import OAI.Geometry.PeriodicTiling.LabeledDigitBlocks
import OAI.Geometry.PeriodicTiling.ShiftMultiplicity
import Mathlib.Tactic.Abel

namespace OAI

universe uΔ uK uA uB

namespace PeriodicTilingThree

structure BlockShiftData (Δ : Type uΔ) (a b : ℕ) where
  e : Δ → ZMod a × ZMod b
  rhoA : Δ → ZMod a
  rhoB : Δ → ZMod b
  orderA : Δ ≃ (ZMod b × ZMod a)
  orderB : Δ ≃ (ZMod a × ZMod b)
  orderA_apply : ∀ δ, orderA δ = ((e δ).2, (e δ).1 + rhoA δ)
  orderB_apply : ∀ δ, orderB δ = ((e δ).1, (e δ).2 + rhoB δ)

namespace BlockShiftData

noncomputable def ofMultiplicity {a b : ℕ} [NeZero a] [NeZero b]
    (ha : 2 ≤ a) (hb : 2 ≤ b) : BlockShiftData (ShiftIndex a b) a b where
  e := shift a b
  rhoA := PeriodicTilingThree.rhoA ha hb
  rhoB := PeriodicTilingThree.rhoB ha hb
  orderA := shiftOrderA ha hb
  orderB := shiftOrderB ha hb
  orderA_apply := shiftOrderA_apply ha hb
  orderB_apply := shiftOrderB_apply ha hb

variable {K : Type uK} {A : Type uA} {B : Type uB} {Δ : Type uΔ} [AddCommGroup K] {a b : ℕ}

def blockForward (D : LabeledBlocks K A B a b) (S : BlockShiftData Δ a b)
    (H : K × Δ → ℤ) (x : ℤ) (k : K) (z : K × Δ) :
    (ZMod a × ZMod b) × K :=
  (D.C (k - z.1) + S.e z.2, D.T (x - H z) (k - z.1))

def blockInverse (D : LabeledBlocks K A B a b) (S : BlockShiftData Δ a b)
    (x : ℤ) (k : K) (v : (ZMod a × ZMod b) × K) : K × Δ :=
  match D.decode v.2 with
  | .inl (c, q) =>
      let δ := S.orderA.symm (v.1.2, v.1.1 + (x : ZMod a) - q)
      (k - D.decode.symm (.inl (c, v.1.1 - (S.e δ).1)), δ)
  | .inr (c, q) =>
      let δ := S.orderB.symm (v.1.1, v.1.2 + (x : ZMod b) - q)
      (k - D.decode.symm (.inr (c, v.1.2 - (S.e δ).2)), δ)

theorem blockInverse_inl (D : LabeledBlocks K A B a b) (S : BlockShiftData Δ a b)
    (x : ℤ) (k : K) (α : ZMod a) (ξ : ZMod b) (c : A) (q : ZMod a) :
    blockInverse D S x k ((α, ξ), D.decode.symm (.inl (c, q))) =
      let δ := S.orderA.symm (ξ, α + (x : ZMod a) - q)
      (k - D.decode.symm (.inl (c, α - (S.e δ).1)), δ) := by
  simp only [blockInverse, Equiv.apply_symm_apply]

theorem blockInverse_inr (D : LabeledBlocks K A B a b) (S : BlockShiftData Δ a b)
    (x : ℤ) (k : K) (α : ZMod a) (ξ : ZMod b) (c : B) (q : ZMod b) :
    blockInverse D S x k ((α, ξ), D.decode.symm (.inr (c, q))) =
      let δ := S.orderB.symm (α, ξ + (x : ZMod b) - q)
      (k - D.decode.symm (.inr (c, ξ - (S.e δ).2)), δ) := by
  simp only [blockInverse, Equiv.apply_symm_apply]

theorem blockForward_inl (D : LabeledBlocks K A B a b) (S : BlockShiftData Δ a b)
    (H : K × Δ → ℤ) (hA : ∀ z, (H z : ZMod a) = S.rhoA z.2)
    (x : ℤ) (k : K) (c : A) (y : ZMod a) (δ : Δ) :
    blockForward D S H x k (k - D.decode.symm (.inl (c, y)), δ) =
      ((y + (S.e δ).1, (S.e δ).2),
        D.decode.symm (.inl (c, y + (x : ZMod a) - S.rhoA δ))) := by
  simp [blockForward, Int.cast_sub, hA, add_sub_assoc]
  apply Prod.ext <;> simp

theorem blockForward_inr (D : LabeledBlocks K A B a b) (S : BlockShiftData Δ a b)
    (H : K × Δ → ℤ) (hB : ∀ z, (H z : ZMod b) = S.rhoB z.2)
    (x : ℤ) (k : K) (c : B) (y : ZMod b) (δ : Δ) :
    blockForward D S H x k (k - D.decode.symm (.inr (c, y)), δ) =
      (((S.e δ).1, y + (S.e δ).2),
        D.decode.symm (.inr (c, y + (x : ZMod b) - S.rhoB δ))) := by
  simp [blockForward, Int.cast_sub, hB, add_sub_assoc]
  apply Prod.ext <;> simp

theorem recoverA (S : BlockShiftData Δ a b) (δ : Δ) (y t : ZMod a) :
    S.orderA.symm ((S.e δ).2, (y + (S.e δ).1) + t -
      (y + t - S.rhoA δ)) = δ := by
  apply S.orderA.injective
  rw [Equiv.apply_symm_apply, S.orderA_apply]
  apply Prod.ext
  · rfl
  · abel_nf

theorem recoverB (S : BlockShiftData Δ a b) (δ : Δ) (y t : ZMod b) :
    S.orderB.symm ((S.e δ).1, (y + (S.e δ).2) + t -
      (y + t - S.rhoB δ)) = δ := by
  apply S.orderB.injective
  rw [Equiv.apply_symm_apply, S.orderB_apply]
  apply Prod.ext
  · rfl
  · abel_nf

theorem blockInverse_forward_inl (D : LabeledBlocks K A B a b)
    (S : BlockShiftData Δ a b) (H : K × Δ → ℤ)
    (hA : ∀ z, (H z : ZMod a) = S.rhoA z.2)
    (x : ℤ) (k : K) (c : A) (y : ZMod a) (δ : Δ) :
    blockInverse D S x k
      (blockForward D S H x k (k - D.decode.symm (.inl (c, y)), δ)) =
      (k - D.decode.symm (.inl (c, y)), δ) := by
  rw [blockForward_inl D S H hA, blockInverse_inl]
  simp only [recoverA]
  simp

theorem blockInverse_forward_inr (D : LabeledBlocks K A B a b)
    (S : BlockShiftData Δ a b) (H : K × Δ → ℤ)
    (hB : ∀ z, (H z : ZMod b) = S.rhoB z.2)
    (x : ℤ) (k : K) (c : B) (y : ZMod b) (δ : Δ) :
    blockInverse D S x k
      (blockForward D S H x k (k - D.decode.symm (.inr (c, y)), δ)) =
      (k - D.decode.symm (.inr (c, y)), δ) := by
  rw [blockForward_inr D S H hB, blockInverse_inr]
  simp only [recoverB]
  simp

theorem blockInverse_forward (D : LabeledBlocks K A B a b)
    (S : BlockShiftData Δ a b) (H : K × Δ → ℤ)
    (hA : ∀ z, (H z : ZMod a) = S.rhoA z.2)
    (hB : ∀ z, (H z : ZMod b) = S.rhoB z.2)
    (x : ℤ) (k : K) :
    Function.LeftInverse (blockInverse D S x k) (blockForward D S H x k) := by
  rintro ⟨l, δ⟩
  cases he : D.decode (k - l) with
  | inl v =>
      rcases v with ⟨c, y⟩
      have hu : D.decode.symm (.inl (c, y)) = k - l := by
        simpa only [he] using D.decode.symm_apply_apply (k - l)
      simpa only [hu, sub_sub_cancel] using blockInverse_forward_inl D S H hA x k c y δ
  | inr v =>
      rcases v with ⟨c, y⟩
      have hu : D.decode.symm (.inr (c, y)) = k - l := by
        simpa only [he] using D.decode.symm_apply_apply (k - l)
      simpa only [hu, sub_sub_cancel] using blockInverse_forward_inr D S H hB x k c y δ

theorem blockForward_inverse_inl (D : LabeledBlocks K A B a b)
    (S : BlockShiftData Δ a b) (H : K × Δ → ℤ)
    (hA : ∀ z, (H z : ZMod a) = S.rhoA z.2)
    (x : ℤ) (k : K) (α : ZMod a) (ξ : ZMod b) (c : A) (q : ZMod a) :
    blockForward D S H x k
      (blockInverse D S x k ((α, ξ), D.decode.symm (.inl (c, q)))) =
      ((α, ξ), D.decode.symm (.inl (c, q))) := by
  let δ := S.orderA.symm (ξ, α + (x : ZMod a) - q)
  have horder : ((S.e δ).2, (S.e δ).1 + S.rhoA δ) =
      (ξ, α + (x : ZMod a) - q) :=
    (S.orderA_apply δ).symm.trans (S.orderA.apply_symm_apply _)
  have he : (S.e δ).2 = ξ := congrArg Prod.fst horder
  have hr : (S.e δ).1 + S.rhoA δ = α + (x : ZMod a) - q :=
    congrArg Prod.snd horder
  have hlabel : (α - (S.e δ).1) + (x : ZMod a) - S.rhoA δ = q := by
    calc
      _ = (α + (x : ZMod a)) - ((S.e δ).1 + S.rhoA δ) := by abel
      _ = (α + (x : ZMod a)) - (α + (x : ZMod a) - q) := by rw [hr]
      _ = q := sub_sub_cancel _ _
  rw [blockInverse_inl]
  change blockForward D S H x k
    (k - D.decode.symm (.inl (c, α - (S.e δ).1)), δ) = _
  rw [blockForward_inl D S H hA]
  simp only [sub_add_cancel, he, hlabel]

theorem blockForward_inverse_inr (D : LabeledBlocks K A B a b)
    (S : BlockShiftData Δ a b) (H : K × Δ → ℤ)
    (hB : ∀ z, (H z : ZMod b) = S.rhoB z.2)
    (x : ℤ) (k : K) (α : ZMod a) (ξ : ZMod b) (c : B) (q : ZMod b) :
    blockForward D S H x k
      (blockInverse D S x k ((α, ξ), D.decode.symm (.inr (c, q)))) =
      ((α, ξ), D.decode.symm (.inr (c, q))) := by
  let δ := S.orderB.symm (α, ξ + (x : ZMod b) - q)
  have horder : ((S.e δ).1, (S.e δ).2 + S.rhoB δ) =
      (α, ξ + (x : ZMod b) - q) :=
    (S.orderB_apply δ).symm.trans (S.orderB.apply_symm_apply _)
  have he : (S.e δ).1 = α := congrArg Prod.fst horder
  have hr : (S.e δ).2 + S.rhoB δ = ξ + (x : ZMod b) - q :=
    congrArg Prod.snd horder
  have hlabel : (ξ - (S.e δ).2) + (x : ZMod b) - S.rhoB δ = q := by
    calc
      _ = (ξ + (x : ZMod b)) - ((S.e δ).2 + S.rhoB δ) := by abel
      _ = (ξ + (x : ZMod b)) - (ξ + (x : ZMod b) - q) := by rw [hr]
      _ = q := sub_sub_cancel _ _
  rw [blockInverse_inr]
  change blockForward D S H x k
    (k - D.decode.symm (.inr (c, ξ - (S.e δ).2)), δ) = _
  rw [blockForward_inr D S H hB]
  simp only [sub_add_cancel, he, hlabel]

theorem blockForward_inverse (D : LabeledBlocks K A B a b)
    (S : BlockShiftData Δ a b) (H : K × Δ → ℤ)
    (hA : ∀ z, (H z : ZMod a) = S.rhoA z.2)
    (hB : ∀ z, (H z : ZMod b) = S.rhoB z.2)
    (x : ℤ) (k : K) :
    Function.RightInverse (blockInverse D S x k) (blockForward D S H x k) := by
  rintro ⟨⟨α, ξ⟩, β⟩
  cases he : D.decode β with
  | inl v =>
      rcases v with ⟨c, q⟩
      have hβ : D.decode.symm (.inl (c, q)) = β := by
        simpa only [he] using D.decode.symm_apply_apply β
      simpa only [hβ] using blockForward_inverse_inl D S H hA x k α ξ c q
  | inr v =>
      rcases v with ⟨c, q⟩
      have hβ : D.decode.symm (.inr (c, q)) = β := by
        simpa only [he] using D.decode.symm_apply_apply β
      simpa only [hβ] using blockForward_inverse_inr D S H hB x k α ξ c q

def blockInverseEquiv (D : LabeledBlocks K A B a b) (S : BlockShiftData Δ a b)
    (H : K × Δ → ℤ) (hA : ∀ z, (H z : ZMod a) = S.rhoA z.2)
    (hB : ∀ z, (H z : ZMod b) = S.rhoB z.2) (x : ℤ) (k : K) :
    (K × Δ) ≃ ((ZMod a × ZMod b) × K) where
  toFun := blockForward D S H x k
  invFun := blockInverse D S x k
  left_inv := blockInverse_forward D S H hA hB x k
  right_inv := blockForward_inverse D S H hA hB x k

@[simp] theorem blockInverseEquiv_apply (D : LabeledBlocks K A B a b)
    (S : BlockShiftData Δ a b) (H : K × Δ → ℤ)
    (hA : ∀ z, (H z : ZMod a) = S.rhoA z.2)
    (hB : ∀ z, (H z : ZMod b) = S.rhoB z.2) (x : ℤ) (k : K) (z : K × Δ) :
    blockInverseEquiv D S H hA hB x k z =
      (D.C (k - z.1) + S.e z.2, D.T (x - H z) (k - z.1)) := rfl

@[simp] theorem blockInverseEquiv_symm_apply (D : LabeledBlocks K A B a b)
    (S : BlockShiftData Δ a b) (H : K × Δ → ℤ)
    (hA : ∀ z, (H z : ZMod a) = S.rhoA z.2)
    (hB : ∀ z, (H z : ZMod b) = S.rhoB z.2)
    (x : ℤ) (k : K) (v : (ZMod a × ZMod b) × K) :
    (blockInverseEquiv D S H hA hB x k).symm v = blockInverse D S x k v := rfl

end BlockShiftData

end PeriodicTilingThree

end OAI
