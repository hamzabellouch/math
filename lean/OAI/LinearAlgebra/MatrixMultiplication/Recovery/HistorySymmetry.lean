import OAI.LinearAlgebra.MatrixMultiplication.Tensor.CompleteWordPair
import OAI.LinearAlgebra.MatrixMultiplication.Recovery.InheritedMasks
import OAI.LinearAlgebra.MatrixMultiplication.Recovery.ExactRecovery

namespace OAI

/-! Finite orbit symmetries, masks and exact recovery operations. -/

open scoped BigOperators
open MatrixMultiplication.Foundation
open MatrixMultiplication.PermutationMatching
open MatrixMultiplication.InheritedMasks

namespace MatrixMultiplication.HistorySymmetry

variable {C : Type*} {P X Y : C → Type*}

def completeWordPairEquiv : CompleteWordPair P X Y ≃
    ((∀ c, P c → X c) × (∀ c, P c → Y c)) where
  toFun w := (w.left, w.right)
  invFun w := ⟨w.1, w.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

noncomputable instance completeWordPairFintype
    [Fintype C] [DecidableEq C] [∀ c, Fintype (P c)] [∀ c, DecidableEq (P c)]
    [∀ c, Fintype (X c)] [∀ c, Fintype (Y c)] : Fintype (CompleteWordPair P X Y) :=
  Fintype.ofEquiv _ completeWordPairEquiv.symm

theorem card_completeWordPair
    [Fintype C] [DecidableEq C] [∀ c, Fintype (P c)] [∀ c, DecidableEq (P c)]
    [∀ c, Fintype (X c)] [∀ c, Fintype (Y c)] :
    Fintype.card (CompleteWordPair P X Y) =
      (∏ c, Fintype.card (X c) ^ Fintype.card (P c)) *
      ∏ c, Fintype.card (Y c) ^ Fintype.card (P c) := by
  rw [Fintype.card_congr completeWordPairEquiv]
  simp

section Coefficients

variable {K : Type*} [CommSemiring K] [Fintype C] [∀ c, Fintype (P c)]
    {XL YL ZL XR YR ZR : C → Type*}

def pairClassProduct
    (TL : ∀ c, Tensor K (XL c) (YL c) (ZL c))
    (TR : ∀ c, Tensor K (XR c) (YR c) (ZR c)) :
    Tensor K (CompleteWordPair P XL XR) (CompleteWordPair P YL YR) (CompleteWordPair P ZL ZR) :=
  fun x y z => classProduct TL x.left y.left z.left * classProduct TR x.right y.right z.right

theorem pairClassProduct_smul
    (TL : ∀ c, Tensor K (XL c) (YL c) (ZL c))
    (TR : ∀ c, Tensor K (XR c) (YR c) (ZR c))
    (g : HalfClassPermutations P)
    (x : CompleteWordPair P XL XR) (y : CompleteWordPair P YL YR)
    (z : CompleteWordPair P ZL ZR) :
    pairClassProduct TL TR (g • x) (g • y) (g • z) = pairClassProduct TL TR x y z := by
  change classProduct TL (fun c => x.left c ∘ (g.1 c).symm)
      (fun c => y.left c ∘ (g.1 c).symm) (fun c => z.left c ∘ (g.1 c).symm) *
    classProduct TR (fun c => x.right c ∘ (g.2 c).symm)
      (fun c => y.right c ∘ (g.2 c).symm) (fun c => z.right c ∘ (g.2 c).symm) = _
  rw [classProduct_permutation, classProduct_permutation]
  rfl

end Coefficients

section Windows

variable [Fintype C] [∀ c, Fintype (P c)] [∀ c, DecidableEq (P c)]
    {SL SR : C → Type*} [∀ c, Fintype (SL c)] [∀ c, Fintype (SR c)]
    [∀ c, DecidableEq (SL c)] [∀ c, DecidableEq (SR c)]

def childWindows (sl : ∀ c, X c → SL c) (sr : ∀ c, Y c → SR c)
    (νl : ∀ c, SL c → ℝ) (νr : ∀ c, SR c → ℝ) (ηl ηr : C → ℝ)
    (w : CompleteWordPair P X Y) : Prop :=
  ∀ c, typeWindow (νl c) (ηl c) (sl c ∘ w.left c) ∧
    typeWindow (νr c) (ηr c) (sr c ∘ w.right c)

omit [Fintype C] [∀ index, DecidableEq (P index)]
  [∀ index, Fintype (SL index)] [∀ index, Fintype (SR index)] in
theorem childWindows_smul
    (sl : ∀ c, X c → SL c) (sr : ∀ c, Y c → SR c)
    (νl : ∀ c, SL c → ℝ) (νr : ∀ c, SR c → ℝ) (ηl ηr : C → ℝ)
    (g : HalfClassPermutations P) (w : CompleteWordPair P X Y) :
    childWindows sl sr νl νr ηl ηr (g • w) ↔ childWindows sl sr νl νr ηl ηr w := by
  unfold childWindows
  change (∀ c, typeWindow (νl c) (ηl c) ((sl c ∘ w.left c) ∘ (g.1 c).symm) ∧
    typeWindow (νr c) (ηr c) ((sr c ∘ w.right c) ∘ (g.2 c).symm)) ↔ _
  simp only [typeWindow_permutation]

end Windows

theorem delete_invariant {K G U V W : Type*} [CommSemiring K] [Group G]
    [MulAction G U] [MulAction G V] [MulAction G W]
    (Q : Tensor K U V W) (px : U → Prop) (py : V → Prop) (pz : W → Prop)
    [DecidablePred px] [DecidablePred py] [DecidablePred pz]
    (hQ : ∀ (g : G) x y z, Q (g • x) (g • y) (g • z) = Q x y z)
    (hx : ∀ (g : G) x, px (g • x) ↔ px x)
    (hy : ∀ (g : G) y, py (g • y) ↔ py y)
    (hz : ∀ (g : G) z, pz (g • z) ↔ pz z)
    (g : G) (x : U) (y : V) (z : W) :
    ExactRecovery.delete Q px py pz (g • x) (g • y) (g • z) =
      ExactRecovery.delete Q px py pz x y z := by
  simp only [ExactRecovery.delete, hx, hy, hz, hQ]

theorem delete_used_left {K U V W : Type*} [CommSemiring K]
    (Q : Tensor K U V W) (px : U → Prop) (py : V → Prop) (pz : W → Prop)
    [DecidablePred px] [DecidablePred py] [DecidablePred pz] (x : U)
    (h : ∃ y z, ExactRecovery.delete Q px py pz x y z ≠ 0) : px x := by
  obtain ⟨y, z, h⟩ := h
  by_contra hn
  simp [ExactRecovery.delete, hn] at h

theorem delete_used_middle {K U V W : Type*} [CommSemiring K]
    (Q : Tensor K U V W) (px : U → Prop) (py : V → Prop) (pz : W → Prop)
    [DecidablePred px] [DecidablePred py] [DecidablePred pz] (y : V)
    (h : ∃ x z, ExactRecovery.delete Q px py pz x y z ≠ 0) : py y := by
  obtain ⟨x, z, h⟩ := h
  by_contra hn
  simp [ExactRecovery.delete, hn] at h

theorem delete_used_right {K U V W : Type*} [CommSemiring K]
    (Q : Tensor K U V W) (px : U → Prop) (py : V → Prop) (pz : W → Prop)
    [DecidablePred px] [DecidablePred py] [DecidablePred pz] (z : W)
    (h : ∃ x y, ExactRecovery.delete Q px py pz x y z ≠ 0) : pz z := by
  obtain ⟨x, y, h⟩ := h
  by_contra hn
  simp [ExactRecovery.delete, hn] at h

end MatrixMultiplication.HistorySymmetry

end OAI
