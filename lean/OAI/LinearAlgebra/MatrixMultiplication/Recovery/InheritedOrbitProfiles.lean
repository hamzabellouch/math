import OAI.LinearAlgebra.MatrixMultiplication.Recovery.InheritedMaskAction
import Mathlib.SetTheory.Cardinal.Finite

namespace OAI

/-! Finite orbit symmetries, masks and exact recovery operations. -/

namespace MatrixMultiplication.PermutationMatching

open scoped BigOperators
open Classical

noncomputable section

variable {C : Type*} {P X Y : C → Type*}
  [∀ c, Fintype (P c)] [∀ c, DecidableEq (X c)] [∀ c, DecidableEq (Y c)]

abbrev PairProfile (P X Y : C → Type*) [∀ c, Fintype (P c)] :=
  InheritedMasks.Profile P X × InheritedMasks.Profile P Y

def pairProfile (w : CompleteWordPair P X Y) : PairProfile P X Y :=
  (InheritedMasks.profile P X w.left, InheritedMasks.profile P Y w.right)

theorem pairProfile_smul (g : HalfClassPermutations P)
    (w : CompleteWordPair P X Y) : pairProfile (g • w) = pairProfile w := by
  apply Prod.ext
  · apply (InheritedMasks.profile_eq_iff P X _ _).mpr
    exact ⟨fun c => g.1 c, fun c => by
      funext i
      simp⟩
  · apply (InheritedMasks.profile_eq_iff P Y _ _).mpr
    exact ⟨fun c => g.2 c, fun c => by
      funext i
      simp⟩

omit [∀ c, Fintype (P c)] [∀ c, DecidableEq (X c)] [∀ c, DecidableEq (Y c)] in
private theorem completeWordPair_ext {w v : CompleteWordPair P X Y}
    (hl : w.left = v.left) (hr : w.right = v.right) : w = v := by
  cases w
  cases v
  cases hl
  cases hr
  rfl

theorem pairProfile_eq_iff (w v : CompleteWordPair P X Y) :
    pairProfile w = pairProfile v ↔
      ∃ g : HalfClassPermutations P, g • w = v := by
  constructor
  · intro h
    have hl := (InheritedMasks.profile_eq_iff P X w.left v.left).mp
      (congrArg Prod.fst h)
    have hr := (InheritedMasks.profile_eq_iff P Y w.right v.right).mp
      (congrArg Prod.snd h)
    obtain ⟨el, hel⟩ := hl
    obtain ⟨er, her⟩ := hr
    refine ⟨(fun c => (el c)⁻¹, fun c => (er c)⁻¹), ?_⟩
    apply completeWordPair_ext
    · funext c i
      simpa [Function.comp_def, Equiv.Perm.inv_def] using congrFun (hel c) i
    · funext c i
      simpa [Function.comp_def, Equiv.Perm.inv_def] using congrFun (her c) i
  · rintro ⟨g, rfl⟩
    exact (pairProfile_smul g w).symm

theorem pairProfile_eq_iff_orbitRel (w v : CompleteWordPair P X Y) :
    pairProfile w = pairProfile v ↔
      MulAction.orbitRel (HalfClassPermutations P) (CompleteWordPair P X Y) w v := by
  constructor
  · intro h
    obtain ⟨g, hg⟩ := (pairProfile_eq_iff v w).mp h.symm
    exact ⟨g, hg⟩
  · rintro ⟨g, rfl⟩
    exact pairProfile_smul g v

abbrev PairOrbit (P X Y : C → Type*) :=
  MulAction.orbitRel.Quotient (HalfClassPermutations P) (CompleteWordPair P X Y)

def pairOrbitProfile : PairOrbit P X Y → PairProfile P X Y :=
  Quotient.lift pairProfile fun w v h => (pairProfile_eq_iff_orbitRel w v).mpr h

theorem pairOrbitProfile_injective :
    Function.Injective (pairOrbitProfile (P := P) (X := X) (Y := Y)) := by
  intro q r
  induction q using Quotient.inductionOn with
  | h w =>
    induction r using Quotient.inductionOn with
    | h v =>
      intro h
      apply Quotient.sound
      exact (pairProfile_eq_iff_orbitRel w v).mp h

variable [Fintype C] [∀ c, Fintype (X c)] [∀ c, Fintype (Y c)]

theorem card_pairOrbits_le :
    Nat.card (PairOrbit P X Y) ≤
      (∏ c, (Fintype.card (P c) + 1) ^ Fintype.card (X c)) *
      (∏ c, (Fintype.card (P c) + 1) ^ Fintype.card (Y c)) := by
  have : Finite (PairOrbit P X Y) :=
    Finite.of_injective pairOrbitProfile pairOrbitProfile_injective
  let := Fintype.ofFinite (PairOrbit P X Y)
  rw [Nat.card_eq_fintype_card]
  calc
    _ ≤ Fintype.card (PairProfile P X Y) :=
      Fintype.card_le_of_injective pairOrbitProfile pairOrbitProfile_injective
    _ = _ := by
      rw [Fintype.card_prod, InheritedMasks.card_profile, InheritedMasks.card_profile]

theorem card_pairOrbits_le_common_bound (m : ℕ)
    (hm : ∀ c, Fintype.card (P c) ≤ m) :
    Nat.card (PairOrbit P X Y) ≤ (m + 1) ^
      ((∑ c, Fintype.card (X c)) + ∑ c, Fintype.card (Y c)) := by
  refine (card_pairOrbits_le (P := P) (X := X) (Y := Y)).trans ?_
  calc
    _ ≤ (∏ c, (m + 1) ^ Fintype.card (X c)) *
        (∏ c, (m + 1) ^ Fintype.card (Y c)) := by
      apply Nat.mul_le_mul
      · exact Finset.prod_le_prod fun c _ =>
          Nat.pow_le_pow_left (Nat.add_le_add_right (hm c) 1) _
      · exact Finset.prod_le_prod fun c _ =>
          Nat.pow_le_pow_left (Nat.add_le_add_right (hm c) 1) _
    _ = _ := by rw [Finset.prod_pow_eq_pow_sum, Finset.prod_pow_eq_pow_sum, pow_add]

end

end MatrixMultiplication.PermutationMatching

end OAI
