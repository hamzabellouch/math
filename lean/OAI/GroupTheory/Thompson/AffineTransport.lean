import OAI.GroupTheory.Thompson.DyadicGapPartition
import OAI.GroupTheory.Thompson.OrderedPLInterpolation
import Mathlib.Data.List.Forall2

namespace OAI

/-!
# Simultaneous affine transport of two separated basic intervals

Each of the three complementary gaps is partitioned and equalized separately.
Consequently the selected source and target cells occupy matching positions
in the two full ordered partitions. The interpolation theorem constructs an
actual increasing dyadic PL homeomorphism on those partitions.
-/

noncomputable section

universe uα uβ

namespace ThompsonNonamenability

private theorem forall₂_after_prefix {α : Type uα} {β : Type uβ} {R : α → β → Prop}
    {A C : List α} {B D : List β} (hlen : A.length = B.length)
    (h : List.Forall₂ R (A ++ C) (B ++ D)) : List.Forall₂ R C D := by
  have hdrop := List.forall₂_drop A.length h
  rw [List.drop_left, hlen, List.drop_left] at hdrop
  exact hdrop

/-- The selected positions are preserved because the three gap lengths are
equalized independently. All partition data will be constructed below. -/
private theorem exists_pair_transport_of_partitions
    (I J I' J' : BasicInterval)
    (P₀ : DyadicGapPartition 0 I.left) (Q₀ : DyadicGapPartition 0 I'.left)
    (P₁ : DyadicGapPartition I.right J.left)
    (Q₁ : DyadicGapPartition I'.right J'.left)
    (P₂ : DyadicGapPartition J.right 1) (Q₂ : DyadicGapPartition J'.right 1)
    (hlen₀ : P₀.cells.length = Q₀.cells.length)
    (hlen₁ : P₁.cells.length = Q₁.cells.length)
    (hlen₂ : P₂.cells.length = Q₂.cells.length) :
    ∃ h : F, CarriesAffinely h I I' ∧ CarriesAffinely h J J' := by
  let L := P₀.cells ++ I :: (P₁.cells ++ J :: P₂.cells)
  let R := Q₀.cells ++ I' :: (Q₁.cells ++ J' :: Q₂.cells)
  have hL : GapChain 0 1 L := by
    exact P₀.chain.append ⟨rfl, P₁.chain.append ⟨rfl, P₂.chain⟩⟩
  have hR : GapChain 0 1 R := by
    exact Q₀.chain.append ⟨rfl, Q₁.chain.append ⟨rfl, Q₂.chain⟩⟩
  have hlen : L.length = R.length := by
    simp only [L, R, List.length_append, List.length_cons, hlen₀, hlen₁, hlen₂]
  obtain ⟨h, hpair⟩ := exists_chain_transport hL hR hlen
  have hpair₀ : List.Forall₂ (CarriesAffinely h)
      (I :: (P₁.cells ++ J :: P₂.cells))
      (I' :: (Q₁.cells ++ J' :: Q₂.cells)) :=
    forall₂_after_prefix hlen₀ hpair
  have hfirst := List.forall₂_cons.mp hpair₀
  have hpair₁ : List.Forall₂ (CarriesAffinely h)
      (J :: P₂.cells) (J' :: Q₂.cells) :=
    forall₂_after_prefix hlen₁ hfirst.2
  exact ⟨h, hfirst.1, (List.forall₂_cons.mp hpair₁).1⟩

/-- Two strictly separated internal basic intervals can simultaneously be
carried onto any other such pair by an actual element of standard Thompson F. -/
theorem exists_affine_pair_transport {I J I' J' : BasicInterval}
    (hI : I.Internal) (hJ : J.Internal)
    (hI' : I'.Internal) (hJ' : J'.Internal)
    (hIJ : I.Before J) (hIJ' : I'.Before J') :
    ∃ h : F, CarriesAffinely h I I' ∧ CarriesAffinely h J J' := by
  obtain ⟨P₀, Q₀, hlen₀⟩ := exists_equal_length_partitions
    isDyadic_zero I.left_isDyadic isDyadic_zero I'.left_isDyadic
    le_rfl (I.left_lt_right.le.trans I.right_le_one)
    le_rfl (I'.left_lt_right.le.trans I'.right_le_one) hI.1 hI'.1
  obtain ⟨P₁, Q₁, hlen₁⟩ := exists_equal_length_partitions
    I.right_isDyadic J.left_isDyadic I'.right_isDyadic J'.left_isDyadic
    (I.left_nonneg.trans I.left_lt_right.le)
    (J.left_lt_right.le.trans J.right_le_one)
    (I'.left_nonneg.trans I'.left_lt_right.le)
    (J'.left_lt_right.le.trans J'.right_le_one) hIJ hIJ'
  obtain ⟨P₂, Q₂, hlen₂⟩ := exists_equal_length_partitions
    J.right_isDyadic isDyadic_one J'.right_isDyadic isDyadic_one
    (J.left_nonneg.trans J.left_lt_right.le) le_rfl
    (J'.left_nonneg.trans J'.left_lt_right.le) le_rfl hJ.2 hJ'.2
  exact exists_pair_transport_of_partitions I J I' J'
    P₀ Q₀ P₁ Q₁ P₂ Q₂ hlen₀ hlen₁ hlen₂

end ThompsonNonamenability

end

end OAI
