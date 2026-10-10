import OAI.Analysis.LipschitzHilbert.Packets.SourcePacketOwnDensity
import OAI.Analysis.LipschitzHilbert.Trees.SourceShortTreeSum

namespace OAI

/-! The short-tree lattice sums for the literal labeled source family.
The Whitney separation is derived from the actual packet centers. -/
noncomputable section
open Set
open scoped BigOperators
namespace LipschitzHilbert.SourceLabeledLattice
open SourceWhitney DyadicLineGrid
variable {N : ℕ} {κ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]
variable (P : SourceLabeledLattice N κ Label Item)

abbrev whitneyAllowed (k m : ℤ) : Prop :=
  Allowed (Finset.univ : Finset P.PacketIndex)
    (fun q => P.actualX q.1 q.2.1 q.2.2) (fun q => P.length q.1) k m

def shortKernel (k m : ℤ) (q : P.PacketIndex) : ℝ :=
  (1+(stripDistance (center k m) (DyadicLineGrid.scale k) (P.actualX q.1 q.2.1 q.2.2)/P.length q.1)^2)⁻¹^2

theorem label_short_kernel_sum (y : ℝ) (k m : ℤ) (hallowed : P.whitneyAllowed k m)
    (hcenter : ∀ j l u, |P.actualZ j l u-y|≤P.width) (j : Fin N) (l : P.labels j) :
    (∑ u : Item j l, P.shortKernel k m ⟨j,l,u⟩) ≤ 144*(4*Real.pi)^2 := by
  classical
  let S := Finset.univ.image (P.site j l)
  have hstrip : ∀ p∈S, |P.originZ j l+P.rowSlope j l*P.length j*p.1+P.width*p.2-y|≤P.width := by
    intro p hp
    obtain ⟨u,_,rfl⟩ := Finset.mem_image.mp hp
    exact hcenter j l u
  have hsep : ∀ p∈S, P.length j≤DyadicLineGrid.scale k →
      DyadicLineGrid.scale k≤stripDistance (center k m) (DyadicLineGrid.scale k) (P.originX j l+P.length j*p.1) := by
    intro p hp hlen
    obtain ⟨u,_,rfl⟩ := Finset.mem_image.mp hp
    exact (stripDistance_large _ _ _ hallowed (Finset.mem_univ ⟨j,l,u⟩) hlen).le
  have h := sheared_strip_kernel_sum (P.originX j l) (P.originZ j l) (P.length j)
    P.width (P.rowSlope j l) (center k m) y (DyadicLineGrid.scale k) (P.length_pos j) P.width_pos S hstrip hsep
  rw [Finset.sum_image (fun _ _ _ _ he => P.site_injective j l he)] at h
  exact h

theorem label_short_kernel_decay_sum (y : ℝ) (k m : ℤ) (hallowed : P.whitneyAllowed k m)
    (hcenter : ∀ j l u, |P.actualZ j l u-y|≤P.width)
    (j : Fin N) (l : P.labels j) (hlen : P.length j≤DyadicLineGrid.scale k) :
    (∑ u : Item j l, P.shortKernel k m ⟨j,l,u⟩) ≤
      144*(4*Real.pi)^2*(P.length j/DyadicLineGrid.scale k)^2 := by
  classical
  let S := Finset.univ.image (P.site j l)
  have hstrip : ∀ p∈S, |P.originZ j l+P.rowSlope j l*P.length j*p.1+P.width*p.2-y|≤P.width := by
    intro p hp
    obtain ⟨u,_,rfl⟩ := Finset.mem_image.mp hp
    exact hcenter j l u
  have hsep : ∀ p∈S, DyadicLineGrid.scale k≤stripDistance (center k m) (DyadicLineGrid.scale k) (P.originX j l+P.length j*p.1) := by
    intro p hp
    obtain ⟨u,_,rfl⟩ := Finset.mem_image.mp hp
    exact (stripDistance_large _ _ _ hallowed (Finset.mem_univ ⟨j,l,u⟩) hlen).le
  have h := sheared_strip_kernel_decay_sum (P.originX j l) (P.originZ j l) (P.length j)
    P.width (P.rowSlope j l) (center k m) y (DyadicLineGrid.scale k) (P.length_pos j) P.width_pos (scale_pos k) S hstrip hsep
  rw [Finset.sum_image (fun _ _ _ _ he => P.site_injective j l he)] at h
  exact h

theorem row_short_kernel_sum (B : ℕ) (hcard : ∀ j, (P.labels j).card≤B)
    (y : ℝ) (k m : ℤ) (hallowed : P.whitneyAllowed k m)
    (hcenter : ∀ j l u, |P.actualZ j l u-y|≤P.width) (j : Fin N) :
    (∑ l : P.labels j, ∑ u : Item j l, P.shortKernel k m ⟨j,l,u⟩) ≤
      144*(4*Real.pi)^2*B := by
  calc
    _ ≤ ∑ _l : P.labels j, 144*(4*Real.pi)^2 :=
      Finset.sum_le_sum (fun l _ => P.label_short_kernel_sum y k m hallowed hcenter j l)
    _ = (P.labels j).card*(144*(4*Real.pi)^2) := by simp
    _ ≤ (B:ℝ)*(144*(4*Real.pi)^2) := mul_le_mul_of_nonneg_right
      (by exact_mod_cast hcard j) (by positivity)
    _ = _ := mul_comm _ _

/-- The short-tail majorant summed over every packet with length at most
`R`. Labels cost only their fixed per-scale multiplicity. -/
theorem packet_short_mass_sum (B : ℕ) (hcard : ∀ j, (P.labels j).card≤B)
    (y R : ℝ) (hR : 0≤R) (k m : ℤ) (hallowed : P.whitneyAllowed k m)
    (hcenter : ∀ j l u, |P.actualZ j l u-y|≤P.width) :
    (∑ q : P.PacketIndex, if P.length q.1≤R then
      P.length q.1*P.width*P.shortKernel k m q else 0) ≤
      288*(4*Real.pi)^2*B*P.width*R := by
  classical
  have hwidth := P.width_pos
  have hrow (j : Fin N) :
      (∑ l : P.labels j, ∑ u : Item j l, if P.length j≤R then
        P.length j*P.width*P.shortKernel k m ⟨j,l,u⟩ else 0) ≤
      (144*(4*Real.pi)^2*B*P.width)*(if P.length j≤R then P.length j else 0) := by
    by_cases hlen : P.length j≤R
    · simp only [ite_eq_left hlen]
      simp_rw [←Finset.mul_sum]
      have h := mul_le_mul_of_nonneg_left (P.row_short_kernel_sum B hcard y k m hallowed hcenter j)
        (mul_nonneg (P.length_pos j).le P.width_pos.le)
      convert h using 1
      ring
    · simp only [ite_eq_right hlen,Finset.sum_const_zero,mul_zero,le_refl]
  calc
    _ = ∑ j : Fin N, ∑ l : P.labels j, ∑ u : Item j l, if P.length j≤R then
      P.length j*P.width*P.shortKernel k m ⟨j,l,u⟩ else 0 := by simp only [Fintype.sum_sigma]
    _ ≤ ∑ j : Fin N, (144*(4*Real.pi)^2*B*P.width)*(if P.length j≤R then P.length j else 0) :=
      Finset.sum_le_sum (fun j _ => hrow j)
    _ = (144*(4*Real.pi)^2*B*P.width)*∑ j : Fin N, if P.length j≤R then P.length j else 0 :=
      (Finset.mul_sum _ _ _).symm
    _ ≤ (144*(4*Real.pi)^2*B*P.width)*(2*R) := mul_le_mul_of_nonneg_left
      (fin_short_dyadic_length_sum N P.topLength R hR) (by positivity)
    _ = _ := by ring

/-- The far-strip majorant over the entire packet family retains decay
in the ratio of top length to Whitney length. -/
theorem packet_short_mass_decay_sum (B : ℕ) (hcard : ∀ j, (P.labels j).card≤B)
    (y : ℝ) (k m : ℤ) (hallowed : P.whitneyAllowed k m)
    (hcenter : ∀ j l u, |P.actualZ j l u-y|≤P.width) (hlarge : P.topLength≤DyadicLineGrid.scale k) :
    (∑ q : P.PacketIndex, P.length q.1*P.width*P.shortKernel k m q) ≤
      288*(4*Real.pi)^2*B*P.width*P.topLength*(P.topLength/DyadicLineGrid.scale k)^2 := by
  classical
  have hwidth := P.width_pos
  have hlen (j : Fin N) : P.length j≤DyadicLineGrid.scale k :=
    (div_le_self P.topLength_pos.le (one_le_pow₀ (by norm_num : (1:ℝ)≤2))).trans hlarge
  have hrow (j : Fin N) :
      (∑ l : P.labels j, ∑ u : Item j l, P.shortKernel k m ⟨j,l,u⟩) ≤
        144*(4*Real.pi)^2*B*(P.length j/DyadicLineGrid.scale k)^2 := by
    calc
      _ ≤ ∑ _l : P.labels j, 144*(4*Real.pi)^2*(P.length j/DyadicLineGrid.scale k)^2 :=
        Finset.sum_le_sum (fun l _ => P.label_short_kernel_decay_sum y k m hallowed hcenter j l (hlen j))
      _ = (P.labels j).card*(144*(4*Real.pi)^2*(P.length j/DyadicLineGrid.scale k)^2) := by simp
      _ ≤ (B:ℝ)*(144*(4*Real.pi)^2*(P.length j/DyadicLineGrid.scale k)^2) :=
        mul_le_mul_of_nonneg_right (by exact_mod_cast hcard j) (by positivity)
      _ = _ := by ring
  calc
    _ = ∑ j : Fin N, P.length j*P.width*(∑ l : P.labels j, ∑ u : Item j l, P.shortKernel k m ⟨j,l,u⟩) := by
      simp only [Fintype.sum_sigma,Finset.mul_sum]
    _ ≤ ∑ j : Fin N, (144*(4*Real.pi)^2*B*P.width)*(P.length j*(P.length j/DyadicLineGrid.scale k)^2) := by
      apply Finset.sum_le_sum
      intro j _
      have h := mul_le_mul_of_nonneg_left (hrow j) (mul_nonneg (P.length_pos j).le P.width_pos.le)
      convert h using 1
      ring
    _ = (144*(4*Real.pi)^2*B*P.width)*∑ j : Fin N, P.length j*(P.length j/DyadicLineGrid.scale k)^2 :=
      (Finset.mul_sum _ _ _).symm
    _ ≤ (144*(4*Real.pi)^2*B*P.width)*(2*P.topLength*(P.topLength/DyadicLineGrid.scale k)^2) :=
      mul_le_mul_of_nonneg_left (fin_dyadic_decay_sum N P.topLength (DyadicLineGrid.scale k) P.topLength_pos (scale_pos k))
        (by positivity)
    _ = _ := by ring

end LipschitzHilbert.SourceLabeledLattice

end

end OAI
