import OAI.Analysis.LipschitzHilbert.Geometry.SourceDirectionLabelCount

namespace OAI

/-! Reindex the actual packets at one scale into their original labels
and spatial sites, then apply the uniform lattice count. -/
noncomputable section
open Set
open scoped BigOperators
namespace LipschitzHilbert.SourceLabeledLattice
attribute [local instance] Classical.propDecidable Classical.decEq
variable {N : ℕ} {κ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]
variable (P : SourceLabeledLattice N κ Label Item)

private theorem filter_card_sum {α : Type*} [Fintype α] (S : Finset α) (p : α → Prop) [DecidablePred p] :
    ((S.filter p).card:ℝ)=∑ i : α, if i∈S ∧ p i then (1:ℝ) else 0 := by
  rw [←Finset.sum_filter]
  have he : Finset.univ.filter (fun i => i∈S ∧ p i)=S.filter p := by ext; simp
  rw [he]
  simp

theorem scale_card_eq_labels (S : Finset P.PacketIndex) (j : Fin N)
    (keep : P.PacketIndex → Prop) :
    ((S.filter fun q => q.1=j ∧ keep q).card:ℝ)=
      ∑ l : P.labels j, ((Finset.univ.filter fun u : Item j l =>
        (⟨j,⟨l,u⟩⟩:P.PacketIndex)∈S ∧ keep ⟨j,⟨l,u⟩⟩).card:ℝ) := by
  refine (filter_card_sum S (fun q : P.PacketIndex => q.1=j ∧ keep q)).trans ?_
  simp only [Fintype.sum_sigma]
  rw [Finset.sum_eq_single j]
  · apply Finset.sum_congr rfl
    intro l _
    symm
    convert filter_card_sum Finset.univ (fun u : Item j l =>
      (⟨j,⟨l,u⟩⟩:P.PacketIndex)∈S ∧ keep ⟨j,⟨l,u⟩⟩) using 1; simp
  · intro i _ hij
    apply Finset.sum_eq_zero
    intro l _
    apply Finset.sum_eq_zero
    intro u _
    simp [hij]
  · simp

theorem direction_packets_count (S : Finset P.PacketIndex)
    (t w K R : ℝ) (hw : 0<w) (hwW : w≤P.width) (hK : 0≤K) (hR : 0≤R)
    (M Q : ℕ) (hQ : R≤Q)
    (hmultiplicity : ∀ j, SourceSlopeLabels.LocalMultiplicity Finset.univ
      (P.rowSlope j) (w/P.length j) M)
    (hnear : ∀ q∈S, |P.rowSlope q.1 q.2.1-t|≤R*(w/P.length q.1))
    (z : ℝ×ℝ) (k : ℕ) :
    ((S.filter fun q => q.1.val=k ∧ z∈densitySpatialBox (P.directionBox t q) K).card:ℝ)≤
      (((2*Q+1)*M:ℕ):ℝ)*(((1+K^2)*(1+(K*(1+R))^2))*(4*Real.pi)^2) := by
  by_cases hk : k<N
  · let j : Fin N := ⟨k,hk⟩
    have heq : (S.filter fun q => q.1.val=k ∧ z∈densitySpatialBox (P.directionBox t q) K)=
        S.filter fun q => q.1=j ∧ z∈densitySpatialBox (P.directionBox t q) K := by
      ext q
      simp only [Finset.mem_filter]
      have hj : q.1.val=k ↔ q.1=j := ⟨fun he => Fin.ext he,fun he => congrArg Fin.val he⟩
      rw [hj]
    rw [heq,P.scale_card_eq_labels]
    apply P.direction_label_count j _ t w K R hw hwW hK hR M Q hQ (hmultiplicity j)
    · intro l hl
      obtain ⟨u,hu⟩ := hl
      exact hnear ⟨j,⟨l,u⟩⟩ (Finset.mem_filter.mp hu).2.1
    · intro l u hu
      exact (Finset.mem_filter.mp hu).2.2
  · have heq : (S.filter fun q => q.1.val=k ∧ z∈densitySpatialBox (P.directionBox t q) K)=∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro q hq
      have hqk := (Finset.mem_filter.mp hq).2.1
      exact hk (hqk ▸ q.1.isLt)
    rw [heq,Finset.card_empty,Nat.cast_zero]
    positivity

end LipschitzHilbert.SourceLabeledLattice

end

end OAI
