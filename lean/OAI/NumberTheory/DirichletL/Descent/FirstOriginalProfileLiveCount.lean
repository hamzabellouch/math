import OAI.NumberTheory.DirichletL.Descent.FirstOriginalProfileLivePartition

namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.InverseMomentFirstOriginalProfile
open InverseMoment ActualEisensteinCubic FirstPassCubeLabels InverseMomentFirstChildWindows InverseSecondSourceBlocks
local notation "O" => ActualEisensteinCubic.O
variable {ι : Type*} [DecidableEq ι]
variable (p : ι→O) [∀i,(Ideal.span {p i}).IsMaximal]

omit [∀ (i : ι), (Ideal.span {p i}).IsMaximal] in
theorem liveJointKeys_card (S : Finset (OriginalIndex ι)) (pool : Finset ι)
    (term : OriginalIndex ι→FirstCommonIndex ι→ℂ) (B : ℕ)
    (hcap : ∀x∈S,∀j∈firstCommonIndices pool,term x j≠0→
      (∀i,sourceIndex (originalNorms p) x i≤B) ∧
      dyadIndex (primeProductNorm p j.2.1)≤B ∧
      dyadIndex (InverseFirstGlobalCaps.jNorm p x.1)≤B) :
    (liveJointKeys p S pool term).card≤(B+1)^8 := by
  let box := (Fintype.piFinset (fun _ : Fin 6=>Finset.range (B+1))) ×ˢ
    (Finset.range (B+1) ×ˢ Finset.range (B+1))
  have hsub : liveJointKeys p S pool term⊆box := by
    intro k hk
    obtain ⟨⟨x,j⟩,hm,rfl⟩ := Finset.mem_image.mp hk
    obtain ⟨hm,hn⟩ := Finset.mem_filter.mp hm
    obtain ⟨hx,hj⟩ := Finset.mem_product.mp hm
    obtain ⟨h₁,h₂,h₃⟩ := hcap x hx j hj hn
    exact Finset.mem_product.mpr ⟨Fintype.mem_piFinset.mpr
      (fun i=>Finset.mem_range.mpr (Nat.lt_succ_of_le (h₁ i))),
      Finset.mem_product.mpr ⟨Finset.mem_range.mpr (Nat.lt_succ_of_le h₂),
        Finset.mem_range.mpr (Nat.lt_succ_of_le h₃)⟩⟩
  have hc : box.card=(B+1)^8 := by
    simp only [box,Finset.card_product,Fintype.card_piFinset,Finset.card_range,Finset.prod_const,Finset.card_univ,Fintype.card_fin]
    ring
  exact hc ▸ Finset.card_le_card hsub

omit [∀ (i : ι), (Ideal.span {p i}).IsMaximal] in
theorem liveJointKeys_card_of_norm_cap (S : Finset (OriginalIndex ι)) (pool : Finset ι)
    (term : OriginalIndex ι→FirstCommonIndex ι→ℂ) (R : ℝ)
    (hcap : ∀x∈S,∀j∈firstCommonIndices pool,term x j≠0→
      (∀i,0<originalNorms p x i ∧ originalNorms p x i≤R) ∧
      (0<primeProductNorm p j.2.1 ∧ primeProductNorm p j.2.1≤R) ∧
      (0<InverseFirstGlobalCaps.jNorm p x.1 ∧ InverseFirstGlobalCaps.jNorm p x.1≤R)) :
    (liveJointKeys p S pool term).card≤(dyadIndex R+1)^8 := by
  apply liveJointKeys_card
  intro x hx j hj hn
  obtain ⟨h₁,h₂,h₃⟩ := hcap x hx j hj hn
  have hm : ∀a : ℝ,0<a→a≤R→dyadIndex a≤dyadIndex R := fun a ha haR=>
    Nat.floor_mono (Real.logb_le_logb_of_le (by norm_num : (1:ℝ)<2) ha haR)
  exact ⟨fun i=>hm _ (h₁ i).1 (h₁ i).2,hm _ h₂.1 h₂.2,hm _ h₃.1 h₃.2⟩

end SevenEighths.InverseMomentFirstOriginalProfile
end

end OAI
