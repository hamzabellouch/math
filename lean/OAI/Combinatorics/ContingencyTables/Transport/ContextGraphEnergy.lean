import OAI.Combinatorics.ContingencyTables.Sampling.PhysicalGraphVertices

namespace OAI

/-! # Contextual transport energy embeds in the actual physical graph -/

namespace ContingencyTables.SmallGraphProfiles

open scoped BigOperators Classical
open SmallContextCoordinates SmallContextEnumeration SmallContextFibres
open PhysicalCompletionFibres LargePairEnumeration BalancedFamily BalancedBox
open IntegerWeightedTransport FirstPaperProfiles ExcessContextProfiles
open FirstPaperContextTransport FirstPaperPhysicalMarginal

universe u

variable {I J : Type u} [Fintype I] [Fintype J] [LinearOrder I] [LinearOrder J]

def PhysicalPrefix (small : I → J → Bool) (s : I×J) (σ : I×J → ℕ)
    (z : SmallProfile small) : Prop :=
  ∀ a : Earlier small s, z (a.val,false)=σ a.val.val

omit [Fintype I] [Fintype J] in
lemma assemble_physicalPrefix (small : I → J → Bool) (s : I×J) (hs : small s.1 s.2=true)
    (σ : I×J → ℕ) (U : ℕ) {n : ℕ} (e : Fin n ≃ Later small s)
    (x : Coordinates Bool (widths (fun _ : Fin n => U)) → ℕ) :
    PhysicalPrefix small s σ (assemble small s hs σ U e x) := by
  intro a
  exact assemble_prefix small s hs σ U e x a false

noncomputable def physicalContextEdges (small : I → J → Bool) (B : I → J → ℕ)
    (s : I×J) (σ : I×J → ℕ) : Finset (SmallProfile small×SmallProfile small) :=
  ((vertices small B) ×ˢ (vertices small B)).filter
    (fun p => IntegerExchangeAdjacent p.1 p.2 ∧ PhysicalPrefix small s σ p.1 ∧ PhysicalPrefix small s σ p.2)

noncomputable def physicalContextEnergy (small : I → J → Bool) (B : I → J → ℕ)
    (s : I×J) (σ : I×J → ℕ) (f H : SmallProfile small → ℝ) : ℝ :=
  (∑ p ∈ physicalContextEdges small B s σ, edgeTerm f H p)/2

omit [LinearOrder I] [LinearOrder J] in
lemma hardMarginal_nonnegative (small : I → J → Bool) (B : I → J → ℕ)
    (r : I → ℕ) (c : J → ℕ) (L : ℕ) (z : SmallProfile small) :
    0 ≤ hardMarginal small B r c L z := by
  unfold hardMarginal fullHardFamily NestedPenaltyApplication.hardWeight
  apply Finset.sum_nonneg
  intro a _
  split_ifs <;> norm_num

/-- The actual conditional variance energy uses physical allowed states
and ordinary exchange edges in its fixed row-major prefix only. -/
theorem context_graphEnergy_le (small : I → J → Bool) (B : I → J → ℕ)
    (r : I → ℕ) (c : J → ℕ) (L : ℕ)
    (s : I×J) (hs : small s.1 s.2=true) (σ : I×J → ℕ) (U : ℕ)
    (hU : 1 ≤ U) (hB : ∀ i j, small i j=true → B i j=U)
    (hσ : ∀ a : Earlier small s, σ a.val.val ≤ U) {n : ℕ} (e : Fin n ≃ Later small s)
    (H : SmallProfile small → ℝ) :
    let Ms := widths (fun _ : Fin n => U)
    let f := contextHard small B r c L Ms (contextEquiv small s hs e U) (prefixRaw small s σ U)
    integerGraphEnergy ((contextVertices U n).filter
      (fun x => InBox (bounds (fun _ : Bool => U) Ms) x ∧ (∑ i, x i)=U+Ms.sum))
      f (fun x => H (assemble small s hs σ U e x)) ≤
      physicalContextEnergy small B s σ (hardMarginal small B r c L) H := by
  dsimp only
  let V := (contextVertices U n).filter
    (fun x => InBox (bounds (fun _ : Bool => U) (widths (fun _ : Fin n => U))) x ∧
      (∑ i, x i)=U+(widths (fun _ : Fin n => U)).sum)
  let E := (V ×ˢ V).filter (fun p => IntegerExchangeAdjacent p.1 p.2)
  let j : ((Coordinates Bool (widths (fun _ : Fin n => U)) → ℕ)×
      (Coordinates Bool (widths (fun _ : Fin n => U)) → ℕ)) →
      (SmallProfile small×SmallProfile small) :=
    fun p => (assemble small s hs σ U e p.1,assemble small s hs σ U e p.2)
  have hj : Function.Injective j := by
    intro a b he
    apply Prod.ext
    · exact assemble_injective small s hs σ U e (congrArg Prod.fst he)
    · exact assemble_injective small s hs σ U e (congrArg Prod.snd he)
  have hmem (x) (hx : x ∈ V) : assemble small s hs σ U e x ∈ vertices small B := by
    obtain ⟨hx,hbox,_⟩ := Finset.mem_filter.mp hx
    exact context_vertex_mem small B s hs σ U hU hB hσ e x hx hbox
  have hsub : E.image j ⊆ physicalContextEdges small B s σ := by
    intro p hp
    obtain ⟨q,hq,rfl⟩ := Finset.mem_image.mp hp
    obtain ⟨hq,hadj⟩ := Finset.mem_filter.mp hq
    obtain ⟨hx,hy⟩ := Finset.mem_product.mp hq
    apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_product.mpr ⟨hmem _ hx,hmem _ hy⟩,
      assemble_exchange_adjacent small s hs σ U e _ _ hadj,
      assemble_physicalPrefix small s hs σ U e _,assemble_physicalPrefix small s hs σ U e _⟩
  unfold integerGraphEnergy physicalContextEnergy
  apply div_le_div_of_nonneg_right _ (by norm_num)
  change (∑ p ∈ E, edgeTerm (hardMarginal small B r c L) H (j p)) ≤ _
  calc
    _ = ∑ p ∈ E.image j, edgeTerm (hardMarginal small B r c L) H p :=
      (Finset.sum_image (fun a _ b _ he => hj he)).symm
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg hsub (fun p _ _ =>
      mul_nonneg (le_min (hardMarginal_nonnegative small B r c L _)
        (hardMarginal_nonnegative small B r c L _)) (sq_nonneg _))

end ContingencyTables.SmallGraphProfiles

end OAI
