import OAI.Combinatorics.ContingencyTables.Transport.ContextAdjacentTransport
import OAI.Combinatorics.ContingencyTables.Transport.FiniteExposureVariance

namespace OAI

/-! # Between-child variance for actual physical exposure contexts -/

namespace ContingencyTables.ExcessContextProfiles

open scoped BigOperators Classical
open SmallContextCoordinates SmallContextEnumeration SmallContextFibres
open PhysicalCompletionFibres LargePairEnumeration BalancedFamily BalancedBox
open IntegerWeightedTransport FirstPaperProfiles FirstPaperContextTransport
open FirstPaperPhysicalMarginal PaddedCompletions CompletionCounts

universe u

lemma graphEnergy_mono {C : Type*} [DecidableEq C]
    (V W : Finset (C → ℕ)) (f H : (C → ℕ) → ℝ)
    (hVW : V ⊆ W) (hf : ∀ x, 0 ≤ f x) :
    integerGraphEnergy V f H ≤ integerGraphEnergy W f H := by
  unfold integerGraphEnergy
  apply div_le_div_of_nonneg_right _ (by norm_num)
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro e he
    obtain ⟨he,hadj⟩ := Finset.mem_filter.mp he
    obtain ⟨hx,hy⟩ := Finset.mem_product.mp he
    exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hVW hx,hVW hy⟩,hadj⟩
  · intro e _ _
    exact mul_nonneg (le_min (hf _) (hf _)) (sq_nonneg _)

noncomputable def contextVertices (U n : ℕ) :
    Finset (Coordinates Bool (widths (fun _ : Fin n => U)) → ℕ) :=
  Finset.univ.biUnion (fun l : Fin (U+1) => leafVertices _ (rootDisplay U l.val))

lemma leafVertices_subset_context (U n l : ℕ) (hl : l ≤ U) :
    leafVertices (widths (fun _ : Fin n => U)) (rootDisplay U l) ⊆ contextVertices U n := by
  intro x hx
  exact Finset.mem_biUnion.mpr ⟨⟨l,Nat.lt_succ_of_le hl⟩,Finset.mem_univ _,hx⟩

variable {I J : Type u} [Fintype I] [Fintype J] [LinearOrder I] [LinearOrder J]

/-- The physical conditional masses and means satisfy the paper's
between-child estimate, allowing arbitrary zero-mass children. -/
theorem physical_child_variance (small : I → J → Bool) (B : I → J → ℕ)
    (r : I → ℕ) (c : J → ℕ) (L : ℕ) (s : I×J) (hs : small s.1 s.2=true)
    (σ : I×J → ℕ) (U : ℕ) (hU : 2 ≤ U)
    (hB : ∀ i j, small i j=true → B i j=U)
    (hlarge : ∀ i j, small i j=false → 2 ≤ B i j)
    (hσ : ∀ a : Earlier small s, σ a.val.val ≤ U) {n : ℕ} (e : Fin n ≃ Later small s)
    (hcap : ∀ T : ResidualTables small r c
      (fun i => r i+rowLargeCount small i*L) (fun j => c j+columnLargeCount small j*L),
      ∀ i j, T.val.val i j ≤ B i j)
    (H : (Coordinates Bool (widths (fun _ : Fin n => U)) → ℕ) → ℝ)
    (hZ : 0 < ∑ j : Fin (U+1), eliminate (widths (fun _ : Fin n => U))
      (contextHard small B r c L _ (contextEquiv small s hs e U) (prefixRaw small s σ U))
      (childProfile U j.val)) :
    let Ms := widths (fun _ : Fin n => U)
    let f := contextHard small B r c L Ms (contextEquiv small s hs e U) (prefixRaw small s σ U)
    let z := fun j => eliminate Ms f (childProfile U j)
    let μ := fun j => eliminate Ms (fun p => f p*H p) (childProfile U j)/z j
    let E := integerGraphEnergy ((contextVertices U n).filter
      (fun x => InBox (bounds (fun _ : Bool => U) Ms) x ∧ (∑ i, x i)=U+Ms.sum)) f H
    (∑ j : Fin (U+1), z j.val*(μ j.val-
      (∑ k : Fin (U+1),z k.val*μ k.val)/(∑ k : Fin (U+1),z k.val))^2) ≤
      ((U:ℝ)+1)^4*(2+2*n*((U:ℝ)+1)^2)*E := by
  dsimp only
  let Ms := widths (fun _ : Fin n => U)
  let f := contextHard small B r c L Ms (contextEquiv small s hs e U) (prefixRaw small s σ U)
  let z := fun j => eliminate Ms f (childProfile U j)
  let μ := fun j => eliminate Ms (fun p => f p*H p) (childProfile U j)/z j
  let V := (contextVertices U n).filter
    (fun x => InBox (bounds (fun _ : Bool => U) Ms) x ∧ (∑ i, x i)=U+Ms.sum)
  have hf : ∀ x, 0 ≤ f x := contextHard_nonnegative small B r c L Ms _ _
  have hz (j : ℕ) : 0 ≤ z j := eliminate_nonnegative Ms f hf _
  have hE : 0 ≤ integerGraphEnergy V f H := graphEnergy_nonnegative V f H hf
  apply child_variance_bound z μ U (2+2*n*((U:ℝ)+1)^2) (integerGraphEnergy V f H)
    (fun j _ => hz j) hZ (by positivity) hE
  · intro a j b haj hjb hbU
    exact context_child_minimum small B r c L Ms (contextEquiv small s hs e U)
      (prefixRaw small s σ U) (fun _ => U) U (prefixRaw_inBox small s σ U hσ) hlarge
      (fun w hw => by rw [widths_constant_mem U w hw]; exact hU) a j b haj hjb hbU
  · intro j hj
    by_cases hl : 0 < z j
    · by_cases hr : 0 < z (j+1)
      · have htransport := adjacent_context_transport small B r c L s hs σ U (j+1) hU
          (by omega) (by omega) hB hlarge hσ e hcap H (by simpa only [Nat.add_sub_cancel] using hl) hr
        dsimp only at htransport
        simp only [Nat.add_sub_cancel] at htransport
        have hsub : (leafVertices Ms (rootDisplay U (j+1))).filter
            (fun x => InBox (bounds (fun _ : Bool => U) Ms) x ∧ (∑ i, x i)=U+Ms.sum) ⊆ V := by
          intro x hx
          obtain ⟨hx,hbox⟩ := Finset.mem_filter.mp hx
          exact Finset.mem_filter.mpr ⟨leafVertices_subset_context U n (j+1) (by omega) hx,hbox⟩
        exact htransport.trans (mul_le_mul_of_nonneg_left (graphEnergy_mono _ V f H hsub hf) (by positivity))
      · have hr0 : z (j+1)=0 := le_antisymm (le_of_not_gt hr) (hz (j+1))
        rw [hr0,min_eq_right (hz j),zero_mul]
        positivity
    · have hl0 : z j=0 := le_antisymm (le_of_not_gt hl) (hz j)
      rw [hl0,min_eq_left (hz (j+1)),zero_mul]
      positivity

end ContingencyTables.ExcessContextProfiles

end OAI
