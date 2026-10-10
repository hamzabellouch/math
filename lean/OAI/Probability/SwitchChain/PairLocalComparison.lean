import OAI.Probability.SwitchChain.PairAssignmentMoves
import OAI.Probability.SwitchChain.PairFiberEnergy
import OAI.Probability.SwitchChain.PairSquaredEnergy

namespace OAI

noncomputable section
open scoped BigOperators RealInnerProductSpace
attribute [local instance] Classical.propDecidable

namespace Problem315.PairFiber

variable {n : ℕ} {d : Fin n → ℕ}

theorem assignment_swap_squared_differences_le_proposals
    (G : GraphState n d) (i j : Fin n) (hij : i ≠ j)
    (T : Assignment G.val i j) (f : GraphState n d → ℝ) :
    (∑ σ ∈ SlicePathComparison.swaps,
      (f ((stateFiberEquiv G i j hij).symm T).val -
        f ((stateFiberEquiv G i j hij).symm
          (assignmentRelabel G.val i j σ T)).val) ^ 2) ≤
    ∑ p ∈ allProposals n,
      if ({i, j} : Finset (Fin n)) ∈ SwitchPairFiber.crossingPairs p then
        (f ((stateFiberEquiv G i j hij).symm T).val -
          f (proposalState ((stateFiberEquiv G i j hij).symm T).val p)) ^ 2
      else 0 := by
  classical
  let R : Assignment G.val i j → GraphState n d :=
    fun U => ((stateFiberEquiv G i j hij).symm U).val
  have hR : Function.Injective R := by
    intro U W h
    apply (stateFiberEquiv G i j hij).symm.injective
    exact Subtype.ext h
  let s : Finset (Equiv.Perm (singletonSet G.val i j)) :=
    SlicePathComparison.swaps.filter (fun σ => assignmentRelabel G.val i j σ T ≠ T)
  have hs (σ : s) : σ.val.IsSwap ∧ assignmentRelabel G.val i j σ.val T ≠ T := by
    exact ⟨SlicePathComparison.mem_swaps σ.val |>.mp (Finset.mem_filter.mp σ.property).1,
      (Finset.mem_filter.mp σ.property).2⟩
  have hex (σ : s) : ∃ p : SwitchProposal n, validSwitch (R T).val p ∧
      ({i, j} : Finset (Fin n)) ∈ SwitchPairFiber.crossingPairs p ∧
      proposalResult (R T).val p = (R (assignmentRelabel G.val i j σ.val T)).val :=
    assignmentRelabel_exists_crossingProposal G i j hij T σ.val (hs σ).1 (hs σ).2
  let p : s → SwitchProposal n := fun σ => Classical.choose (hex σ)
  have hp (σ : s) := Classical.choose_spec (hex σ)
  have hstate (σ : s) : proposalState (R T) (p σ) =
      R (assignmentRelabel G.val i j σ.val T) := by
    apply Subtype.ext
    exact (hp σ).2.2
  have hinj : Function.Injective p := by
    intro σ τ heq
    apply Subtype.ext
    apply assignmentRelabel_injective_on_nontrivial G.val i j T
      (hs σ).1 (hs τ).1 (hs σ).2 (hs τ).2
    apply hR
    rw [← hstate σ, ← hstate τ, heq]
  let D : Equiv.Perm (singletonSet G.val i j) → ℝ :=
    fun σ => (f (R T) - f (R (assignmentRelabel G.val i j σ T))) ^ 2
  let E : SwitchProposal n → ℝ := fun q =>
    if ({i, j} : Finset (Fin n)) ∈ SwitchPairFiber.crossingPairs q then
      (f (R T) - f (proposalState (R T) q)) ^ 2 else 0
  have hweight (σ : s) : E (p σ) = D σ.val := by
    dsimp only [E, D]
    rw [ite_eq_left (hp σ).2.1, hstate σ]
  have hrestrict : (∑ σ ∈ SlicePathComparison.swaps, D σ) = ∑ σ : s, D σ.val := by
    rw [Finset.sum_coe_sort]
    symm
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro σ hσ hnot
    have hfix : assignmentRelabel G.val i j σ T = T := by
      by_contra hne
      exact hnot (Finset.mem_filter.mpr ⟨hσ, hne⟩)
    simp [D, hfix]
  change (∑ σ ∈ SlicePathComparison.swaps, D σ) ≤ ∑ q ∈ allProposals n, E q
  rw [hrestrict]
  calc
    (∑ σ : s, D σ.val) = ∑ σ : s, E (p σ) := by
      apply Finset.sum_congr rfl
      intro σ _
      exact (hweight σ).symm
    _ = ∑ q ∈ Finset.univ.image p, E q :=
      (Finset.sum_image (fun _ _ _ _ h => hinj h)).symm
    _ ≤ ∑ q ∈ allProposals n, E q := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro q hq
        exact Finset.mem_univ q
      · intro q _ _
        dsimp only [E]
        split_ifs <;> positivity

theorem inner_fluctuation_le_pairSwitchLaplacian
    (i j : Fin n) (hij : i ≠ j) (f : PairResampling.StateSpace n d) :
    inner ℝ f (PairResampling.fluctuation n d {i, j} f) ≤
      (n : ℝ) ^ 2 * ∑ G : GraphState n d,
        f G * pairSwitchLaplacian n d {i, j} (fun H => f H) G := by
  classical
  let E : GraphState n d → ℝ := fun H =>
    ∑ p ∈ allProposals n,
      if ({i, j} : Finset (Fin n)) ∈ SwitchPairFiber.crossingPairs p then
        (f H - f (proposalState H p)) ^ 2 else 0
  have hE (H : GraphState n d) : 0 ≤ E H := by
    apply Finset.sum_nonneg
    intro p _
    split_ifs <;> positivity
  have hlocal (G : GraphState n d) :
      (∑ T : Assignment G.val i j,
        (f ((stateFiberEquiv G i j hij).symm T).val -
          PairResampling.expectation n d {i, j} f G) ^ 2) ≤
        (n : ℝ) ^ 2 / 2 *
          ∑ T : Assignment G.val i j, E ((stateFiberEquiv G i j hij).symm T).val := by
    let R : Assignment G.val i j → GraphState n d :=
      fun T => ((stateFiberEquiv G i j hij).symm T).val
    have hcard : Fintype.card (Assignment G.val i j) =
        Nat.choose (singletonSet G.val i j).card (leftSet G.val i j).card := by
      rw [← Nat.card_eq_fintype_card]
      exact assignment_natCard G.val i j
    have hmean := expectation_eq_assignment_average G i j hij f
    rw [← hcard] at hmean
    have hvar := assignment_variance_le_swap_squared_differences G.val i j
      (fun T => f (R T))
    change (∑ T : Assignment G.val i j,
      (f (R T) - (∑ U, f (R U)) / (Fintype.card (Assignment G.val i j) : ℝ)) ^ 2) ≤ _ at hvar
    rw [← hmean] at hvar
    have hsum : (∑ T : Assignment G.val i j, ∑ σ ∈ SlicePathComparison.swaps,
        (f (R T) - f (R (assignmentRelabel G.val i j σ T))) ^ 2) ≤
          ∑ T : Assignment G.val i j, E (R T) := by
      apply Finset.sum_le_sum
      intro T _
      exact assignment_swap_squared_differences_le_proposals G i j hij T (fun H => f H)
    have hN : ((singletonSet G.val i j).card : ℝ) ≤ (n : ℝ) := by
      exact_mod_cast (show (singletonSet G.val i j).card ≤ n from
        (Finset.card_le_univ _).trans_eq (Fintype.card_fin n))
    have hN2 : ((singletonSet G.val i j).card : ℝ) ^ 2 ≤ (n : ℝ) ^ 2 :=
      pow_le_pow_left₀ (Nat.cast_nonneg _) hN 2
    calc
      _ ≤ ((singletonSet G.val i j).card : ℝ) ^ 2 / 2 *
          ∑ T : Assignment G.val i j, ∑ σ ∈ SlicePathComparison.swaps,
            (f (R T) - f (R (assignmentRelabel G.val i j σ T))) ^ 2 := hvar
      _ ≤ ((singletonSet G.val i j).card : ℝ) ^ 2 / 2 *
          ∑ T : Assignment G.val i j, E (R T) :=
        mul_le_mul_of_nonneg_left hsum (by positivity)
      _ ≤ (n : ℝ) ^ 2 / 2 * ∑ T : Assignment G.val i j, E (R T) :=
        mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right hN2 (by norm_num))
          (Finset.sum_nonneg (fun T _ => hE (R T)))
  have h := inner_fluctuation_le_of_assignment_sum_bound i j hij f E
    ((n : ℝ) ^ 2 / 2) hlocal
  calc
    _ ≤ (n : ℝ) ^ 2 / 2 * ∑ G : GraphState n d, E G := h
    _ = _ := by
      rw [PairSquaredEnergy.pairSwitchLaplacian_energy]
      dsimp only [E]
      ring

end Problem315.PairFiber

namespace Problem315.PairResampling

theorem fluctuation_energy_le_pairSwitchLaplacian {n : ℕ} {d : Fin n → ℕ}
    (f : StateSpace n d) (a : Finset (Fin n)) (ha : a ∈ pairs n) :
    inner ℝ f (fluctuation n d a f) ≤ (n : ℝ) ^ 2 *
      ∑ G : GraphState n d, f G * pairSwitchLaplacian n d a (fun H => f H) G := by
  classical
  have hcard : a.card = 2 := (Finset.mem_powersetCard.mp ha).2
  obtain ⟨i, j, hij, rfl⟩ := Finset.card_eq_two.mp hcard
  exact PairFiber.inner_fluctuation_le_pairSwitchLaplacian i j hij f

end Problem315.PairResampling

end

end OAI
