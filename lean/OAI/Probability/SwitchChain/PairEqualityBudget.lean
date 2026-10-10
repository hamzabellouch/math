import OAI.Probability.SwitchChain.PairEqualityRestriction
import OAI.Probability.SwitchChain.PairFiberEqualityTransport
import OAI.Probability.SwitchChain.PairFiberEnergy
import OAI.Probability.SwitchChain.SliceCardEncoding
import OAI.Probability.SwitchChain.PairSwapFlipProjection

namespace OAI

noncomputable section
open scoped BigOperators RealInnerProductSpace

namespace Problem315.PairEquality
open PairResampling PairFiber
attribute [local instance] Classical.propDecidable
variable {n : ℕ} {d : Fin n → ℕ}

def assignmentNormalizedEquiv (G : GraphState n d) (i j : Fin n) :
    Assignment G.val i j ≃
      SliceNormalized.State (singletonSet G.val i j) (leftSet G.val i j).card :=
  (assignmentSliceEquiv G.val i j).trans (cardSliceEquivPowerset _)

theorem assignmentVector_eq_raw (G : GraphState n d) (i j : Fin n) (hij : i ≠ j)
    (x y : singletonSet G.val i j) (hxy : x ≠ y) :
    assignmentVector G i j x.val y.val =
      SliceNormalized.reindexedRaw (assignmentNormalizedEquiv G i j) x y := by
  have hval : x.val ≠ y.val := fun h => hxy (Subtype.ext h)
  have ha : active i j x.val y.val G := ⟨x.property, y.property⟩
  ext T
  let H := (stateFiberEquiv G i j hij).symm T
  have hc := centered_reconstruction G i j x.val y.val hij hval ha T
  have hr := fluctuation_eq_raw_of_fiber G i j hij x y hxy
    (observable i x.val y.val) (fun _ => rfl) H
  change centered i j x.val y.val H.val = _ at hr
  change (if active i j x.val y.val G then
    SliceMoments.centeredEqual (singletonSet G.val i j) (leftSet G.val i j).card
      x.val y.val T.val else 0) = _
  rw [ite_eq_left ha, ← hc]
  change centered i j x.val y.val H.val = _
  rw [hr]
  change SliceNormalized.raw (leftSet G.val i j).card x y
      (stateFiberNormalizedEquiv G i j hij H) =
    SliceNormalized.raw (leftSet G.val i j).card x y (assignmentNormalizedEquiv G i j T)
  have he : stateFiberNormalizedEquiv G i j hij H = assignmentNormalizedEquiv G i j T := by
    change (assignmentSliceEquiv G.val i j).trans (cardSliceEquivPowerset _)
      (stateFiberEquiv G i j hij ((stateFiberEquiv G i j hij).symm T)) = _
    rw [Equiv.apply_symm_apply]
    rfl
  rw [he]

theorem restriction_projection_energy_eq_raw (G : GraphState n d)
    (i j : Fin n) (hij : i ≠ j) (x y : singletonSet G.val i j)
    (f : StateSpace n d) :
    (if x = y then 0 else
      ‖assignmentRestriction G i j hij (projection i j x.val y.val f)‖ ^ 2) =
    ‖(ℝ ∙ SliceNormalized.reindexedRaw (assignmentNormalizedEquiv G i j) x y).starProjection
      (assignmentRestriction G i j hij f)‖ ^ 2 := by
  by_cases hxy : x = y
  · subst y
    have hz : SliceNormalized.reindexedRaw (assignmentNormalizedEquiv G i j) x x = 0 := by
      ext T
      simp
    simp [hz]
  · rw [ite_eq_right hxy, assignmentRestriction_projection G i j x.val y.val hij
      (fun h => hxy (Subtype.ext h)), assignmentVector_eq_raw G i j hij x y hxy]

theorem assignment_projection_budget (G : GraphState n d) (i j : Fin n)
    (hij : i ≠ j) (f : StateSpace n d) :
    (∑ x : singletonSet G.val i j, ∑ y : singletonSet G.val i j,
      if x = y then 0 else
        ‖assignmentRestriction G i j hij (projection i j x.val y.val f)‖ ^ 2) ≤
      (1 / 4 : ℝ) * ∑ x : singletonSet G.val i j, ∑ y : singletonSet G.val i j,
        ∑ T : Assignment G.val i j,
          (f ((stateFiberEquiv G i j hij).symm T).val -
            f ((stateFiberEquiv G i j hij).symm
              (assignmentRelabel G.val i j (Equiv.swap x y) T)).val) ^ 2 := by
  have hq : (leftSet G.val i j).card ≤ Fintype.card (singletonSet G.val i j) := by
    rw [Fintype.card_coe]
    exact Finset.card_le_card (leftSet_subset_singletonSet G.val i j)
  have h := SliceNormalized.reindexed_projection_energy_le_swap_sum
    (assignmentNormalizedEquiv G i j) hq (assignmentRestriction G i j hij f)
  have hswap (x y : singletonSet G.val i j) (T : Assignment G.val i j) :
      (assignmentNormalizedEquiv G i j).symm
        (SliceEuclideanGenerator.swapState (leftSet G.val i j).card x y
          (assignmentNormalizedEquiv G i j T)) =
        assignmentRelabel G.val i j (Equiv.swap x y) T := by
    exact SliceNormalized.conjugated_swap_cardSlice (assignmentSliceEquiv G.val i j) x y T
  simp_rw [hswap, assignmentRestriction_apply] at h
  simp_rw [restriction_projection_energy_eq_raw G i j hij]
  linarith

theorem assignmentRestriction_projection_eq_zero_of_inactive
    (G : GraphState n d) (i j k l : Fin n) (hij : i ≠ j) (hkl : k ≠ l)
    (ha : ¬ active i j k l G) (f : StateSpace n d) :
    assignmentRestriction G i j hij (projection i j k l f) = 0 := by
  rw [assignmentRestriction_projection G i j k l hij hkl]
  have hz : assignmentVector G i j k l = 0 := by
    ext T
    simp [assignmentVector, ha]
  simp [hz]

theorem sum_array_subtype {V : Type*} [DecidableEq V]
    (s : Finset V) (F : V → V → ℝ) :
    (∑ k : s, ∑ l : s, F k.val l.val) = ∑ k ∈ s, ∑ l ∈ s, F k l := by
  calc
    _ = ∑ k : s, ∑ l ∈ s, F k.val l := by
      apply Finset.sum_congr rfl
      intro k _
      exact Finset.sum_coe_sort s (fun l => F k.val l)
    _ = _ := Finset.sum_coe_sort s (fun k => ∑ l ∈ s, F k l)

theorem sum_array_eq_subtype {V : Type*} [Fintype V] [DecidableEq V]
    (s : Finset V) (F : V → V → ℝ)
    (hs : ∀ k l, ¬ (k ∈ s ∧ l ∈ s) → F k l = 0) :
    (∑ k, ∑ l, F k l) = ∑ k : s, ∑ l : s, F k.val l.val := by
  calc
    _ = ∑ k ∈ s, ∑ l, F k l := by
      symm
      apply Finset.sum_subset (Finset.subset_univ s)
      intro k _ hk
      apply Finset.sum_eq_zero
      intro l _
      exact hs k l (fun h => hk h.1)
    _ = ∑ k ∈ s, ∑ l ∈ s, F k l := by
      apply Finset.sum_congr rfl
      intro k hk
      symm
      apply Finset.sum_subset (Finset.subset_univ s)
      intro l _ hl
      exact hs k l (fun h => hl h.2)
    _ = _ := (sum_array_subtype s F).symm

theorem assignment_projection_sum_eq_singletons (G : GraphState n d)
    (i j : Fin n) (hij : i ≠ j) (f : StateSpace n d) :
    (∑ k, ∑ l, if k = l then 0 else
      ‖assignmentRestriction G i j hij (projection i j k l f)‖ ^ 2) =
    ∑ x : singletonSet G.val i j, ∑ y : singletonSet G.val i j,
      if x = y then 0 else
        ‖assignmentRestriction G i j hij (projection i j x.val y.val f)‖ ^ 2 := by
  have h := sum_array_eq_subtype (singletonSet G.val i j)
    (fun k l => if k = l then 0 else
      ‖assignmentRestriction G i j hij (projection i j k l f)‖ ^ 2) ?_
  · simpa only [Subtype.ext_iff] using h
  · intro k l ha
    by_cases hkl : k = l
    · simp [hkl]
    · rw [ite_eq_right hkl, assignmentRestriction_projection_eq_zero_of_inactive
        G i j k l hij hkl ha f]
      simp

theorem sum_assignmentRestriction_norm_sq (i j : Fin n) (hij : i ≠ j)
    (f : StateSpace n d) :
    (∑ G : GraphState n d, ‖assignmentRestriction G i j hij f‖ ^ 2 /
      (Nat.choose (singletonSet G.val i j).card (leftSet G.val i j).card : ℝ)) =
      ‖f‖ ^ 2 := by
  simp_rw [EuclideanSpace.real_norm_sq_eq]
  simp only [assignmentRestriction_apply]
  have hav (G : GraphState n d) := assignment_average_eq_fiber_average G i j hij
    (fun H => (f H)^2)
  simp_rw [hav]
  exact sum_fiber_average {i,j} (fun H => (f H)^2)

theorem sum_assignmentRestriction_family_norm_sq
    {A : Type*} [Fintype A] (i j : Fin n) (hij : i ≠ j)
    (F : A → StateSpace n d) :
    (∑ G : GraphState n d, (∑ a, ‖assignmentRestriction G i j hij (F a)‖ ^ 2) /
      (Nat.choose (singletonSet G.val i j).card (leftSet G.val i j).card : ℝ)) =
      ∑ a, ‖F a‖ ^ 2 := by
  simp_rw [Finset.sum_div]
  rw [Finset.sum_comm]
  simp_rw [sum_assignmentRestriction_norm_sq i j hij]

theorem sum_norm_sq_le_of_assignment_restriction_budget
    {A B : Type*} [Fintype A] [Fintype B]
    (i j : Fin n) (hij : i ≠ j) (F : A → StateSpace n d) (H : B → StateSpace n d)
    (hl : ∀ G : GraphState n d,
      (∑ a, ‖assignmentRestriction G i j hij (F a)‖ ^ 2) ≤
        ∑ b, ‖assignmentRestriction G i j hij (H b)‖ ^ 2) :
    (∑ a, ‖F a‖ ^ 2) ≤ ∑ b, ‖H b‖ ^ 2 := by
  rw [← sum_assignmentRestriction_family_norm_sq i j hij F,
    ← sum_assignmentRestriction_family_norm_sq i j hij H]
  apply Finset.sum_le_sum
  intro G _
  exact div_le_div_of_nonneg_right (hl G) (Nat.cast_nonneg _)

def orderedGain (i j k l : Fin n) : StateSpace n d →L[ℝ] StateSpace n d :=
  if h : FourDistinct i k l j then
    SwitchFlip.projection (fourVertexProposal i k l j h) else 0

@[simp] theorem orderedGain_of_distinct (i j k l : Fin n)
    (h : FourDistinct i k l j) :
    orderedGain (d := d) i j k l =
      SwitchFlip.projection (fourVertexProposal i k l j h) := by
  simp only [orderedGain, dite_eq_left h]

theorem assignment_orderedGain_norm_sq (G : GraphState n d)
    (i j : Fin n) (hij : i ≠ j) (x y : singletonSet G.val i j)
    (f : StateSpace n d) :
    ‖assignmentRestriction G i j hij (orderedGain i j x.val y.val f)‖ ^ 2 =
      (1 / 4 : ℝ) * ∑ T : Assignment G.val i j,
        (f ((stateFiberEquiv G i j hij).symm T).val -
          f ((stateFiberEquiv G i j hij).symm
            (assignmentRelabel G.val i j (Equiv.swap x y) T)).val) ^ 2 := by
  by_cases hxy : x = y
  · subst y
    have hd : ¬ FourDistinct i x.val x.val j := fun h => h.2.2.2.1 rfl
    simp [orderedGain, hd, assignmentRelabel, SlicePermutationAction.relabel]
  · have hd := fourDistinct_of_singleton_labels G.val i j hij x y hxy
    rw [orderedGain_of_distinct i j x.val y.val hd, EuclideanSpace.real_norm_sq_eq,
      Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro T _
    rw [assignmentRestriction_apply, projection_at_assignment G i j hij x y hd]
    ring

theorem sum_array_subtype_le {V : Type*} [Fintype V] [DecidableEq V]
    (s : Finset V) (F : V → V → ℝ) (hF : ∀ k l, 0 ≤ F k l) :
    (∑ k : s, ∑ l : s, F k.val l.val) ≤ ∑ k, ∑ l, F k l := by
  rw [sum_array_subtype]
  calc
    _ ≤ ∑ k ∈ s, ∑ l, F k l := by
      apply Finset.sum_le_sum
      intro k _
      apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ s)
      intro l _ _
      exact hF k l
    _ ≤ _ := by
      apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ s)
      intro k _ _
      exact Finset.sum_nonneg (fun l _ => hF k l)

theorem assignment_ordered_projection_budget (G : GraphState n d)
    (i j : Fin n) (hij : i ≠ j) (f : StateSpace n d) :
    (∑ k, ∑ l, if k = l then 0 else
      ‖assignmentRestriction G i j hij (projection i j k l f)‖ ^ 2) ≤
      ∑ k, ∑ l, ‖assignmentRestriction G i j hij (orderedGain i j k l f)‖ ^ 2 := by
  rw [assignment_projection_sum_eq_singletons G i j hij f]
  calc
    _ ≤ (1 / 4 : ℝ) * ∑ x : singletonSet G.val i j, ∑ y : singletonSet G.val i j,
        ∑ T : Assignment G.val i j,
          (f ((stateFiberEquiv G i j hij).symm T).val -
            f ((stateFiberEquiv G i j hij).symm
              (assignmentRelabel G.val i j (Equiv.swap x y) T)).val) ^ 2 :=
      assignment_projection_budget G i j hij f
    _ = ∑ x : singletonSet G.val i j, ∑ y : singletonSet G.val i j,
        ‖assignmentRestriction G i j hij (orderedGain i j x.val y.val f)‖ ^ 2 := by
      simp_rw [assignment_orderedGain_norm_sq G i j hij]
      simp only [Finset.mul_sum]
    _ ≤ _ := sum_array_subtype_le (singletonSet G.val i j)
      (fun k l => ‖assignmentRestriction G i j hij (orderedGain i j k l f)‖ ^ 2)
      (fun k l => sq_nonneg _)

theorem ordered_projection_budget (i j : Fin n) (hij : i ≠ j) (f : StateSpace n d) :
    (∑ k, ∑ l, if k = l then 0 else ‖projection i j k l f‖ ^ 2) ≤
      ∑ k, ∑ l, ‖orderedGain i j k l f‖ ^ 2 := by
  let F : Fin n × Fin n → StateSpace n d :=
    fun p => if p.1 = p.2 then 0 else projection i j p.1 p.2 f
  let H : Fin n × Fin n → StateSpace n d := fun p => orderedGain i j p.1 p.2 f
  have hF (G : GraphState n d) (k l : Fin n) :
      ‖assignmentRestriction G i j hij (F (k,l))‖ ^ 2 =
        if k = l then 0 else
          ‖assignmentRestriction G i j hij (projection i j k l f)‖ ^ 2 := by
    by_cases hkl : k = l <;> simp [F, hkl]
  have h := sum_norm_sq_le_of_assignment_restriction_budget i j hij F H (fun G => by
    simp only [Fintype.sum_prod_type]
    simp_rw [hF]
    exact assignment_ordered_projection_budget G i j hij f)
  have hFg (k l : Fin n) : ‖F (k,l)‖ ^ 2 =
      if k = l then 0 else ‖projection i j k l f‖ ^ 2 := by
    by_cases hkl : k = l <;> simp [F, hkl]
  simpa only [Fintype.sum_prod_type, hFg, H] using h

end Problem315.PairEquality

end

end OAI
