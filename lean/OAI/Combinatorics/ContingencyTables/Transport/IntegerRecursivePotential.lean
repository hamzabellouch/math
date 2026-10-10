import OAI.Combinatorics.ContingencyTables.Transport.IntegerCorrectionKernel

namespace OAI

/-! # Telescoping the actual raw integer recursion

The literal future kernel commutation and nonnegative square identity
control every future correction after a split. No signature property of
the weighted correction kernel is used.
-/

namespace ContingencyTables.IntegerWeightedTransport

open scoped BigOperators Classical Matrix
open CommonBasesFPRAS FactorialSignatures BalancedFamily BalancedEnumeration IntegerMarginal

universe u

variable {I : Type u} [Fintype I] [DecidableEq I]

lemma correction_future_lower (Ms : List ℕ) (U : ℕ) (hU : 2 ≤ U)
    (F : ((Coordinates I Ms ⊕ Bool) → ℕ) → ℝ) (z : I → ℕ)
    (h : I → ℝ) (g : ℕ → ℝ) (hF : ∀ x, 0 ≤ F x) :
    (integerRemovalMatrix (correctionKernel Ms (marginal F U)) z).toBilin' h h ≤
      ∑ j : Fin (U+1),
        (integerRemovalMatrix (correctionKernel Ms (exposePullback Ms F))
          (profile z j.val (U-j.val))).toBilin'
          (extendCoefficients h (g j.val) (g (j.val+1)))
          (extendCoefficients h (g j.val) (g (j.val+1))) := by
  rw [correctionKernel_current_commute]
  rw [Fin.sum_univ_eq_sum_range (fun j =>
    (integerRemovalMatrix (correctionKernel Ms (exposePullback Ms F))
      (profile z j (U-j))).toBilin'
      (extendCoefficients h (g j) (g (j+1)))
      (extendCoefficients h (g j) (g (j+1)))) (U+1)]
  have ht := future_form_monotone (correctionKernel Ms (exposePullback Ms F)) z
    (U-2) h g (correctionKernel_nonnegative Ms _ (fun x => hF _))
  simpa only [show U-2+2=U by omega, show U-2+3=U+1 by omega, IntegerMarginal.pairMatrix] using ht

omit [Fintype I] in
lemma integerRemovalMatrix_add (F G : (I → ℕ) → ℝ) (z : I → ℕ) :
    integerRemovalMatrix (fun x => F x+G x) z =
      integerRemovalMatrix F z + integerRemovalMatrix G z := by
  ext i j
  simp only [integerRemovalMatrix, Matrix.add_apply]
  split_ifs <;> simp

lemma correction_form_cons (Ms : List ℕ) (U : ℕ)
    (F : ((Coordinates I Ms ⊕ Bool) → ℕ) → ℝ) (z : I → ℕ) (h : I → ℝ) :
    (integerRemovalMatrix (correctionKernel (U::Ms) F) z).toBilin' h h =
      (integerRemovalMatrix (weightedFuture (exposedFamily Ms F) (U+1)) z).toBilin' h h +
      (integerRemovalMatrix (correctionKernel Ms (marginal F U)) z).toBilin' h h := by
  rw [correctionKernel, integerRemovalMatrix_add]
  simp only [map_add, LinearMap.add_apply]

/-- The entire leaf potential is bounded by the root potential minus
the sum of the actual root future forms. All recursive hypotheses are
derived from the original valid total slice. -/
theorem recursivePotential_bound : ∀ (Ms : List ℕ) {I : Type u} [Fintype I] [DecidableEq I]
    (F : (Coordinates I Ms → ℕ) → ℝ) (m z : I → ℕ) (R : ℕ) (h : I → ℝ),
    (∀ U ∈ Ms, 2 ≤ U) → (∀ x, 0 ≤ F x) →
    BalancedBox.PositiveSlice F (bounds m Ms) (R+Ms.sum) →
    BalancedBox.RemovalSlice F (bounds m Ms) (R+Ms.sum) →
    BalancedBox.InBox m z → (∑ i, z i)=R+1 →
    holeLinear (eliminate Ms F) z h=0 →
    recursivePotential Ms F z h ≤ holePotential (eliminate Ms F) z h -
      (integerRemovalMatrix (correctionKernel Ms F) z).toBilin' h h := by
  intro Ms
  induction Ms with
  | nil =>
    intro I _ _ F m z R h _ _ _ _ _ _ _
    change holePotential F z h ≤ holePotential F z h -
      (integerRemovalMatrix (fun _ => 0) z).toBilin' h h
    have hz : integerRemovalMatrix (fun _ : I → ℕ => (0:ℝ)) z=0 := by
      ext i j
      simp [integerRemovalMatrix]
    rw [hz]
    simp
  | cons U Ms ih =>
    intro I _ _ F m z R h hwidth hF hpos hsig hz htotal hbalance
    have hU := hwidth U (by simp)
    have htail : ∀ V ∈ Ms, 2 ≤ V := fun V hV => hwidth V (by simp [hV])
    have hp : BalancedBox.PositiveSlice F (profile (bounds m Ms) U U) (R+U+Ms.sum) := by
      rw [show R+U+Ms.sum=R+(U::Ms).sum by simp only [List.sum_cons]; omega]
      exact hpos
    have hs : BalancedBox.RemovalSlice F (profile (bounds m Ms) U U) (R+U+Ms.sum) := by
      rw [show R+U+Ms.sum=R+(U::Ms).sum by simp only [List.sum_cons]; omega]
      exact hsig
    let f := exposedFamily Ms F
    let G := exposePullback Ms F
    let g := pairCoefficient (cross f (U+1) z) (innerWeight f (U+1) z) h
    obtain ⟨hfpos,hfsig⟩ := exposed_slices Ms U m R F htail hp hs
    have hinner : ∀ k, 0 < k → k < U+1 → 0 < innerWeight f (U+1) z k := by
      intro k hk0 hkU
      rw [innerWeight, ite_eq_left ⟨hk0,hkU⟩]
      apply hfpos
      · apply BalancedBox.profile_inBox m z U (k-1) (U+1-1-k) hz <;> omega
      · rw [BalancedBox.profile_total, htotal]
        omega
    have hcum : pairCumulative (cross f (U+1) z) h (U+1)=0 := by
      rw [cumulative_eq_parent_demand]
      change holeLinear (marginal (exposedFamily Ms F) U) z h=0
      rw [exposed_marginal]
      exact hbalance
    have hGpos := expose_source_positive Ms U m R F hp
    have hGsig : BalancedBox.RemovalSlice G (bounds (profile m U U) Ms) (R+U+Ms.sum) := by
      have ht := removalSlice_reindex (exposeEquiv (I := I) Ms) F
        (profile (bounds m Ms) U U) (R+U+Ms.sum) hs
      rw [expose_bounds_forward] at ht
      exact ht
    have hleaves : (∑ j : Fin (U+1), recursivePotential Ms G
        (profile z j.val (U-j.val)) (extendCoefficients h (g j.val) (g (j.val+1)))) ≤
        ∑ j : Fin (U+1), (holePotential f (profile z j.val (U-j.val))
          (extendCoefficients h (g j.val) (g (j.val+1))) -
        (integerRemovalMatrix (correctionKernel Ms G) (profile z j.val (U-j.val))).toBilin'
          (extendCoefficients h (g j.val) (g (j.val+1)))
          (extendCoefficients h (g j.val) (g (j.val+1)))) := by
      apply Finset.sum_le_sum
      intro j _
      apply ih G (profile m U U) _ (R+U) _ htail (fun x => hF _) hGpos hGsig
      · exact BalancedBox.profile_inBox m z U j.val (U-j.val) hz
          (by have := j.isLt; omega) (Nat.sub_le _ _)
      · rw [BalancedBox.profile_total, htotal]
        have hj := j.isLt
        omega
      · exact integer_child_balance f z U j.val (by have := j.isLt; omega) h hinner hcum
    have hsplit := integer_split_potential_bound f z U h (by
      intro j hj0 hjU
      apply hfsig
      · exact BalancedBox.profile_inBox m z U j (U+1-j) hz (by omega) (by omega)
      · rw [BalancedBox.profile_total, htotal]
        omega) (by
      intro j hj0 hjU
      apply hfpos
      · exact BalancedBox.profile_inBox m z U (j-1) (U-j) hz (by omega) (Nat.sub_le _ _)
      · rw [BalancedBox.profile_total, htotal]
        omega) hcum
    change (∑ j ∈ Finset.range (U+1), holePotential f (profile z j (U-j))
      (extendCoefficients h (g j) (g (j+1)))) ≤ _ at hsplit
    rw [← weightedFuture_form, exposed_marginal] at hsplit
    rw [← Fin.sum_univ_eq_sum_range (fun j => holePotential f (profile z j (U-j))
      (extendCoefficients h (g j) (g (j+1)))) (U+1)] at hsplit
    have hfuture := correction_future_lower Ms U hU F z h g hF
    rw [Finset.sum_sub_distrib] at hleaves
    change (∑ j : Fin (U+1), recursivePotential Ms G
      (profile z j.val (U-j.val)) (extendCoefficients h (g j.val) (g (j.val+1)))) ≤ _
    rw [correction_form_cons]
    linarith

end ContingencyTables.IntegerWeightedTransport

end OAI
