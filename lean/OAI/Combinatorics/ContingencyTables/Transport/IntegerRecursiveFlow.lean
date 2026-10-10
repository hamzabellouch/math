import OAI.Combinatorics.ContingencyTables.Transport.IntegerExposure
import OAI.Combinatorics.ContingencyTables.Transport.IntegerPairRecursion
import OAI.Combinatorics.ContingencyTables.Transport.IntegerLeafTransport

namespace OAI

/-! # The actual recursive signed integer demands

Every node exposes an ordinary balanced pair, computes the cumulative
coefficients from its actual remaining marginal, and retains the old
coefficients. The numerator can include any test function on complete
configurations. Its total leaf demand is exactly its root demand.
-/

namespace ContingencyTables.IntegerWeightedTransport

open scoped BigOperators Classical
open BalancedFamily BalancedEnumeration IntegerMarginal

universe u

noncomputable def recursivePotential : {I : Type u} → [Fintype I] → [DecidableEq I] →
    (Ms : List ℕ) → ((Coordinates I Ms → ℕ) → ℝ) → (I → ℕ) → (I → ℝ) → ℝ
  | _, _, _, [], F, z, h => holePotential F z h
  | I, _, _, U::Ms, F, z, h =>
    let f := exposedFamily Ms F
    let g := pairCoefficient (cross f (U+1) z) (innerWeight f (U+1) z) h
    ∑ j : Fin (U+1), recursivePotential Ms
      (fun x => F (fun t => x ((exposeEquiv (I := I) Ms).symm t)))
      (profile z j.val (U-j.val)) (extendCoefficients h (g j.val) (g (j.val+1)))

noncomputable def recursiveDemand : {I : Type u} → [Fintype I] → [DecidableEq I] →
    (Ms : List ℕ) → ((Coordinates I Ms → ℕ) → ℝ) →
    ((Coordinates I Ms → ℕ) → ℝ) → (I → ℕ) → (I → ℝ) → ℝ
  | _, _, _, [], _, G, z, h => holeLinear G z h
  | I, _, _, U::Ms, F, G, z, h =>
    let f := exposedFamily Ms F
    let g := pairCoefficient (cross f (U+1) z) (innerWeight f (U+1) z) h
    ∑ j : Fin (U+1), recursiveDemand Ms
      (fun x => F (fun t => x ((exposeEquiv (I := I) Ms).symm t)))
      (fun x => G (fun t => x ((exposeEquiv (I := I) Ms).symm t)))
      (profile z j.val (U-j.val)) (extendCoefficients h (g j.val) (g (j.val+1)))

/-- All auxiliary ordinary negative-pair divergences cancel in the
actual recursion. No limit of recursive coefficients is needed. -/
theorem recursiveDemand_eq : ∀ (Ms : List ℕ) {I : Type u} [Fintype I] [DecidableEq I]
    (F G : (Coordinates I Ms → ℕ) → ℝ) (z : I → ℕ) (h : I → ℝ),
    recursiveDemand Ms F G z h = holeLinear (eliminate Ms G) z h := by
  intro Ms
  induction Ms with
  | nil => intro I _ _ F G z h; rfl
  | cons U Ms ih =>
    intro I _ _ F G z h
    let f := exposedFamily Ms F
    let g := pairCoefficient (cross f (U+1) z) (innerWeight f (U+1) z) h
    change (∑ j : Fin (U+1), recursiveDemand Ms
      (fun x => F (fun t => x ((exposeEquiv (I := I) Ms).symm t)))
      (fun x => G (fun t => x ((exposeEquiv (I := I) Ms).symm t)))
      (profile z j.val (U-j.val)) (extendCoefficients h (g j.val) (g (j.val+1)))) = _
    simp_rw [ih]
    change (∑ j : Fin (U+1), holeLinear (exposedFamily Ms G)
      (profile z j.val (U-j.val)) (extendCoefficients h (g j.val) (g (j.val+1)))) = _
    rw [Fin.sum_univ_eq_sum_range (fun j => holeLinear (exposedFamily Ms G)
      (profile z j (U-j)) (extendCoefficients h (g j) (g (j+1)))) (U+1)]
    rw [integer_demand_conservation, exposed_marginal]

theorem recursivePotential_nonnegative : ∀ (Ms : List ℕ) {I : Type u} [Fintype I] [DecidableEq I]
    (F : (Coordinates I Ms → ℕ) → ℝ) (z : I → ℕ) (h : I → ℝ),
    (∀ p, 0≤F p) → 0≤recursivePotential Ms F z h := by
  intro Ms
  induction Ms with
  | nil =>
    intro I _ _ F z h hF
    apply Finset.sum_nonneg
    intro i _
    apply mul_nonneg _ (sq_nonneg _)
    unfold oneHole
    split_ifs
    · exact hF _
    · exact le_rfl
  | cons U Ms ih =>
    intro I _ _ F z h hF
    apply Finset.sum_nonneg
    intro j _
    exact ih _ _ _ (fun p => hF _)


noncomputable def recursiveEnergy : {I : Type u} → [Fintype I] → [DecidableEq I] →
    (Ms : List ℕ) → ((Coordinates I Ms → ℕ) → ℝ) →
    ((Coordinates I Ms → ℕ) → ℝ) → (I → ℕ) → (I → ℝ) → ℝ
  | _, _, _, [], F, H, z, _ =>
    SignedTransport.cliqueEnergy (oneHole F z) (fun _ => 1) (fun i => H (FactorialSignatures.removeOne z i))
  | I, _, _, U::Ms, F, H, z, h =>
    let f := exposedFamily Ms F
    let g := pairCoefficient (cross f (U+1) z) (innerWeight f (U+1) z) h
    ∑ j : Fin (U+1), recursiveEnergy Ms
      (fun x => F (fun t => x ((exposeEquiv (I := I) Ms).symm t)))
      (fun x => H (fun t => x ((exposeEquiv (I := I) Ms).symm t)))
      (profile z j.val (U-j.val)) (extendCoefficients h (g j.val) (g (j.val+1)))

lemma oneHole_nonnegative {I : Type*} [DecidableEq I] (F : (I → ℕ) → ℝ)
    (hF : ∀ p, 0≤F p) (z : I → ℕ) (i : I) : 0≤oneHole F z i := by
  unfold oneHole
  split_ifs
  · exact hF _
  · exact le_rfl

lemma oneHole_mul {I : Type*} [DecidableEq I] (F H : (I → ℕ) → ℝ)
    (z : I → ℕ) (i : I) :
    oneHole (fun p => F p*H p) z i = oneHole F z i * H (FactorialSignatures.removeOne z i) := by
  unfold oneHole
  split_ifs <;> simp

theorem recursiveEnergy_nonnegative : ∀ (Ms : List ℕ) {I : Type u} [Fintype I] [DecidableEq I]
    (F H : (Coordinates I Ms → ℕ) → ℝ) (z : I → ℕ) (h : I → ℝ),
    (∀ p, 0≤F p) → 0≤recursiveEnergy Ms F H z h := by
  intro Ms
  induction Ms with
  | nil =>
    intro I _ _ F H z h hF
    change 0≤SignedTransport.cliqueEnergy (oneHole F z) (fun _ => 1)
      (fun i => H (FactorialSignatures.removeOne z i))
    unfold SignedTransport.cliqueEnergy
    apply div_nonneg _ (by norm_num)
    apply Finset.sum_nonneg
    intro i _
    apply Finset.sum_nonneg
    intro j _
    exact mul_nonneg (le_min (by simpa using oneHole_nonnegative F hF z i)
      (by simpa using oneHole_nonnegative F hF z j)) (sq_nonneg _)
  | cons U Ms ih =>
    intro I _ _ F H z h hF
    apply Finset.sum_nonneg
    intro j _
    exact ih _ _ _ _ (fun p => hF _)


noncomputable def recursivelyBalanced : {I : Type u} → [Fintype I] → [DecidableEq I] →
    (Ms : List ℕ) → ((Coordinates I Ms → ℕ) → ℝ) → (I → ℕ) → (I → ℝ) → Prop
  | _, _, _, [], F, z, h => holeLinear F z h = 0
  | I, _, _, U::Ms, F, z, h =>
    let f := exposedFamily Ms F
    let g := pairCoefficient (cross f (U+1) z) (innerWeight f (U+1) z) h
    ∀ j : Fin (U+1), recursivelyBalanced Ms
      (fun x => F (fun t => x ((exposeEquiv (I := I) Ms).symm t)))
      (profile z j.val (U-j.val)) (extendCoefficients h (g j.val) (g (j.val+1)))

/-- Positivity only on the valid box and degree supplies every cumulative
coefficient denominator and propagates root balance to all actual leaves. -/
theorem recursivelyBalanced_of_slice : ∀ (Ms : List ℕ) {I : Type u} [Fintype I] [DecidableEq I]
    (F : (Coordinates I Ms → ℕ) → ℝ) (m z : I → ℕ) (R : ℕ) (h : I → ℝ),
    BalancedBox.PositiveSlice F (bounds m Ms) (R+Ms.sum) →
    BalancedBox.InBox m z → (∑ i, z i)=R+1 →
    holeLinear (eliminate Ms F) z h=0 → recursivelyBalanced Ms F z h := by
  intro Ms
  induction Ms with
  | nil => intro I _ _ F m z R h _ _ _ hb; exact hb
  | cons U Ms ih =>
    intro I _ _ F m z R h hpos hz htotal hbalance
    have hp : BalancedBox.PositiveSlice F (profile (bounds m Ms) U U) (R+U+Ms.sum) := by
      rw [show R+U+Ms.sum=R+(U::Ms).sum by simp only [List.sum_cons]; omega]
      exact hpos
    let f := exposedFamily Ms F
    let g := pairCoefficient (cross f (U+1) z) (innerWeight f (U+1) z) h
    have hfpos := exposed_positive Ms U m R F hp
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
    change ∀ j : Fin (U+1), recursivelyBalanced Ms
      (fun x => F (fun t => x ((exposeEquiv (I := I) Ms).symm t)))
      (profile z j.val (U-j.val)) (extendCoefficients h (g j.val) (g (j.val+1)))
    intro j
    apply ih _ (profile m U U) _ (R+U) _ (expose_source_positive Ms U m R F hp)
    · exact BalancedBox.profile_inBox m z U j.val (U-j.val) hz (by omega) (Nat.sub_le _ _)
    · rw [BalancedBox.profile_total, htotal]
      have hj := j.isLt
      omega
    · change holeLinear f (profile z j.val (U-j.val))
        (extendCoefficients h (g j.val) (g (j.val+1)))=0
      exact integer_child_balance f z U j.val (by have := j.isLt; omega) h hinner hcum

/-- The full actual recursive signed demands satisfy the leaf energy
comparison once their recursively proved balances are supplied. -/
theorem recursive_signed_transport : ∀ (Ms : List ℕ) {I : Type u} [Fintype I] [DecidableEq I]
    (F H : (Coordinates I Ms → ℕ) → ℝ) (z : I → ℕ) (h : I → ℝ),
    (∀ p, 0≤F p) → recursivelyBalanced Ms F z h →
    (recursiveDemand Ms F (fun p => F p*H p) z h)^2 ≤
      recursivePotential Ms F z h * recursiveEnergy Ms F H z h := by
  intro Ms
  induction Ms with
  | nil =>
    intro I _ _ F H z h hF hbal
    have ht := integer_leaf_transport F z h
      (fun i => H (FactorialSignatures.removeOne z i)) hF hbal
    change (holeLinear (fun p => F p*H p) z h)^2 ≤ holePotential F z h *
      SignedTransport.cliqueEnergy (oneHole F z) (fun _ => 1)
        (fun i => H (FactorialSignatures.removeOne z i))
    have he : holeLinear (fun p => F p*H p) z h =
        ∑ i, oneHole F z i * h i * H (FactorialSignatures.removeOne z i) := by
      unfold holeLinear
      simp_rw [oneHole_mul]
      apply Finset.sum_congr rfl
      intro i _
      ring
    rw [he]
    exact ht
  | cons U Ms ih =>
    intro I _ _ F H z h hF hbal
    change (∑ j : Fin (U+1), recursiveDemand Ms _ _ _ _)^2 ≤
      (∑ j : Fin (U+1), recursivePotential Ms _ _ _) *
      (∑ j : Fin (U+1), recursiveEnergy Ms _ _ _ _)
    apply Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul Finset.univ
    · intro j _
      exact recursivePotential_nonnegative Ms _ _ _ (fun p => hF _)
    · intro j _
      exact recursiveEnergy_nonnegative Ms _ _ _ _ (fun p => hF _)
    · intro j _
      exact ih _ _ _ _ (fun p => hF _) (hbal j)

/-- The recursively accumulated clique energy is independent of all
signed coefficients; only the actual display and weight family matter. -/
theorem recursiveEnergy_independent : ∀ (Ms : List ℕ) {I : Type u} [Fintype I] [DecidableEq I]
    (F H : (Coordinates I Ms → ℕ) → ℝ) (z : I → ℕ) (h h' : I → ℝ),
    recursiveEnergy Ms F H z h = recursiveEnergy Ms F H z h' := by
  intro Ms
  induction Ms with
  | nil => intro I _ _ F H z h h'; rfl
  | cons U Ms ih =>
    intro I _ _ F H z h h'
    apply Finset.sum_congr rfl
    intro j _
    exact ih _ _ _ _ _

/-- The full recursive comparison with all balances discharged from
the literal softened slice, expressed solely using the root numerator. -/
theorem integer_recursive_transport_of_slice {I : Type u} [Fintype I] [DecidableEq I]
    (Ms : List ℕ) (F H : (Coordinates I Ms → ℕ) → ℝ) (m z : I → ℕ)
    (R : ℕ) (h : I → ℝ) (hF : ∀ p, 0 ≤ F p)
    (hpos : BalancedBox.PositiveSlice F (bounds m Ms) (R+Ms.sum))
    (hz : BalancedBox.InBox m z) (htotal : (∑ i, z i)=R+1)
    (hbalance : holeLinear (eliminate Ms F) z h=0) :
    (holeLinear (eliminate Ms (fun p => F p*H p)) z h)^2 ≤
      recursivePotential Ms F z h * recursiveEnergy Ms F H z h := by
  rw [← recursiveDemand_eq Ms F (fun p => F p*H p) z h]
  exact recursive_signed_transport Ms F H z h hF
    (recursivelyBalanced_of_slice Ms F m z R h hpos hz htotal hbalance)

end ContingencyTables.IntegerWeightedTransport

end OAI
