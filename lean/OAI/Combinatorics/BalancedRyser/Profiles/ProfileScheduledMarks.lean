import OAI.Combinatorics.BalancedRyser.Probability.ExposureInterleaving
import OAI.Combinatorics.BalancedRyser.Profiles.ProfileMarkedOrders

namespace OAI

noncomputable section
attribute [local instance] Classical.propDecidable
open scoped BigOperators

namespace Balanced.ProfileScheduledMarks

open ExposureInterleaving ConditionalOrderVariance ProfileMarkedOrders

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

def label (U : Finset (Line F)) : U ≃ Fin U.card :=
  Fintype.equivFinOfCardEq (Fintype.card_coe U)

def prefixD (D C : Finset (Line F)) (s : Step D.card C.card) : Finset D :=
  (previousD (Real.sqrt 2) s).map (label D).symm.toEmbedding

def prefixC (D C : Finset (Line F)) (s : Step D.card C.card) : Finset C :=
  (previousC (Real.sqrt 2) s).map (label C).symm.toEmbedding

def unexposedD (D C : Finset (Line F)) (s : Step D.card C.card) : Finset D :=
  (remainingD (Real.sqrt 2) s).map (label D).symm.toEmbedding

def unexposedC (D C : Finset (Line F)) (s : Step D.card C.card) : Finset C :=
  (remainingC (Real.sqrt 2) s).map (label C).symm.toEmbedding

def stepD (D C : Finset (Line F)) (i : D) : Step D.card C.card :=
  Sum.inl (label D i)

def stepC (D C : Finset (Line F)) (j : C) : Step D.card C.card :=
  Sum.inr (label C j)

def zD (D : Finset (Line F)) (i : D) : ℝ := grid (label D i)

def zC (C : Finset (Line F)) (j : C) : ℝ := coverGrid (Real.sqrt 2) (label C j)

def ID (D C : Finset (Line F)) (i : D) : Finset D := prefixD D C (stepD D C i)
def JD (D C : Finset (Line F)) (i : D) : Finset C := prefixC D C (stepD D C i)
def IC (D C : Finset (Line F)) (j : C) : Finset C := prefixC D C (stepC D C j)
def JC (D C : Finset (Line F)) (j : C) : Finset D := prefixD D C (stepC D C j)

omit [Field F] [Fintype F] [DecidableEq F] in
@[simp] theorem current_not_ID (D C : Finset (Line F)) (i : D) : i ∉ ID D C i := by
  simp [ID, prefixD, stepD, Finset.mem_map_equiv]

omit [Field F] [Fintype F] [DecidableEq F] in
@[simp] theorem current_not_IC (D C : Finset (Line F)) (j : C) : j ∉ IC D C j := by
  simp [IC, prefixC, stepC, Finset.mem_map_equiv]

omit [Field F] [Fintype F] in
theorem prefixD_complement (D C : Finset (Line F)) (s : Step D.card C.card) :
    Finset.univ \ prefixD D C s = unexposedD D C s := by
  ext i
  simp [prefixD, unexposedD, previousD, remainingD, Finset.mem_map_equiv]

omit [Field F] [Fintype F] in
theorem prefixC_complement (D C : Finset (Line F)) (s : Step D.card C.card) :
    Finset.univ \ prefixC D C s = unexposedC D C s := by
  ext j
  simp [prefixC, unexposedC, previousC, remainingC, Finset.mem_map_equiv]

omit [Field F] [Fintype F] [DecidableEq F] in
theorem prefixD_add_unexposedD (D C : Finset (Line F))
    (s : Step D.card C.card) :
    (prefixD D C s).card + (unexposedD D C s).card = D.card := by
  simpa [prefixD, unexposedD] using previousD_add_remainingD (Real.sqrt 2) s

omit [Field F] [Fintype F] [DecidableEq F] in
theorem prefixC_add_unexposedC (D C : Finset (Line F))
    (s : Step D.card C.card) :
    (prefixC D C s).card + (unexposedC D C s).card = C.card := by
  simpa [prefixC, unexposedC] using previousC_add_remainingC (Real.sqrt 2) s

omit [Field F] [Fintype F] [DecidableEq F] in

theorem unexposed_fraction_bounds (D C : Finset (Line F))
    (hD : 0 < D.card) (hC : 0 < C.card) (s : Step D.card C.card) :
    |((unexposedD D C s).card : ℝ) / D.card - parameter (Real.sqrt 2) s| ≤
      1 / D.card ∧
    |((unexposedC D C s).card : ℝ) / C.card -
      parameter (Real.sqrt 2) s ^ (Real.sqrt 2)| ≤ 1 / C.card := by
  simpa [unexposedD, unexposedC] using source_remaining_fraction_bounds hD hC s

omit [Field F] [Fintype F] [DecidableEq F] in
@[simp] theorem unexposedC_empty (D : Finset (Line F))
    (s : Step D.card (∅ : Finset (Line F)).card) : unexposedC D ∅ s = ∅ := by
  exact Finset.eq_empty_of_forall_notMem
    (fun index => (Finset.notMem_empty index.val index.property).elim)

omit [Field F] [Fintype F] [DecidableEq F] in
@[simp] theorem prefixC_empty (D : Finset (Line F))
    (s : Step D.card (∅ : Finset (Line F)).card) : prefixC D ∅ s = ∅ := by
  exact Finset.eq_empty_of_forall_notMem (fun j => (Finset.notMem_empty j.1 j.2).elim)

def sourceMarkCount (D C : Finset (Line F)) (η ε : ℝ) (p : OrderPair D C) : ℕ :=
  markCount D C (ID D C) (JD D C) (zD D) (IC D C) (JC D C) (zC C) η ε p

theorem sourceMarkCount_le (D C : Finset (Line F)) (η ε : ℝ) (p : OrderPair D C) :
    sourceMarkCount D C η ε p ≤ D.card + C.card :=
  markCount_le D C (ID D C) (JD D C) (zD D) (IC D C) (JC D C) (zC C) η ε p

theorem sourceMarkCount_antitone (D C : Finset (Line F))
    {η ε η' ε' : ℝ} (hη : η ≤ η') (hε : ε ≤ ε') (p : OrderPair D C) :
    sourceMarkCount D C η' ε' p ≤ sourceMarkCount D C η ε p :=
  markCount_antitone D C (ID D C) (JD D C) (zD D) (IC D C) (JC D C) (zC C)
    hη hε p

def normalizedMean (D C : Finset (Line F)) (η ε : ℝ) : ℝ :=
  (𝔼 p : OrderPair D C, (sourceMarkCount D C η ε p : ℝ)) / Fintype.card F

theorem normalizedMean_antitone (D C : Finset (Line F))
    {η ε η' ε' : ℝ} (hη : η ≤ η') (hε : ε ≤ ε') :
    normalizedMean D C η' ε' ≤ normalizedMean D C η ε := by
  apply div_le_div_of_nonneg_right _ (by positivity)
  exact mean_markCount_antitone D C (ID D C) (JD D C) (zD D)
    (IC D C) (JC D C) (zC C) hη hε

omit [Field F] [Fintype F] [DecidableEq F] in

theorem sum_zD (D : Finset (Line F)) (f : ℝ → ℝ) :
    (∑ i : D, f (zD D i)) = ∑ j : Fin D.card, f (grid j) :=
  Fintype.sum_equiv (label D) _ _ (fun _ => rfl)

omit [Field F] [Fintype F] [DecidableEq F] in

theorem sum_zC (C : Finset (Line F)) (f : ℝ → ℝ) :
    (∑ i : C, f (zC C i)) = ∑ j : Fin C.card, f (coverGrid (Real.sqrt 2) j) :=
  Fintype.sum_equiv (label C) _ _ (fun _ => rfl)

end Balanced.ProfileScheduledMarks

end

end OAI
