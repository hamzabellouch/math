import Mathlib
import OAI.Probability.BinarySweep.Processes.LocalPathWeight
import OAI.Probability.BinarySweep.FiniteLaws.CyclicHolder

namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace BinaryCoordinateSweeps
attribute [local instance] Classical.propDecidable

lemma independent_event_weight {J : Type*} [Fintype J] {X : J → Type*}
    [∀ j, Fintype (X j)] (w : ∀ j, X j → ℝ) (P : ∀ j, X j → Prop) :
    (∑ x : ∀ j, X j, if ∀ j, P j (x j) then ∏ j, w j (x j) else 0) =
      ∏ j, ∑ a : X j, if P j a then w j a else 0 := by
  classical
  calc
    _ = ∑ x : ∀ j, X j, ∏ j, if P j (x j) then w j (x j) else 0 := by
      apply Finset.sum_congr rfl
      intro x _
      exact Fintype.prod_ite_zero.symm
    _ = _ := (Fintype.prod_sum (fun j a => if P j a then w j a else 0)).symm

lemma conditionalWeight_factor {b h : ℕ} {bits : Fin b → ℕ} (H : PathFamily bits h)
    (z : ℝ) (g : GridChoices bits) :
    (if pathEvent H g then gridWeight bits z g else 0) =
      ∏ j, ∏ y, if Assigns (lineInput H j y) (lineOutput H j y) (g j y) then
        lineLaw (bits j) z (g j y) else 0 := by
  classical
  rw [pathEvent_iff_assigns]
  simp only [Fintype.prod_ite_zero]
  split_ifs <;> rfl

lemma sum_prod_grid {b : ℕ} (bits : Fin b → ℕ)
    (f : ∀ j : Fin b, GridOutside bits j → Equiv.Perm (Slot (bits j)) → ℝ) :
    (∑ g : GridChoices bits, ∏ j, ∏ y, f j y (g j y)) =
      ∏ j, ∏ y, ∑ σ, f j y σ := by
  rw [← Fintype.prod_sum (fun (j : Fin b)
    (g : GridOutside bits j → Equiv.Perm (Slot (bits j))) => ∏ y, f j y (g y))]
  apply Finset.prod_congr rfl
  intro j _
  exact (Fintype.prod_sum (f j)).symm

lemma conditionalNormalizer_eq_prod {b h : ℕ} {bits : Fin b → ℕ} (H : PathFamily bits h)
    (z : ℝ) : conditionalNormalizer H z = ∏ j, ∏ y, localPathWeight H z j y := by
  let f (j : Fin b) (y : GridOutside bits j) (σ : Equiv.Perm (Slot (bits j))) : ℝ :=
    if Assigns (lineInput H j y) (lineOutput H j y) σ then lineLaw (bits j) z σ else 0
  have hL : conditionalNormalizer H z =
      ∑ g : GridChoices bits, ∏ j, ∏ y, f j y (g j y) := by
    unfold conditionalNormalizer
    apply Finset.sum_congr rfl
    intro g _
    rw [conditionalWeight_factor]
  have hR : (∏ j, ∏ y, localPathWeight H z j y) =
      ∏ j, ∏ y, ∑ σ, f j y σ := by
    apply Finset.prod_congr rfl
    intro j _
    apply Finset.prod_congr rfl
    intro y _
    unfold localPathWeight assignmentWeight
    refine Finset.sum_congr ?_ ?_
    · ext σ
      simp only [Finset.mem_univ]
    intro σ _
    unfold f
    split_ifs <;> rfl
  rw [hL, hR]
  exact sum_prod_grid bits f

abbrev ConditionalChoices {b h : ℕ} {bits : Fin b → ℕ} (H : PathFamily bits h) :=
  {g : GridChoices bits // pathEvent H g}

instance conditionalChoicesFintype {b h : ℕ} {bits : Fin b → ℕ} (H : PathFamily bits h) :
    Fintype (ConditionalChoices H) := Fintype.ofFinite _

instance conditionalChoicesNonempty {b h : ℕ} {bits : Fin b → ℕ} (H : PathFamily bits h) :
    Nonempty (ConditionalChoices H) := by
  obtain ⟨g, hg⟩ := pathEvent_nonempty H
  exact ⟨⟨g, hg⟩⟩

def conditionalChoiceWeight {b h : ℕ} {bits : Fin b → ℕ} (H : PathFamily bits h)
    (z : ℝ) (g : ConditionalChoices H) : ℝ :=
  gridWeight bits z g.val / conditionalNormalizer H z

lemma conditionalChoiceWeight_nonneg {b h : ℕ} {bits : Fin b → ℕ} (H : PathFamily bits h)
    {z : ℝ} (hz : 0 ≤ z) (hz1 : z < 1) (g : ConditionalChoices H) :
    0 ≤ conditionalChoiceWeight H z g :=
  le_of_lt (div_pos (gridWeight_pos bits hz hz1 g.val) (conditionalNormalizer_pos H hz hz1))

lemma conditionalChoiceWeight_sum {b h : ℕ} {bits : Fin b → ℕ} (H : PathFamily bits h)
    {z : ℝ} (hz : 0 ≤ z) (hz1 : z < 1) :
    ∑ g : ConditionalChoices H, conditionalChoiceWeight H z g = 1 := by
  classical
  unfold conditionalChoiceWeight
  rw [← Finset.sum_div]
  have hs : (∑ g : ConditionalChoices H, gridWeight bits z g.val) =
      conditionalNormalizer H z := by
    unfold conditionalNormalizer
    rw [← Finset.sum_filter]
    exact (Finset.sum_subtype _ (by simp) _).symm
  rw [hs, div_self (conditionalNormalizer_pos H hz hz1).ne']

abbrev Placement {b h : ℕ} {bits : Fin b → ℕ} (H : PathFamily bits h)
    (k : ℕ) (t : Fin (b+1)) := Fin k ↪ FreeSlot H t

def placementBijection {b h : ℕ} {bits : Fin b → ℕ} (H : PathFamily bits h)
    (k : ℕ) (g : ConditionalChoices H) :
    Placement H k 0 ≃ Placement H k (Fin.last b) :=
  (Equiv.refl (Fin k)).embeddingCongr (remainingBijection H g.val g.property)

def placementProbability {b h : ℕ} {bits : Fin b → ℕ} (H : PathFamily bits h)
    (z : ℝ) {k : ℕ} (x : Placement H k 0) (y : Placement H k (Fin.last b)) : ℝ := by
  classical
  exact ∑ g : ConditionalChoices H,
    if placementBijection H k g x = y then conditionalChoiceWeight H z g else 0

section FiniteBijectionKernel
variable {Ω A B : Type*} [Fintype Ω] [Fintype A] [Fintype B]

def bijectionKernel (w : Ω → ℝ) (e : Ω → A ≃ B) (x : A) (y : B) : ℝ :=
  ∑ ω, if e ω x = y then w ω else 0

omit [Fintype A] [Fintype B] in
lemma bijectionKernel_nonneg (w : Ω → ℝ) (e : Ω → A ≃ B)
    (hw : ∀ ω, 0 ≤ w ω) (x : A) (y : B) : 0 ≤ bijectionKernel w e x y := by
  apply Finset.sum_nonneg
  intro ω _
  split_ifs
  · exact hw ω
  · exact le_rfl

omit [Fintype A] in
lemma bijectionKernel_rowSum (w : Ω → ℝ) (e : Ω → A ≃ B) (x : A) :
    ∑ y, bijectionKernel w e x y = ∑ ω, w ω := by
  unfold bijectionKernel
  rw [Finset.sum_comm]
  simp

lemma bijectionKernel_colSum (w : Ω → ℝ) (e : Ω → A ≃ B) (y : B) :
    ∑ x, bijectionKernel w e x y = ∑ ω, w ω := by
  unfold bijectionKernel
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro ω _
  rw [(e ω).sum_comp (fun x => if x = y then w ω else 0)]
  simp

end FiniteBijectionKernel

lemma placementProbability_eq_kernel {b h : ℕ} {bits : Fin b → ℕ}
    (H : PathFamily bits h) (z : ℝ) {k : ℕ}
    (x : Placement H k 0) (y : Placement H k (Fin.last b)) :
    placementProbability H z x y =
      bijectionKernel (conditionalChoiceWeight H z) (placementBijection H k) x y := by
  unfold placementProbability bijectionKernel
  apply Finset.sum_congr rfl
  intro g _
  split_ifs <;> rfl

lemma placementProbability_nonneg {b h : ℕ} {bits : Fin b → ℕ} (H : PathFamily bits h)
    {z : ℝ} (hz : 0 ≤ z) (hz1 : z < 1) {k : ℕ}
    (x : Placement H k 0) (y : Placement H k (Fin.last b)) :
    0 ≤ placementProbability H z x y := by
  rw [placementProbability_eq_kernel]
  exact bijectionKernel_nonneg _ _ (conditionalChoiceWeight_nonneg H hz hz1) x y

lemma placementProbability_rowSum {b h : ℕ} {bits : Fin b → ℕ} (H : PathFamily bits h)
    {z : ℝ} (hz : 0 ≤ z) (hz1 : z < 1) {k : ℕ} (x : Placement H k 0) :
    ∑ y, placementProbability H z x y = 1 := by
  simp_rw [placementProbability_eq_kernel]
  rw [bijectionKernel_rowSum, conditionalChoiceWeight_sum H hz hz1]

lemma placementProbability_colSum {b h : ℕ} {bits : Fin b → ℕ} (H : PathFamily bits h)
    {z : ℝ} (hz : 0 ≤ z) (hz1 : z < 1) {k : ℕ} (y : Placement H k (Fin.last b)) :
    ∑ x, placementProbability H z x y = 1 := by
  simp_rw [placementProbability_eq_kernel]
  rw [bijectionKernel_colSum, conditionalChoiceWeight_sum H hz hz1]

lemma card_placement {b h : ℕ} {bits : Fin b → ℕ} (H : PathFamily bits h)
    (k : ℕ) (t : Fin (b+1)) :
    Fintype.card (Placement H k t) = (gridSize bits - h).descFactorial k := by
  rw [Fintype.card_embedding_eq, card_freeSlot, Fintype.card_fin]

def placementIdentification {b h : ℕ} {bits : Fin b → ℕ} (H : PathFamily bits h) (k : ℕ) :
    Placement H k 0 ≃ Placement H k (Fin.last b) :=
  (Equiv.refl (Fin k)).embeddingCongr (freeIdentification H)

def placementKernel {b h : ℕ} {bits : Fin b → ℕ} (H : PathFamily bits h)
    (z : ℝ) {k : ℕ} (x y : Placement H k 0) : ℝ :=
  placementProbability H z x (placementIdentification H k y)

lemma placementKernel_nonneg {b h : ℕ} {bits : Fin b → ℕ} (H : PathFamily bits h)
    {z : ℝ} (hz : 0 ≤ z) (hz1 : z < 1) {k : ℕ} (x y : Placement H k 0) :
    0 ≤ placementKernel H z x y := placementProbability_nonneg H hz hz1 _ _

lemma placementKernel_rowSum {b h : ℕ} {bits : Fin b → ℕ} (H : PathFamily bits h)
    {z : ℝ} (hz : 0 ≤ z) (hz1 : z < 1) {k : ℕ} (x : Placement H k 0) :
    ∑ y, placementKernel H z x y = 1 := by
  unfold placementKernel
  rw [(placementIdentification H k).sum_comp]
  exact placementProbability_rowSum H hz hz1 x

lemma placementKernel_colSum {b h : ℕ} {bits : Fin b → ℕ} (H : PathFamily bits h)
    {z : ℝ} (hz : 0 ≤ z) (hz1 : z < 1) {k : ℕ} (y : Placement H k 0) :
    ∑ x, placementKernel H z x y = 1 := placementProbability_colSum H hz hz1 _

def placementEdge {b h : ℕ} {bits : Fin b → ℕ} (H : PathFamily bits h)
    (z : ℝ) (reverse : Bool) {k : ℕ} (x y : Placement H k 0) : ℝ :=
  if reverse then placementKernel H z y x else placementKernel H z x y

theorem placement_cycle_bound {b h : ℕ} {bits : Fin b → ℕ} (H : PathFamily bits h)
    {z : ℝ} (hz : 0 ≤ z) (hz1 : z < 1) (k n : ℕ) (reverse : Fin (n+1) → Bool) :
    (∑ x : Fin (n+1) → Placement H k 0,
      ∏ i, (placementEdge H z (reverse i) (x i) (x (finRotate (n+1) i))) ^
        ((n : ℝ) / (n+1 : ℝ))) ≤ ((gridSize bits - h).descFactorial k : ℝ) := by
  rw [← card_placement H k 0]
  apply Cyclic.sum_cycle_rpow_le_card
  · intro i x y
    unfold placementEdge
    split_ifs <;> exact placementKernel_nonneg H hz hz1 _ _
  · intro i y
    unfold placementEdge
    cases reverse i with
    | false => exact placementKernel_colSum H hz hz1 y
    | true => exact placementKernel_rowSum H hz hz1 y

end BinaryCoordinateSweeps

end

end OAI
