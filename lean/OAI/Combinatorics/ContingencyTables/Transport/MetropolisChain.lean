import OAI.Combinatorics.ContingencyTables.Dense.PublishedCheeger

namespace OAI

/-!
# Finite weighted Metropolis chain

The holding probability, stationary law, and cut flow are proved from
positive weights, symmetric proposals, and the proposal-degree bound.
Only the final Poincaré consequence uses the explicit published Cheeger input.
-/

namespace ContingencyTables.MetropolisChain

open CommonBasesFPRAS
open scoped BigOperators Classical

noncomputable section

variable {X : Type*} [Fintype X] [Nonempty X]

def normalizer (w : X → ℝ) : ℝ := ∑ x, w x

theorem normalizer_pos (w : X → ℝ) (hw : ∀ x, 0 < w x) : 0 < normalizer w := by
  exact Finset.sum_pos (fun x _ => hw x) Finset.univ_nonempty

def move (w : X → ℝ) (Adj : X → X → Prop) (β : ℝ) (x y : X) : ℝ :=
  if Adj x y then β * min 1 (w y / w x) else 0

private theorem accept_mass (a b : ℝ) (ha : 0 < a) :
    a * min 1 (b / a) = min a b := by
  rw [mul_min_of_nonneg _ _ ha.le, mul_one, mul_div_cancel₀ _ (ne_of_gt ha)]

omit [Fintype X] [Nonempty X] in
theorem move_nonnegative (w : X → ℝ) (hw : ∀ x, 0 < w x)
    (Adj : X → X → Prop) (β : ℝ) (hβ : 0 ≤ β) (x y : X) :
    0 ≤ move w Adj β x y := by
  unfold move
  split_ifs
  · exact mul_nonneg hβ (le_min (by norm_num) (div_nonneg (hw y).le (hw x).le))
  · exact le_rfl

omit [Nonempty X] in
theorem move_reversible (w : X → ℝ) (hw : ∀ x, 0 < w x)
    (Adj : X → X → Prop) (hsym : ∀ x y, Adj x y ↔ Adj y x)
    (β : ℝ) (x y : X) :
    (w x / normalizer w) * move w Adj β x y =
      (w y / normalizer w) * move w Adj β y x := by
  unfold move
  by_cases h : Adj x y
  · rw [ite_eq_left h, ite_eq_left ((hsym x y).mp h)]
    have hx := accept_mass (w x) (w y) (hw x)
    have hy := accept_mass (w y) (w x) (hw y)
    calc
      _ = β * (w x * min 1 (w y / w x)) / normalizer w := by ring
      _ = β * min (w x) (w y) / normalizer w := by rw [hx]
      _ = β * (w y * min 1 (w x / w y)) / normalizer w := by rw [hy, min_comm]
      _ = _ := by ring
  · simp only [h, (hsym x y).not.mp h, ite_false, mul_zero]

omit [Nonempty X] in
theorem move_row_bound (w : X → ℝ) (Adj : X → X → Prop) (β : ℝ) (hβ : 0 ≤ β)
    (D : ℕ) (hdegree : ∀ x, (Finset.univ.filter (Adj x)).card ≤ D)
    (hproposal : (D : ℝ) * β ≤ 1 / 2) (x : X) : ∑ y, move w Adj β x y ≤ 1 / 2 := by
  calc
    _ ≤ ∑ y : X, if Adj x y then β else 0 := by
      apply Finset.sum_le_sum
      intro y _
      unfold move
      split_ifs
      · exact (mul_le_mul_of_nonneg_left (min_le_left _ _) hβ).trans_eq (mul_one β)
      · exact le_rfl
    _ = ((Finset.univ.filter (Adj x)).card : ℝ) * β := by
      rw [← Finset.sum_filter]
      simp
    _ ≤ (D : ℝ) * β := mul_le_mul_of_nonneg_right (by exact_mod_cast hdegree x) hβ
    _ ≤ 1 / 2 := hproposal

def chain (w : X → ℝ) (hw : ∀ x, 0 < w x)
    (Adj : X → X → Prop) (hsym : ∀ x y, Adj x y ↔ Adj y x)
    (β : ℝ) (hβ : 0 ≤ β) (D : ℕ)
    (hdegree : ∀ x, (Finset.univ.filter (Adj x)).card ≤ D)
    (hproposal : (D : ℝ) * β ≤ 1 / 2) : FiniteChain X :=
  FiniteChain.ofMoves (fun x => w x / normalizer w) (move w Adj β)
    (fun x => div_pos (hw x) (normalizer_pos w hw))
    (by rw [← Finset.sum_div]; exact div_self (ne_of_gt (normalizer_pos w hw)))
    (move_nonnegative w hw Adj β hβ)
    (move_row_bound w Adj β hβ D hdegree hproposal)
    (move_reversible w hw Adj hsym β)

theorem chain_flow (w : X → ℝ) (hw : ∀ x, 0 < w x)
    (Adj : X → X → Prop) (hsym : ∀ x y, Adj x y ↔ Adj y x)
    (β : ℝ) (hβ : 0 ≤ β) (D : ℕ)
    (hdegree : ∀ x, (Finset.univ.filter (Adj x)).card ≤ D)
    (hproposal : (D : ℝ) * β ≤ 1 / 2) (x y : X) (hxy : x ≠ y) :
    let C := chain w hw Adj hsym β hβ D hdegree hproposal
    C.π x * C.P x y = if Adj x y then β * min (w x) (w y) / normalizer w else 0 := by
  change (w x / normalizer w) * (move w Adj β x y + if x = y then _ else 0) = _
  rw [ite_eq_right hxy, add_zero]
  unfold move
  split_ifs
  · have hx := accept_mass (w x) (w y) (hw x)
    calc
      _ = β * (w x * min 1 (w y / w x)) / normalizer w := by ring
      _ = _ := by rw [hx]
  · exact mul_zero _

theorem chain_cut_flow (w : X → ℝ) (hw : ∀ x, 0 < w x)
    (Adj : X → X → Prop) (hsym : ∀ x y, Adj x y ↔ Adj y x)
    (β : ℝ) (hβ : 0 ≤ β) (D : ℕ)
    (hdegree : ∀ x, (Finset.univ.filter (Adj x)).card ≤ D)
    (hproposal : (D : ℝ) * β ≤ 1 / 2) (S : Finset X) :
    let C := chain w hw Adj hsym β hβ D hdegree hproposal
    (∑ x ∈ S, ∑ y ∈ Sᶜ, C.π x * C.P x y) =
      (β / normalizer w) * (∑ x ∈ S, ∑ y ∈ Sᶜ, if Adj x y then min (w x) (w y) else 0) := by
  dsimp only
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x hx
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro y hy
  have hxy : x ≠ y := fun h => (Finset.mem_compl.mp hy) (h ▸ hx)
  rw [chain_flow w hw Adj hsym β hβ D hdegree hproposal x y hxy]
  split_ifs <;> ring

theorem poincare_of_weighted_cut (w : X → ℝ) (hw : ∀ x, 0 < w x)
    (Adj : X → X → Prop) (hsym : ∀ x y, Adj x y ↔ Adj y x)
    (β : ℝ) (hβ : 0 ≤ β) (D : ℕ)
    (hdegree : ∀ x, (Finset.univ.filter (Adj x)).card ≤ D)
    (hproposal : (D : ℝ) * β ≤ 1 / 2)
    (hCheeger : PublishedInputs.FiniteCheeger X) (κ : ℝ) (hκ : 0 < κ)
    (hcut : ∀ S : Finset X,
      κ * min (∑ x ∈ S, w x) (∑ x ∈ Sᶜ, w x) ≤
        β * (∑ x ∈ S, ∑ y ∈ Sᶜ, if Adj x y then min (w x) (w y) else 0)) :
    ∀ f : X → ℝ,
      (chain w hw Adj hsym β hβ D hdegree hproposal).variance f ≤
        (2 / κ ^ 2) * (chain w hw Adj hsym β hβ D hdegree hproposal).energy f := by
  apply hCheeger _ κ hκ
  intro S
  rw [chain_cut_flow]
  change κ * min (∑ x ∈ S, w x / normalizer w) (∑ x ∈ Sᶜ, w x / normalizer w) ≤ _
  rw [← Finset.sum_div, ← Finset.sum_div, min_div_div_right (normalizer_pos w hw).le]
  have hz := normalizer_pos w hw
  have h := div_le_div_of_nonneg_right (hcut S) hz.le
  convert h using 1 <;> ring

end

end ContingencyTables.MetropolisChain

end OAI
