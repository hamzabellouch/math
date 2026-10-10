import OAI.Combinatorics.DiscreteConvexity.Basic
import OAI.Combinatorics.DiscreteConvexity.CoordinateObservations
import OAI.Combinatorics.DiscreteConvexity.UnionBound
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace OAI

/-!
# The mandatory-row coupling at high density

The auxiliary inclusion probability is valid throughout the closed high-density
regime `1 ≤ L * p`, including equality, when it is zero.

At each coordinate the mandatory label is uniform and independent of the
independent Bernoulli marks. Taking a product of these laws across coordinates
gives each row its full Bernoulli subset law. The union is full in every outcome;
only marginal probabilities are used to obtain simultaneous family membership.
-/

noncomputable section

namespace TalagrandDiscreteConvexity

/-- The extra inclusion probability after the uniformly chosen mandatory row. -/
def mandatoryParameter (L : ℕ) (p : ℝ) : ℝ :=
  (p - 1 / (L : ℝ)) / (1 - 1 / (L : ℝ))

theorem mandatoryParameter_den_pos {L : ℕ} (hL : 1 < L) :
    0 < 1 - 1 / (L : ℝ) := by
  have hLreal : (1 : ℝ) < (L : ℝ) := by exact_mod_cast hL
  have hLpos : (0 : ℝ) < (L : ℝ) := lt_trans zero_lt_one hLreal
  exact sub_pos.mpr ((div_lt_one hLpos).mpr hLreal)

theorem mandatoryParameter_nonneg {L : ℕ} {p : ℝ}
    (hL : 1 < L) (hLp : 1 ≤ (L : ℝ) * p) :
    0 ≤ mandatoryParameter L p := by
  have hLreal : (1 : ℝ) < (L : ℝ) := by exact_mod_cast hL
  have hLpos : (0 : ℝ) < (L : ℝ) := lt_trans zero_lt_one hLreal
  have hbase : 1 / (L : ℝ) ≤ p :=
    (div_le_iff₀ hLpos).mpr (by simpa only [mul_comm] using hLp)
  exact div_nonneg (sub_nonneg.mpr hbase) (mandatoryParameter_den_pos hL).le

theorem mandatoryParameter_lt_one {L : ℕ} {p : ℝ}
    (hL : 1 < L) (hp : p < 1) : mandatoryParameter L p < 1 := by
  exact (div_lt_one (mandatoryParameter_den_pos hL)).mpr
    (sub_lt_sub_right hp (1 / (L : ℝ)))

theorem mandatoryParameter_marginal {L : ℕ} (hL : 1 < L) (p : ℝ) :
    1 / (L : ℝ) + (1 - 1 / (L : ℝ)) * mandatoryParameter L p = p := by
  unfold mandatoryParameter
  rw [mul_div_cancel₀ _ (mandatoryParameter_den_pos hL).ne']
  ring

theorem mandatoryParameter_boundary {L : ℕ} {p : ℝ}
    (hL : 1 < L) (hLp : (L : ℝ) * p = 1) : mandatoryParameter L p = 0 := by
  have hLreal : (1 : ℝ) < (L : ℝ) := by exact_mod_cast hL
  have hLpos : (0 : ℝ) < (L : ℝ) := lt_trans zero_lt_one hLreal
  have hpbase : p = 1 / (L : ℝ) :=
    (eq_div_iff hLpos.ne').mpr (by simpa only [mul_comm] using hLp)
  unfold mandatoryParameter
  rw [hpbase, sub_self, zero_div]

/-- A coordinate chooses one compulsory row, together with independent marks.
The mark in the compulsory row may be sampled and then ignored. -/
abbrev MandatoryColumn (L : ℕ) := Fin L × (Fin L → Bool)

def mandatoryBit {L : ℕ} (j : Fin L) (z : MandatoryColumn L) : Bool :=
  decide (z.1 = j ∨ z.2 j = true)

@[simp] theorem mandatoryBit_mandatory {L : ℕ} (z : MandatoryColumn L) :
    mandatoryBit z.1 z = true := by
  simp [mandatoryBit]

private theorem mandatory_prob_prod_or {Ω Γ : Type*} [Fintype Ω] [Fintype Γ]
    (μ : FiniteLaw Ω) (ν : FiniteLaw Γ) (P : Ω → Prop) (Q : Γ → Prop) :
    (μ.prod ν).prob (fun z => P z.1 ∨ Q z.2) =
      μ.prob P + (1 - μ.prob P) * ν.prob Q := by
  classical
  have h := (μ.prod ν).prob_compl (fun z => P z.1 ∨ Q z.2)
  simp only [not_or] at h
  rw [FiniteLaw.prob_prod μ ν (fun ω => ¬ P ω) (fun γ => ¬ Q γ),
    μ.prob_compl P, ν.prob_compl Q] at h
  nlinarith only [h]

/-- Uniform mandatory label, independent of all the extra row marks. -/
def mandatoryColumnLaw {L : ℕ} (hL : 1 < L) (p : ℝ) (hp : p < 1)
    (hLp : 1 ≤ (L : ℝ) * p) : FiniteLaw (MandatoryColumn L) := by
  let : Nonempty (Fin L) := ⟨⟨0, lt_trans Nat.zero_lt_one hL⟩⟩
  exact (FiniteLaw.uniform (Fin L)).prod
    (FiniteLaw.iid (bitLaw (mandatoryParameter L p)
      (mandatoryParameter_nonneg hL hLp) (mandatoryParameter_lt_one hL hp).le) L)

theorem mandatoryColumnLaw_marginal {L : ℕ} (hL : 1 < L) (p : ℝ)
    (hp : p < 1) (hLp : 1 ≤ (L : ℝ) * p) (j : Fin L) :
    (mandatoryColumnLaw hL p hp hLp).prob (fun z => mandatoryBit j z = true) = p := by
  classical
  let : Nonempty (Fin L) := ⟨⟨0, lt_trans Nat.zero_lt_one hL⟩⟩
  have hmandatory : (FiniteLaw.uniform (Fin L)).prob (fun k => k = j) =
      1 / (L : ℝ) := by
    rw [FiniteLaw.uniform_prob]
    simp only [Fintype.card_fin]
    congr 1
    norm_cast
    apply Finset.card_eq_one.mpr
    refine ⟨j, ?_⟩
    ext k
    simp
  have hmarks :
      (FiniteLaw.iid (bitLaw (mandatoryParameter L p)
        (mandatoryParameter_nonneg hL hLp) (mandatoryParameter_lt_one hL hp).le) L).prob
        (fun marks => marks j = true) = mandatoryParameter L p := by
    unfold FiniteLaw.iid
    rw [FiniteLaw.prob_pi_coordinate
      (fun _ : Fin L => bitLaw (mandatoryParameter L p)
        (mandatoryParameter_nonneg hL hLp) (mandatoryParameter_lt_one hL hp).le)
      j (fun b : Bool => b = true)]
    exact bitLaw_prob_true _ _ _
  unfold mandatoryColumnLaw
  simp only [mandatoryBit, decide_eq_true_eq]
  rw [mandatory_prob_prod_or (FiniteLaw.uniform (Fin L))
    (FiniteLaw.iid (bitLaw (mandatoryParameter L p)
      (mandatoryParameter_nonneg hL hLp) (mandatoryParameter_lt_one hL hp).le) L)
    (fun k : Fin L => k = j) (fun marks : Fin L → Bool => marks j = true),
    hmandatory, hmarks]
  exact mandatoryParameter_marginal hL p

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- Read the sets in all rows of a coordinate array. -/
def mandatoryRows {L : ℕ} (ω : α → MandatoryColumn L) (j : Fin L) : Finset α :=
  cubeSet (fun i => mandatoryBit j (ω i))

/-- The coordinate choices are independent; the rows need not be independent. -/
def mandatoryArrayLaw {L : ℕ} (hL : 1 < L) (p : ℝ) (hp : p < 1)
    (hLp : 1 ≤ (L : ℝ) * p) : FiniteLaw (α → MandatoryColumn L) :=
  FiniteLaw.pi (fun _ : α => mandatoryColumnLaw hL p hp hLp)

/-- Every atom of each row has its exact Bernoulli subset mass. -/
theorem mandatoryRows_prob_eq_mass {L : ℕ} (hL : 1 < L) (p : ℝ)
    (hp : p < 1) (hLp : 1 ≤ (L : ℝ) * p) (j : Fin L) (s : Finset α) :
    (mandatoryArrayLaw (α := α) hL p hp hLp).prob
      (fun ω => mandatoryRows ω j = s) = bernoulliMass p s := by
  exact prob_pi_cubeSet_eq_mass (fun _ : α => mandatoryColumnLaw hL p hp hLp)
    (fun _ => mandatoryBit j) p (fun _ => mandatoryColumnLaw_marginal hL p hp hLp j) s

/-- The row distribution agrees on arbitrary, potentially nonmonotone families. -/
theorem mandatoryRows_prob_mem_family {L : ℕ} (hL : 1 < L) (p : ℝ)
    (hp : p < 1) (hLp : 1 ≤ (L : ℝ) * p) (j : Fin L) (D : Family α) :
    (mandatoryArrayLaw (α := α) hL p hp hLp).prob
      (fun ω => mandatoryRows ω j ∈ D) = familyMeasure p D := by
  exact prob_pi_cubeSet_mem_family (fun _ : α => mandatoryColumnLaw hL p hp hLp)
    (fun _ => mandatoryBit j) p (fun _ => mandatoryColumnLaw_marginal hL p hp hLp j) D

/-- The selected mandatory row contains each coordinate in every outcome. -/
theorem mandatoryRows_union {L : ℕ} (ω : α → MandatoryColumn L) :
    unionTuple (mandatoryRows ω) = Finset.univ := by
  ext i
  simp only [Finset.mem_univ, iff_true]
  apply mem_unionTuple.mpr
  refine ⟨(ω i).1, ?_⟩
  exact mem_cubeSet.mpr (mandatoryBit_mandatory (ω i))

/-- Marginal success probabilities and the union bound give a covering tuple.
There is no independence assumption between the rows. -/
theorem exists_mandatory_cover {L : ℕ} (hL : 1 < L) (p : ℝ)
    (hp : p < 1) (hLp : 1 ≤ (L : ℝ) * p) (D : Family α)
    (hbudget : (L : ℝ) * (1 - familyMeasure p D) < 1) :
    ∃ rows : Fin L → Finset α,
      (∀ j, rows j ∈ D) ∧ unionTuple rows = Finset.univ := by
  have hmarginal (j : Fin L) :
      (mandatoryArrayLaw (α := α) hL p hp hLp).prob
        (fun ω => mandatoryRows ω j ∈ D) = familyMeasure p D :=
    mandatoryRows_prob_mem_family hL p hp hLp j D
  have hbudget' : (Fintype.card (Fin L) : ℝ) * (1 - familyMeasure p D) < 1 := by
    simpa only [Fintype.card_fin] using hbudget
  obtain ⟨ω, hω⟩ := FiniteLaw.exists_forall_of_const
    (mandatoryArrayLaw (α := α) hL p hp hLp)
    (fun j ω => mandatoryRows ω j ∈ D) (familyMeasure p D) hmarginal hbudget'
  exact ⟨mandatoryRows ω, hω, mandatoryRows_union ω⟩

end TalagrandDiscreteConvexity

end

end OAI
