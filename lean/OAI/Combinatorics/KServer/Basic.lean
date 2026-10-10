import Mathlib

namespace OAI

noncomputable section
open scoped BigOperators

namespace KServer

universe u

/-- Labeled configurations; no injectivity condition, so repetitions are allowed. -/
abbrev Configuration (k : ℕ) (X : Type u) := Fin k → X

/-- The finite probability simplex of the available server labels. -/
def LabelDistribution (k : ℕ) :=
  {p : Fin k → ℝ // (∀ i, 0  ≤  p i) ∧ ∑ i, p i = 1}

/-- A behavioral policy knows the entire past request/choice history and the new
request. It is a single rule for all horizons. Pairing the past requests and
choices is equivalent to the histories X^t × [k]^(t-1) in the manuscript. -/
abbrev Policy (k : ℕ) (X : Type u) :=
  List (X × Fin k) → X → LabelDistribution k

/-- Serve one request by moving exactly the indicated label to the request. -/
def serve {k : ℕ} {X : Type u} (s : Configuration k X) (i : Fin k) (r : X) :
    Configuration k X := Function.update s i r

/-- Deterministic movement of a label string on a fixed finite request sequence. -/
def serviceCost {k : ℕ} {X : Type u} [MetricSpace X] (s : Configuration k X) :
    (σ : List X) → (Fin σ.length → Fin k) → ℝ
  | [], _ => 0
  | r :: rs, j =>
      dist (s (j 0)) r + serviceCost (serve s (j 0) r) rs (fun i => j i.succ)

/-- Probability of a finite label string under the successive behavioral choices. -/
def pathProbability {k : ℕ} {X : Type u} (A : Policy k X)
    (h : List (X × Fin k)) : (σ : List X) → (Fin σ.length → Fin k) → ℝ
  | [], _ => 1
  | r :: rs, j =>
      (A h r).val (j 0) * pathProbability A (h ++ [(r, j 0)]) rs (fun i => j i.succ)

/-- Exact finite expected total movement against an oblivious input. -/
def expectedCost {k : ℕ} {X : Type u} [MetricSpace X]
    (A : Policy k X) (s : Configuration k X) (σ : List X) : ℝ :=
  ∑ j : Fin σ.length → Fin k, pathProbability A [] σ j * serviceCost s σ j

/-- Offline optimum over the finite set of all label strings. For k ≥ 2 this
range is nonempty and finite, hence its real infimum is the attained minimum.
There is no restriction on the metric itself. -/
def optimalCost {k : ℕ} {X : Type u} [MetricSpace X]
    (s : Configuration k X) (σ : List X) : ℝ :=
  sInf (Set.range (serviceCost s σ))

/-- Literal main objective, with arbitrary universes, arbitrary metric spaces,
repeated initial positions, and one policy and additive constant for all finite
inputs. Real constants are finite; an embedding witnesses at least k+1 points.
The final implication encodes availability of B=0 for distinct starts. -/
def ReductionStatement : Prop :=
  ∃ C : ℝ, ∀ (k : ℕ), 2  ≤  k →
    ∀ (X : Type u) (_ : MetricSpace X),
      (∃ e : Fin (k + 1) → X, Function.Injective e) →
      ∀ s : Configuration k X,
        ∃ A : Policy k X, ∃ B : ℝ,
          0  ≤  B ∧ (Function.Injective s → B = 0) ∧
          ∀ σ : List X,
            expectedCost A s σ  ≤  C * (Real.log (k + 1)) ^ 2 * optimalCost s σ + B


/- Finite behavioral experiments and product compactness. -/


instance (k : ℕ) : TopologicalSpace (LabelDistribution k) :=
  inferInstanceAs (TopologicalSpace
    {probability : Fin k → ℝ // (∀ label, 0 ≤ probability label) ∧ ∑ label, probability label = 1})

instance (k : ℕ) : CompactSpace (LabelDistribution k) := by
  apply isCompact_iff_compactSpace.mp
  apply IsCompact.of_isClosed_subset
    (isCompact_Icc : IsCompact (Set.Icc (0 : Fin k → ℝ) 1))
  · change IsClosed
      ({probability : Fin k → ℝ | ∀ label, 0 ≤ probability label} ∩
        {probability : Fin k → ℝ | ∑ label, probability label = 1})
    apply IsClosed.inter
    · simp only [Set.ofPred_forall]
      exact isClosed_iInter fun label => isClosed_le continuous_const (continuous_apply label)
    · exact isClosed_eq (by fun_prop) continuous_const
  · rintro probability ⟨nonnegative, total⟩
    refine ⟨nonnegative, ?_⟩
    intro label
    calc
      probability label ≤ ∑ other, probability other :=
        Finset.single_le_sum (fun other _ => nonnegative other) (Finset.mem_univ label)
      _ = 1 := total

/-- A pure choice, also used to fill unreachable decision histories. -/
def pureDistribution {k : ℕ} (i : Fin k) : LabelDistribution k :=
  ⟨fun j => if j = i then 1 else 0, by
    constructor
    · intro j; dsimp only; split_ifs <;> norm_num
    · simp⟩

instance (k : ℕ) [NeZero k] : Nonempty (LabelDistribution k) :=
  ⟨pureDistribution 0⟩

lemma serviceCost_nonneg {k : ℕ} {X : Type u} [MetricSpace X]
    (s : Configuration k X) (σ : List X) (j : Fin σ.length → Fin k) :
    0  ≤  serviceCost s σ j := by
  induction σ generalizing s with
  | nil => simp [serviceCost]
  | cons r rs ih => exact add_nonneg dist_nonneg (ih _ _)

lemma pathProbability_nonneg {k : ℕ} {X : Type u} (A : Policy k X)
    (h : List (X × Fin k)) (σ : List X) (j : Fin σ.length → Fin k) :
    0  ≤  pathProbability A h σ j := by
  induction σ generalizing h with
  | nil => simp [pathProbability]
  | cons r rs ih => exact mul_nonneg ((A h r).property.1 _) (ih _ _)

/-- Decompose a complete label string into its first decision and its tail. -/
lemma sum_labelStrings {k n : ℕ} (f : (Fin (n + 1) → Fin k) → ℝ) :
    ∑ j, f j = ∑ i : Fin k, ∑ js : Fin n → Fin k, f (Fin.cons i js) := by
  rw [← Fintype.sum_equiv (Fin.consEquiv (fun _ : Fin (n + 1) => Fin k))
    (fun p => f (Fin.cons p.1 p.2)) f (fun _ => rfl), Fintype.sum_prod_type]

lemma pathProbability_sum {k : ℕ} {X : Type u} (A : Policy k X)
    (h : List (X × Fin k)) (σ : List X) :
    ∑ j : Fin σ.length → Fin k, pathProbability A h σ j = 1 := by
  induction σ generalizing h with
  | nil => simp [pathProbability]
  | cons r rs ih =>
    change (∑ j : Fin (rs.length + 1) → Fin k, pathProbability A h (r :: rs) j) = 1
    rw [sum_labelStrings]
    simp only [pathProbability, Fin.cons_zero, Fin.cons_succ]
    simp_rw [← Finset.mul_sum, ih, mul_one]
    exact (A h r).property.2

lemma expectedCost_nonneg {k : ℕ} {X : Type u} [MetricSpace X]
    (A : Policy k X) (s : Configuration k X) (σ : List X) :
    0  ≤  expectedCost A s σ :=
  Finset.sum_nonneg fun _ _ => mul_nonneg (pathProbability_nonneg _ _ _ _)
    (serviceCost_nonneg _ _ _)

lemma continuous_pathProbability {k : ℕ} {X : Type u}
    (h : List (X × Fin k)) (σ : List X) (j : Fin σ.length → Fin k) :
    Continuous fun A : Policy k X => pathProbability A h σ j := by
  induction σ generalizing h with
  | nil => exact continuous_const
  | cons r rs ih =>
    change Continuous fun A : Policy k X =>
      (A h r).val (j 0) * pathProbability A (h ++ [(r, j 0)]) rs (fun i => j i.succ)
    apply Continuous.mul _ (ih _ _)
    exact (continuous_apply (j 0)).comp
      (continuous_subtype_val.comp ((continuous_apply r).comp (continuous_apply h)))

/-- Equation (cost-polynomial): a fixed finite input has continuous expected
cost on the full, possibly infinite, product of decision simplexes. -/
lemma continuous_expectedCost {k : ℕ} {X : Type u} [MetricSpace X]
    (s : Configuration k X) (σ : List X) :
    Continuous fun A : Policy k X => expectedCost A s σ := by
  exact continuous_finsetSum _ fun j _ =>
    (continuous_pathProbability [] σ j).mul continuous_const

/-- The topological step of Lemma `compact-policy`.  The finite feasibility
premise is the *remaining quantitative obligation*, not asserted here. This
lemma does not use finite/bounded/discrete assumptions on the request space. -/
theorem compact_policy_of_finite_feasibility {k : ℕ} {X : Type u} [MetricSpace X]
    (s : Configuration k X) (bound : List X → ℝ)
    (hfinite : ∀ F : Finset (List X), ∃ A : Policy k X,
      ∀ σ ∈ F, expectedCost A s σ  ≤  bound σ) :
    ∃ A : Policy k X, ∀ σ : List X, expectedCost A s σ  ≤  bound σ := by
  let constraints (σ : List X) : Set (Policy k X) :=
    {A | expectedCost A s σ  ≤  bound σ}
  have hclosed (σ : List X) : IsClosed (constraints σ) :=
    isClosed_le (continuous_expectedCost s σ) continuous_const
  have hfip (F : Finset (List X)) : (⋂ σ ∈ F, constraints σ).Nonempty := by
    obtain ⟨A, hA⟩ := hfinite F
    exact ⟨A, by simpa only [Set.mem_iInter, constraints, Set.mem_ofPred_eq] using hA⟩
  obtain ⟨A, hA⟩ := CompactSpace.iInter_nonempty hclosed hfip
  exact ⟨A, by simpa only [Set.mem_iInter, constraints, Set.mem_ofPred_eq] using hA⟩

/-! Section02's matching and strongly lazy simulation, including repeated
positions and arbitrary metric spaces. -/

def configurationAfter {k : ℕ} {X : Type u} (s : Configuration k X)
    (h : List (X × Fin k)) : Configuration k X :=
  h.foldl (fun c ri => serve c ri.2 ri.1) s

def StronglyLazy {k : ℕ} {X : Type u} (s : Configuration k X) (A : Policy k X) : Prop :=
  ∀ h r, (∃ i, configurationAfter s h i = r) →
    ∀ j, configurationAfter s h j ≠ r → (A h r).val j = 0

lemma configurationAfter_append {k : ℕ} {X : Type u} (s : Configuration k X)
    (h : List (X × Fin k)) (r : X) (i : Fin k) :
    configurationAfter s (h ++ [(r,i)]) = serve (configurationAfter s h) i r := by
  simp [configurationAfter, List.foldl_append]

end KServer
end

end OAI
