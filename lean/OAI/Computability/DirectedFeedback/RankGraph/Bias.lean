import Mathlib
import OAI.Computability.DirectedFeedback.RankGraph.Point

namespace OAI

section
noncomputable section
open scoped BigOperators
noncomputable section
open scoped Classical BigOperators
noncomputable section
open scoped Classical
noncomputable section
open scoped Classical
noncomputable section
open scoped Classical BigOperators
noncomputable section
open scoped BigOperators
noncomputable section
open scoped BigOperators
open DirectedFeedback.SourceProbability
noncomputable section
open scoped Classical BigOperators
noncomputable section
open scoped Classical BigOperators
noncomputable section
open scoped Classical BigOperators
noncomputable section
open scoped Classical BigOperators
noncomputable section
open scoped Classical BigOperators
noncomputable section
open scoped Classical BigOperators
noncomputable section
open scoped Classical BigOperators
noncomputable section
open scoped Classical BigOperators
namespace DirectedFeedback.Games
open DirectedFeedback.SourceProbability
open FiniteDistribution
variable {U V E X Y : Type} [Fintype U] [Fintype V] [Fintype E]
  [Fintype X] [Fintype Y] [Nonempty X] [Nonempty Y]

theorem listChoice_weight {S : Finset X} {x : X} (hx : x ∈ S) :
    (listChoice S).weight x = 1 / (S.card : ℝ) := by
  have h : S.Nonempty := ⟨x, hx⟩
  simp only [listChoice, dite_eq_left h, hx, ↓reduceIte]

theorem listChoice_pair_success (π : X → Y) (S : Finset X) (R : Finset Y)
    (J : ℕ) (hJ : 1 ≤ J) (hS : S.card ≤ J) (hR : R.card ≤ J)
    (hh : ∃ x ∈ S, π x ∈ R) :
    1 / (J : ℝ)^2 ≤ ((listChoice S).product (listChoice R)).probability
      (fun z => decide (π z.1 = z.2)) := by
  obtain ⟨x, hx, hpx⟩ := hh
  have hcS : (0 : ℝ) < S.card := by exact_mod_cast (Finset.card_pos.mpr ⟨x, hx⟩)
  have hcR : (0 : ℝ) < R.card := by exact_mod_cast (Finset.card_pos.mpr ⟨π x, hpx⟩)
  have hSJ : (S.card : ℝ) ≤ J := by exact_mod_cast hS
  have hRJ : (R.card : ℝ) ≤ J := by exact_mod_cast hR
  have hJpos : (0 : ℝ) < J := by exact_mod_cast (show 0 < J by omega)
  calc
    1 / (J : ℝ)^2 = (1 / (J : ℝ)) * (1 / (J : ℝ)) := by ring
    _ ≤ (1 / (S.card : ℝ)) * (1 / (R.card : ℝ)) :=
      mul_le_mul (one_div_le_one_div_of_le hcS hSJ) (one_div_le_one_div_of_le hcR hRJ)
        (by positivity) (by positivity)
    _ = ((listChoice S).product (listChoice R)).weight (x, π x) := by
      simp only [product, listChoice_weight hx, listChoice_weight hpx]
    _ ≤ _ := probability_ge_atom _ _ (x, π x) (by simp)

omit [Nonempty X] [Nonempty Y] in

theorem randomized_score (G : Game U V E X Y)
    (α : U → FiniteDistribution X) (β : V → FiniteDistribution Y) :
    ((table α).product (table β)).expectation (fun l => G.score l.1 l.2) =
      G.edgeLaw.expectation (fun e => ((α (G.left e)).product (β (G.right e))).probability
        (fun z => decide (G.project e z.1 = z.2))) := by
  simp only [Game.score, probability_eq_expect, expectation_product]
  rw [show (table α).expectation (fun x => (table β).expectation
      (fun y => G.edgeLaw.expectation (fun e =>
        if decide (G.project e (x (G.left e)) = y (G.right e)) then 1 else 0))) =
      G.edgeLaw.expectation (fun e => (table α).expectation (fun x =>
        (table β).expectation (fun y =>
          if decide (G.project e (x (G.left e)) = y (G.right e)) then 1 else 0))) from by
      simp_rw [expectation_comm (table β) G.edgeLaw]
      exact expectation_comm (table α) G.edgeLaw _]
  apply expectation_congr
  intro e
  exact expectation_table_pair α β (G.left e) (G.right e)
    (fun x y => if decide (G.project e x = y) then 1 else 0)

theorem list_decoding (G : Game U V E X Y) (θ : ℝ) (hsound : G.Sound θ)
    (Ju : U → Finset X) (Jv : V → Finset Y) (J : ℕ) (hJ : 1 ≤ J)
    (hu : ∀ u, (Ju u).card ≤ J) (hv : ∀ v, (Jv v).card ≤ J) :
    G.edgeLaw.probability (fun e => decide (∃ x ∈ Ju (G.left e), G.project e x ∈ Jv (G.right e)))
      ≤ θ * (J : ℝ)^2 := by
  let α : U → FiniteDistribution X := fun u => listChoice (Ju u)
  let β : V → FiniteDistribution Y := fun v => listChoice (Jv v)
  have hscore : G.edgeLaw.expectation (fun e => ((α (G.left e)).product (β (G.right e))).probability
        (fun z => decide (G.project e z.1 = z.2))) ≤ θ := by
    rw [← randomized_score G α β]
    calc
      _ ≤ ((table α).product (table β)).expectation (fun _ => θ) :=
        expectation_mono _ (fun l => hsound l.1 l.2)
      _ = _ := expectation_const _ _
  have hJpos : (0 : ℝ) < J := by exact_mod_cast (show 0 < J by omega)
  rw [probability_eq_expect]
  calc
    _ ≤ G.edgeLaw.expectation (fun e => (J : ℝ)^2 *
      ((α (G.left e)).product (β (G.right e))).probability
        (fun z => decide (G.project e z.1 = z.2))) := by
      apply expectation_mono
      intro e
      by_cases hh : ∃ x ∈ Ju (G.left e), G.project e x ∈ Jv (G.right e)
      · simp only [hh, decide_true, ↓reduceIte]
        have h := listChoice_pair_success (G.project e) (Ju (G.left e)) (Jv (G.right e))
          J hJ (hu _) (hv _) hh
        exact (div_le_iff₀ (sq_pos_of_pos hJpos)).mp h |>.trans_eq (mul_comm _ _)
      · simp only [hh, decide_false, Bool.false_eq_true, ↓reduceIte]
        exact mul_nonneg (sq_nonneg _) (probability_nonnegative _ _)
    _ = (J : ℝ)^2 * G.edgeLaw.expectation (fun e =>
      ((α (G.left e)).product (β (G.right e))).probability
        (fun z => decide (G.project e z.1 = z.2))) := expectation_mul_left _ _ _
    _ ≤ _ := by nlinarith [mul_le_mul_of_nonneg_left hscore (sq_nonneg (J : ℝ))]

end DirectedFeedback.Games

noncomputable section
open scoped Classical BigOperators
namespace DirectedFeedback.Construction
open DirectedFeedback.SourceProbability FiniteDistribution
open RankGraph Prefix PrefixExperiment Games
variable {U V E X Y : Type} [Fintype U] [Fintype V] [Fintype E]
  [Fintype X] [Fintype Y] [Nonempty X] [Nonempty Y]
variable {M T N : ℕ} [NeZero M] [NeZero T]

def bias (i : Fin M) : ℝ := (2:ℝ)⁻¹ ^ (i.val+2)

omit [NeZero M] in
theorem bias_pos (i : Fin M) : 0 < bias i := by unfold bias; positivity

omit [NeZero M] in
theorem bias_le_quarter (i : Fin M) : bias i ≤ 1/4 := by
  unfold bias
  rw [pow_add]
  have h : (2:ℝ)⁻¹ ^ i.val ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  norm_num at *
  linarith

def subsetLaw (i : Fin M) : FiniteDistribution (X → Bool) :=
  Pivotal.law (bias i) (bias_pos i).le (by linarith [bias_le_quarter i])

abbrev Slot (U X : Type) (M : ℕ) := Atom U (Fin M) (X → Bool)
abbrev PrefixData (U X : Type) (M t : ℕ) := Fin t → Slot U X M

def sets {t : ℕ} (a : PrefixData U X M t) (j : ℕ) : Set X :=
  if h : j < t then {x | (a ⟨j,h⟩).2.2 x = true} else ∅

def cell {t : ℕ} (a : PrefixData U X M t) : (Fin t → X) → Fin (cellCount t) :=
  prefixCell t (sets a)

def vertices {t : ℕ} (a : PrefixData U X M t) : Fin t → U := fun j => (a j).1

abbrev Emb (L N : ℕ) := {ψ : Fin L → Fin N // StrictMono ψ}
def maxCells (X : Type) [Fintype X] (T : ℕ) := cellCount T * Fintype.card X
def rankLength (X : Type) [Fintype X] (T : ℕ) := 10 * maxCells X T + 30

abbrev Common (U X : Type) [Fintype X] (M T N : ℕ) :=
  Emb (rankLength X T) N × (Σ t : Fin T, PrefixData U X M t.val)
abbrev Full (U X : Type) [Fintype X] (M T N : ℕ) :=
  Emb (rankLength X T) N × PrefixData U X M T
abbrev Big (U X : Type) [Fintype X] (M T N : ℕ) :=
  Common U X M T N × (U × Pivotal.LabelOrder X)
abbrev Small (U V X Y : Type) [Fintype X] [Fintype Y] (M T N : ℕ) :=
  Common U X M T N × (V × Pivotal.LabelOrder Y)
abbrev Compare (U E X Y : Type) [Fintype X] (M T N : ℕ) :=
  Σ d : Common U X M T N, E × (Σ _ : Fin M, Fin (cellCount d.2.1.val) × (Y → Coupling.Block))

abbrev Wild (U V X Y : Type) [Fintype X] [Fintype Y]
    (M T N : ℕ) := Full U X M T N ⊕ (Big U X M T N ⊕ Small U V X Y M T N)

def bigMarginal (G : Game U V E X Y) := G.edgeLaw.pushforward G.left
def smallMarginal (G : Game U V E X Y) := G.edgeLaw.pushforward G.right

def common (G : Game U V E X Y) (ψLaw : FiniteDistribution (Emb (rankLength X T) N)) :
    FiniteDistribution (Common U X M T N) := commonLaw ψLaw (bigMarginal G) subsetLaw T

def fullLaw (G : Game U V E X Y) (ψLaw : FiniteDistribution (Emb (rankLength X T) N)) :
    FiniteDistribution (Full U X M T N) := ψLaw.product ((atomLaw (bigMarginal G) subsetLaw).iid T)

def bigLaw (G : Game U V E X Y) (ψLaw : FiniteDistribution (Emb (rankLength X T) N)) :
    FiniteDistribution (Big U X M T N) := (common G ψLaw).product
      ((bigMarginal G).product Pivotal.labelOrderLaw)

def smallLaw (G : Game U V E X Y) (ψLaw : FiniteDistribution (Emb (rankLength X T) N)) :
    FiniteDistribution (Small U V X Y M T N) := (common G ψLaw).product
      ((smallMarginal G).product Pivotal.labelOrderLaw)

instance cellCountNeZero (t : ℕ) : NeZero (cellCount t) :=
  ⟨by rw [cellCount_eq]; positivity⟩

def comparisonLaw (G : Game U V E X Y)
    (ψLaw : FiniteDistribution (Emb (rankLength X T) N)) :
    FiniteDistribution (Compare U E X Y M T N) :=
  (common G ψLaw).sigma (fun d => G.edgeLaw.product ((uniform (Fin M)).sigma (fun i =>
    (uniform (Fin (cellCount d.2.1.val))).product
      (Coupling.law (bias i) (bias_pos i).le (by linarith [bias_le_quarter i])))))

theorem cellCount_mono {s t : ℕ} (h : s ≤ t) : cellCount s ≤ cellCount t := by
  simp only [cellCount_eq]
  exact Nat.pow_le_pow_right (by decide) h

omit [NeZero T] in
theorem full_cells_bound : cellCount T ≤ maxCells X T := by
  have h : 1 ≤ Fintype.card X := Fintype.card_pos
  simpa [maxCells] using Nat.mul_le_mul_left (cellCount T) h

omit [Nonempty X] [NeZero T] in
theorem ordered_cells_bound {I : Type} [Fintype I] [DecidableEq I]
    (hI : Fintype.card I ≤ Fintype.card X) (t : Fin T) (o : Pivotal.LabelOrder I) :
    cellCount t.val * (Fintype.card {i : I // i ≠ o.1} + 1) ≤ maxCells X T := by
  have he : Fintype.card I = Fintype.card {i : I // i ≠ o.1} + 1 := by
    simpa using Fintype.card_congr o.2
  rw [← he]
  exact Nat.mul_le_mul (cellCount_mono (Nat.le_of_lt t.isLt)) hI

def level (ψ : Emb (rankLength X T) N) {k : ℕ} (hk : k ≤ maxCells X T) (j : Fin k) : Fin N :=
  ψ.val ⟨10*j.val+19, by have := j.isLt; unfold rankLength; omega⟩

def fullCount (a : PrefixData U X M T) (i : Fin M) (x : Fin T → X) : ℕ :=
  (Finset.univ.filter (fun j => (a j).2.1 = i ∧ (a j).2.2 (x j) = true)).card

def fullStars (a : PrefixData U X M T) : Set (Fin T → X) :=
  {x | ∃ i : Fin M, (fullCount a i x : ℝ) < bias i * T / (2*M)}

def fullWildcard (d : Full U X M T N) :
    TestGraph.Wildcard (U := U) (V := V) (X := X) (Y := Y) (T := T) (N := N) where
  tuple := .inl ⟨⟨T, by omega⟩, vertices d.2⟩
  cells := cellCount T
  cell := cell d.2
  stars := fullStars d.2
  level := level d.1 full_cells_bound

def bigWildcard (d : Big U X M T N) :
    TestGraph.Wildcard (U := U) (V := V) (X := X) (Y := Y) (T := T) (N := N) where
  tuple := .inl ⟨⟨d.1.2.1.val+1, by have := d.1.2.1.isLt; omega⟩,
    Fin.snoc (vertices d.1.2.2) d.2.1⟩
  cells := cellCount d.1.2.1.val * (Fintype.card {x : X // x ≠ d.2.2.1}+1)
  cell := fun a => orderedCell (cell d.1.2.2) d.2.2.2 (splitLast d.1.2.1.val a)
  stars := {a | a (Fin.last d.1.2.1.val) = d.2.2.1}
  level := level d.1.1 (ordered_cells_bound le_rfl d.1.2.1 d.2.2)

def smallWildcard (hYX : Fintype.card Y ≤ Fintype.card X) (d : Small U V X Y M T N) :
    TestGraph.Wildcard (U := U) (V := V) (X := X) (Y := Y) (T := T) (N := N) where
  tuple := .inr ⟨d.1.2.1, vertices d.1.2.2, d.2.1⟩
  cells := cellCount d.1.2.1.val * (Fintype.card {y : Y // y ≠ d.2.2.1}+1)
  cell := orderedCell (cell d.1.2.2) d.2.2.2
  stars := {a | a.2 = d.2.2.1}
  level := level d.1.1 (ordered_cells_bound hYX d.1.2.1 d.2.2)

def wildcard (hYX : Fintype.card Y ≤ Fintype.card X) : Wild U V X Y M T N →
    TestGraph.Wildcard (U := U) (V := V) (X := X) (Y := Y) (T := T) (N := N)
  | .inl d => fullWildcard d
  | .inr (.inl d) => bigWildcard d
  | .inr (.inr d) => smallWildcard hYX d

def comparison (G : Game U V E X Y) (fiber : E → X ≃ Y × Bool)
    (d : Compare U E X Y M T N) :
    TestGraph.Comparison (U := U) (V := V) (X := X) (Y := Y) (T := T) (N := N) :=
  let t := d.1.2.1
  let a := d.1.2.2
  let e := d.2.1
  let r := d.2.2.2.1
  let z := d.2.2.2.2
  { source := twoLevel d.1.1.val (.inr ⟨t, vertices a, G.right e⟩)
      (conditionedSet (cell a) r {y | Coupling.smallBits z y = true})
      ⟨1, by unfold rankLength; omega⟩ ⟨16, by unfold rankLength; omega⟩
    target := twoLevel d.1.1.val
      (.inl ⟨⟨t.val+1, by have := t.isLt; omega⟩, Fin.snoc (vertices a) (G.left e)⟩)
      (splitLast t.val ⁻¹' conditionedSet (cell a) r {x | Coupling.bigBits (fiber e) z x = true})
      ⟨2, by unfold rankLength; omega⟩ ⟨17, by unfold rankLength; omega⟩ }

end DirectedFeedback.Construction

noncomputable section
open scoped Classical BigOperators
namespace DirectedFeedback.SourceProbability.FiniteDistribution
variable {Ω : Type*} [Fintype Ω]

abbrev Support (μ : FiniteDistribution Ω) := {x : Ω // 0 < μ.weight x}

theorem sum_support (μ : FiniteDistribution Ω) (f : Ω → ℝ) :
    (∑ x : μ.Support, μ.weight x.val * f x.val) = ∑ x, μ.weight x * f x := by
  rw [← Finset.sum_subtype (Finset.univ.filter (fun x => 0 < μ.weight x)) (by simp) (fun x => μ.weight x * f x)]
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro x _
  by_cases h : 0 < μ.weight x
  · simp [h]
  · have hz : μ.weight x = 0 := le_antisymm (not_lt.mp h) (μ.nonnegative x)
    simp [hz]

def supported (μ : FiniteDistribution Ω) : FiniteDistribution μ.Support where
  weight x := μ.weight x.val
  nonnegative x := μ.nonnegative x.val
  normalized := by simpa using sum_support μ (fun _ => 1) |>.trans (by simpa using μ.normalized)

@[simp] theorem expectation_supported (μ : FiniteDistribution Ω) (f : Ω → ℝ) :
    μ.supported.expectation (fun x => f x.val) = μ.expectation f := sum_support μ f

@[simp] theorem probability_supported (μ : FiniteDistribution Ω) (f : Ω → Bool) :
    μ.supported.probability (fun x => f x.val) = μ.probability f := by
  simp only [probability_eq_expect]
  exact expectation_supported μ (fun x => if f x then 1 else 0)

def extend (μ : FiniteDistribution Ω) (f : μ.Support → Bool) (x : Ω) : Bool :=
  if h : 0 < μ.weight x then f ⟨x,h⟩ else false

@[simp] theorem extend_at_support (μ : FiniteDistribution Ω) (f : μ.Support → Bool)
    (x : μ.Support) : μ.extend f x.val = f x := by simp [extend,x.property]

theorem probability_extend (μ : FiniteDistribution Ω) (f : μ.Support → Bool) :
    μ.probability (μ.extend f) = μ.supported.probability f := by
  rw [← probability_supported]
  simp only [extend_at_support]

theorem support_nonempty (μ : FiniteDistribution Ω) : Nonempty μ.Support := by
  by_contra h
  have hz : ∀ x, μ.weight x = 0 := by
    intro x
    exact le_antisymm (not_lt.mp (fun hx => h ⟨⟨x,hx⟩⟩)) (μ.nonnegative x)
  have := μ.normalized
  simp [hz] at this

end DirectedFeedback.SourceProbability.FiniteDistribution

noncomputable section
open scoped Classical BigOperators
namespace DirectedFeedback.Construction
open DirectedFeedback.SourceProbability FiniteDistribution
open RankGraph Prefix PrefixExperiment Games
variable {U V E X Y : Type} [Fintype U] [Fintype V] [Fintype E]
  [Fintype X] [Fintype Y] [Nonempty X] [Nonempty Y]
variable {M T N : ℕ} [NeZero M] [NeZero T]
omit [NeZero M] [NeZero T] in
instance rankFintype : Fintype (Rank U V X Y T N) := Fintype.ofFinite _

variable (G : Game U V E X Y) (ψLaw : FiniteDistribution (Emb (rankLength X T) N))

abbrev WildSupport := (fullLaw (M := M) G ψLaw).Support ⊕
  ((bigLaw (M := M) G ψLaw).Support ⊕ (smallLaw (M := M) G ψLaw).Support)
abbrev ComparisonSupport := (comparisonLaw (M := M) G ψLaw).Support
abbrev OutputVertex := TestGraph.Vertex U V X Y
  (WildSupport (M := M) G ψLaw) (ComparisonSupport (M := M) G ψLaw) T N

def forgetWild : WildSupport (M := M) G ψLaw → Wild U V X Y M T N
  | .inl d => .inl d.val
  | .inr (.inl d) => .inr (.inl d.val)
  | .inr (.inr d) => .inr (.inr d.val)

def wildSupport (hYX : Fintype.card Y ≤ Fintype.card X) (w : WildSupport (M := M) G ψLaw) :=
  wildcard hYX (forgetWild G ψLaw w)

def compSupport (fiber : E → X ≃ Y × Bool) (c : ComparisonSupport (M := M) G ψLaw) :=
  comparison G fiber c.val

def OutputArc (hYX : Fintype.card Y ≤ Fintype.card X) (fiber : E → X ≃ Y × Bool) :=
  TestGraph.Arc (wildSupport (M := M) G ψLaw hYX) (compSupport (M := M) G ψLaw fiber)

theorem output_loopless (hYX : Fintype.card Y ≤ Fintype.card X) (fiber : E → X ≃ Y × Bool)
    (v : OutputVertex (M := M) G ψLaw) : ¬OutputArc G ψLaw hYX fiber v v :=
  TestGraph.arc_irrefl _ _ v

def vertexCost (D H K : ℝ) : OutputVertex (M := M) G ψLaw → ℝ
  | .inl _ => D+1
  | .inr (.inl (.inl d)) => H * (fullLaw G ψLaw).weight d.val
  | .inr (.inl (.inr (.inl d))) => Fintype.card X * (bigLaw G ψLaw).weight d.val
  | .inr (.inl (.inr (.inr d))) => Fintype.card Y * (smallLaw G ψLaw).weight d.val
  | .inr (.inr d) => K * (comparisonLaw G ψLaw).weight d.val

theorem vertexCost_pos (D H K : ℝ) (hD : 0 ≤ D) (hH : 0 < H) (hK : 0 < K)
    (v : OutputVertex (M := M) G ψLaw) : 0 < vertexCost G ψLaw D H K v := by
  rcases v with r | (d | d)
  · dsimp [vertexCost]; linarith
  · rcases d with d | (d | d)
    · exact mul_pos hH d.property
    · exact mul_pos (by exact_mod_cast Fintype.card_pos) d.property
    · exact mul_pos (by exact_mod_cast Fintype.card_pos) d.property
  · exact mul_pos hK d.property

instance fullSupportFintype : Fintype ((fullLaw (M := M) G ψLaw).Support) := inferInstance
instance bigSupportFintype : Fintype ((bigLaw (M := M) G ψLaw).Support) := inferInstance
instance smallSupportFintype : Fintype ((smallLaw (M := M) G ψLaw).Support) := inferInstance
instance comparisonSupportFintype : Fintype ((comparisonLaw (M := M) G ψLaw).Support) := inferInstance

instance outputFintype : Fintype (OutputVertex (M := M) G ψLaw) := by
  unfold OutputVertex TestGraph.Vertex WildSupport ComparisonSupport
  infer_instance

def totalDeletionCost (D H K : ℝ) (deleted : OutputVertex (M := M) G ψLaw → Bool) : ℝ :=
  ∑ v, if deleted v then vertexCost G ψLaw D H K v else 0

def fullDeleted (deleted : OutputVertex (M := M) G ψLaw → Bool) : Full U X M T N → Bool :=
  (fullLaw G ψLaw).extend (fun d => deleted (.inr (.inl (.inl d))))
def bigDeleted (deleted : OutputVertex (M := M) G ψLaw → Bool) : Big U X M T N → Bool :=
  (bigLaw G ψLaw).extend (fun d => deleted (.inr (.inl (.inr (.inl d)))))
def smallDeleted (deleted : OutputVertex (M := M) G ψLaw → Bool) : Small U V X Y M T N → Bool :=
  (smallLaw G ψLaw).extend (fun d => deleted (.inr (.inl (.inr (.inr d)))))
def comparisonDeleted (deleted : OutputVertex (M := M) G ψLaw → Bool) : Compare U E X Y M T N → Bool :=
  (comparisonLaw G ψLaw).extend (fun d => deleted (.inr (.inr d)))

theorem deletionCost_decomposition (D H K : ℝ) (deleted : OutputVertex (M := M) G ψLaw → Bool) :
    totalDeletionCost G ψLaw D H K deleted =
      (∑ r : Rank U V X Y T N, if deleted (.inl r) then D+1 else 0) +
      (H * (fullLaw G ψLaw).probability (fullDeleted G ψLaw deleted) +
      (Fintype.card X * (bigLaw G ψLaw).probability (bigDeleted G ψLaw deleted) +
       Fintype.card Y * (smallLaw G ψLaw).probability (smallDeleted G ψLaw deleted))) +
      K * (comparisonLaw G ψLaw).probability (comparisonDeleted G ψLaw deleted) := by
  unfold totalDeletionCost
  rw [Fintype.sum_sum_type, Fintype.sum_sum_type, Fintype.sum_sum_type, Fintype.sum_sum_type]
  change _ = _ + (H * (fullLaw G ψLaw).probability ((fullLaw G ψLaw).extend _) +
    ((Fintype.card X : ℝ) * (bigLaw G ψLaw).probability ((bigLaw G ψLaw).extend _) +
    (Fintype.card Y : ℝ) * (smallLaw G ψLaw).probability ((smallLaw G ψLaw).extend _))) +
    K * (comparisonLaw G ψLaw).probability ((comparisonLaw G ψLaw).extend _)
  rw [probability_extend, probability_extend, probability_extend, probability_extend]
  simp only [probability, vertexCost, supported, Finset.mul_sum, mul_ite, mul_zero]
  ring

theorem rank_retained (D H K : ℝ) (hD : 0 ≤ D) (hH : 0 < H) (hK : 0 < K)
    (deleted : OutputVertex (M := M) G ψLaw → Bool)
    (hcost : totalDeletionCost G ψLaw D H K deleted ≤ D) (r : Rank U V X Y T N) :
    deleted (.inl r) = false := by
  by_contra h
  have ht : deleted (.inl r) = true := Bool.eq_true_of_not_eq_false h
  have hh := Finset.single_le_sum (fun v (_ : v ∈ (Finset.univ : Finset (OutputVertex (M := M) G ψLaw))) =>
    show (0:ℝ) ≤ (if deleted v then vertexCost G ψLaw D H K v else 0) from
      by split <;> [exact (vertexCost_pos G ψLaw D H K hD hH hK v).le; rfl])
    (Finset.mem_univ (Sum.inl r))
  change (if deleted (.inl r) then D+1 else 0) ≤ totalDeletionCost G ψLaw D H K deleted at hh
  rw [ht] at hh
  simp only [↓reduceIte] at hh
  linarith

end DirectedFeedback.Construction

noncomputable section
open scoped Classical
namespace DirectedFeedback.Prefix
variable {S X : Type*} {k : ℕ}

def normalizedCondition (g : Set S → Bool) (cell : S → Fin k)
    (h0 : g ∅ = false) (h1 : g Set.univ = true)
    (g' : Set (S × X) → Bool) (good : Prop) (fallback : X) (R : Set X) : Bool :=
  if good then g' (conditionedSet cell (transition g cell h0 h1) R)
  else decide (fallback ∈ R)

theorem normalized_eq (g : Set S → Bool) (cell : S → Fin k)
    (h0 : g ∅ = false) (h1 : g Set.univ = true)
    (g' : Set (S × X) → Bool) (good : Prop) (fallback : X) (hg : good) :
    normalizedCondition g cell h0 h1 g' good fallback =
      fun R => g' (conditionedSet cell (transition g cell h0 h1) R) := by
  funext R; simp [normalizedCondition, hg]

theorem normalized_properties (g : Set S → Bool) (cell : S → Fin k)
    (h0 : g ∅ = false) (h1 : g Set.univ = true)
    (g' : Set (S × X) → Bool) (good : Prop) (fallback : X)
    (hg' : good → Monotone g')
    (hlift : ∀ E, g' (Prod.fst ⁻¹' E) = g E) :
    Monotone (normalizedCondition g cell h0 h1 g' good fallback) ∧
    normalizedCondition g cell h0 h1 g' good fallback ∅ = false ∧
    normalizedCondition g cell h0 h1 g' good fallback Set.univ = true := by
  by_cases hg : good
  · rw [normalized_eq g cell h0 h1 g' good fallback hg]
    exact conditioned_properties g g' (hg' hg) cell _ (transition_spec g cell h0 h1) hlift
  · have he : normalizedCondition g cell h0 h1 g' good fallback =
        (fun R => decide (fallback ∈ R)) := by
      funext R; simp [normalizedCondition, hg]
    rw [he]
    refine ⟨?_, by simp, by simp⟩
    intro A B hAB
    rw [Bool.le_iff_imp]
    simpa using (fun h : fallback ∈ A => hAB h)

end DirectedFeedback.Prefix

namespace DirectedFeedback.RankGraph
open Prefix
variable {U V X Y : Type} {T N L k : ℕ}
variable (ord : Rank U V X Y T N → ℕ) (ψ : Fin L → Fin N)
variable (hL : 30 ≤ L) (hψ : StrictMono ψ)
variable (hord : ∀ {a b}, Arc a b → ord a < ord b)

def conditionedSmall (t : Fin T) (s : Fin t.val → U) (cell : (Fin t.val → X) → Fin k)
    (v : V) (fallback : Y) : Set Y → Bool :=
  normalizedCondition (referenceBit ord ψ hL (.inl ⟨⟨t.val, by omega⟩, s⟩)) cell
    (reference_empty hL hψ hord _) (reference_univ hL hψ hord _)
    (referenceBit ord ψ hL (.inr ⟨t, s, v⟩))
    (Good ord ψ hL (.inr ⟨t, s, v⟩)) fallback

theorem conditionedSmall_properties (t : Fin T) (s : Fin t.val → U)
    (cell : (Fin t.val → X) → Fin k) (v : V) (fallback : Y) :
    Monotone (conditionedSmall ord ψ hL hψ hord t s cell v fallback) ∧
      conditionedSmall ord ψ hL hψ hord t s cell v fallback ∅ = false ∧
      conditionedSmall ord ψ hL hψ hord t s cell v fallback Set.univ = true := by
  apply normalized_properties
  · exact good_monotone hL hψ hord _
  · intro E
    unfold referenceBit
    exact (compare_prefix_small (ord := ord) (ψ := ψ) t s v E _ _ _).symm

def bigStepBit (t : Fin T) (s : Fin t.val → U) (u : U)
    (E : Set ((Fin t.val → X) × X)) : Bool :=
  referenceBit ord ψ hL (.inl ⟨⟨t.val+1, by omega⟩, Fin.snoc s u⟩)
    (splitLast t.val ⁻¹' E)

theorem bigStepBit_lift (t : Fin T) (s : Fin t.val → U) (u : U)
    (E : Set (Fin t.val → X)) :
    bigStepBit ord ψ hL t s u (Prod.fst ⁻¹' E) =
      referenceBit ord ψ hL (.inl ⟨⟨t.val, by omega⟩, s⟩) E := by
  unfold bigStepBit referenceBit
  change compareBit ord ψ (.inl ⟨⟨t.val+1, by omega⟩, Fin.snoc s u⟩)
      (Fin.init ⁻¹' E) _ _ _ = _
  have hi := @Fin.init_snoc t.val (fun _ => U) u s
  have hh := compare_prefix_big (X := X) (Y := Y) (ord := ord) (ψ := ψ)
    t.val t.isLt (Fin.snoc s u) E ⟨1, by omega⟩ ⟨14, by omega⟩ ⟨L-2, by omega⟩
  rw [hi] at hh
  exact hh.symm

def conditionedBig (t : Fin T) (s : Fin t.val → U) (cell : (Fin t.val → X) → Fin k)
    (u : U) (fallback : X) : Set X → Bool :=
  normalizedCondition (referenceBit ord ψ hL (.inl ⟨⟨t.val, by omega⟩, s⟩)) cell
    (reference_empty hL hψ hord _) (reference_univ hL hψ hord _)
    (bigStepBit ord ψ hL t s u)
    (Good ord ψ hL (.inl ⟨⟨t.val+1, by omega⟩, Fin.snoc s u⟩)) fallback

theorem conditionedBig_properties (t : Fin T) (s : Fin t.val → U)
    (cell : (Fin t.val → X) → Fin k) (u : U) (fallback : X) :
    Monotone (conditionedBig ord ψ hL hψ hord t s cell u fallback) ∧
      conditionedBig ord ψ hL hψ hord t s cell u fallback ∅ = false ∧
      conditionedBig ord ψ hL hψ hord t s cell u fallback Set.univ = true := by
  apply normalized_properties
  · intro hg E E' hEE'
    apply good_monotone hL hψ hord _ hg
    exact Set.preimage_mono hEE'
  · exact bigStepBit_lift ord ψ hL t s u

end DirectedFeedback.RankGraph

noncomputable section
open scoped Classical BigOperators
namespace DirectedFeedback.Prefix
variable {S : Type*} {k : ℕ}

theorem starred_transition_crosses (g : Set S → Bool) (hg : Monotone g)
    (cell : S → Fin k) (r : Fin k) (hr : Transition g cell r) (Z : Set S)
    (hz : ∀ a, cell a = r → a ∈ Z) :
    g (boundary cell r.val \ Z) = false ∧
      g ((boundary cell r.val \ Z) ∪ Z) = true := by
  constructor
  · have h := hg (Set.sdiff_subset : boundary cell r.val \ Z ⊆ boundary cell r.val)
    rw [hr.1] at h
    exact le_antisymm h (by simp)
  · have hsub : boundary cell (r.val+1) ⊆ (boundary cell r.val \ Z) ∪ Z := by
      intro a ha
      by_cases haz : a ∈ Z
      · exact Or.inr haz
      · left
        refine ⟨?_, haz⟩
        have hn : cell a ≠ r := fun he => haz (hz a he)
        have hnv : (cell a).val ≠ r.val := fun he => hn (Fin.ext he)
        change (cell a).val < r.val + 1 at ha
        change (cell a).val < r.val
        omega
    have h := hg hsub
    rw [hr.2] at h
    exact le_antisymm (by simp) h

theorem unstarred_transition_exists (g : Set S → Bool) (hg : Monotone g)
    (cell : S → Fin k) (r : Fin k) (hr : Transition g cell r) (Z : Set S)
    (hn : ¬(g (boundary cell r.val \ Z) = false ∧
      g ((boundary cell r.val \ Z) ∪ Z) = true)) :
    ∃ a, cell a = r ∧ a ∉ Z := by
  by_contra hh
  apply hn
  apply starred_transition_crosses g hg cell r hr Z
  intro a ha
  by_contra hz
  exact hh ⟨a, ha, hz⟩

end DirectedFeedback.Prefix

noncomputable section
open scoped Classical BigOperators
namespace DirectedFeedback.Construction
open DirectedFeedback.SourceProbability FiniteDistribution
open RankGraph Prefix PrefixExperiment Games
variable {U V E X Y : Type} [Fintype U] [Fintype V] [Fintype E]
  [Fintype X] [Fintype Y] [Nonempty X] [Nonempty Y]
variable {M T N : ℕ} [NeZero M] [NeZero T]
variable (G : Game U V E X Y) (ψLaw : FiniteDistribution (Emb (rankLength X T) N))
variable (hYX : Fintype.card Y ≤ Fintype.card X) (fiber : E → X ≃ Y × Bool)
variable (deleted : OutputVertex (M := M) G ψLaw → Bool)
variable (ord : OutputVertex (M := M) G ψLaw → ℕ)
variable (hord : ∀ {a b}, deleted a = false → deleted b = false →
  OutputArc G ψLaw hYX fiber a b → ord a < ord b)
variable (hrank : ∀ r, deleted (.inl r) = false)

abbrev rankOrder : Rank U V X Y T N → ℕ := fun r => ord (.inl r)

include hord hrank in
theorem rankOrder_arc {a b : Rank U V X Y T N} (h : RankGraph.Arc a b) :
    rankOrder G ψLaw ord a < rankOrder G ψLaw ord b :=
  hord (hrank a) (hrank b) (.rank h)

omit [NeZero M] [NeZero T] [Nonempty X] in
theorem rankLength_ge : 30 ≤ rankLength X T := by unfold rankLength; omega

theorem full_unstarred (d : (fullLaw (M := M) G ψLaw).Support)
    (hkeep : deleted (.inr (.inl (.inl d))) = false)
    (hgood : Good (rankOrder G ψLaw ord) d.val.1.val rankLength_ge (fullWildcard (V := V) (Y := Y) d.val).tuple) :
    ∃ x : Fin T → X,
      cell d.val.2 x = transition
        (referenceBit (rankOrder G ψLaw ord) d.val.1.val rankLength_ge (fullWildcard (V := V) (Y := Y) d.val).tuple)
        (cell d.val.2)
        (reference_empty rankLength_ge d.val.1.property (rankOrder_arc G ψLaw hYX fiber deleted ord hord hrank) (fullWildcard (V := V) (Y := Y) d.val).tuple)
        (reference_univ rankLength_ge d.val.1.property (rankOrder_arc G ψLaw hYX fiber deleted ord hord hrank) (fullWildcard (V := V) (Y := Y) d.val).tuple) ∧
      x ∉ fullStars d.val.2 := by
  let g := referenceBit (rankOrder G ψLaw ord) d.val.1.val rankLength_ge (fullWildcard (V := V) (Y := Y) d.val).tuple
  have h0 : g ∅ = false := reference_empty rankLength_ge d.val.1.property
    (rankOrder_arc G ψLaw hYX fiber deleted ord hord hrank) _
  have h1 : g Set.univ = true := reference_univ rankLength_ge d.val.1.property
    (rankOrder_arc G ψLaw hYX fiber deleted ord hord hrank) _
  let r := transition g (cell d.val.2) h0 h1
  apply unstarred_transition_exists g (good_monotone rankLength_ge d.val.1.property
    (rankOrder_arc G ψLaw hYX fiber deleted ord hord hrank) _ hgood)
    (cell d.val.2) r (transition_spec g (cell d.val.2) h0 h1) (fullStars d.val.2)
  apply wildcard_forcing (K := maxCells X T) rfl full_cells_bound d.val.1.property
    (rankOrder G ψLaw ord) hgood (cell d.val.2) (fullStars d.val.2) r.val (Nat.le_of_lt r.isLt)
  intro x y hx hy
  exact TestGraph.wildcard_path (wildSupport G ψLaw hYX) (compSupport G ψLaw fiber)
    ord (fun v => deleted v = false) hord hrank (.inl d) hkeep x y hx hy

def bigFunction (fallback : X) (d : Common U X M T N) (u : U) : (X → Bool) → Bool :=
  fun b => conditionedBig (rankOrder G ψLaw ord) d.1.val rankLength_ge d.1.property
    (rankOrder_arc G ψLaw hYX fiber deleted ord hord hrank) d.2.1 (vertices d.2.2)
    (cell d.2.2) u fallback {x | b x = true}

def smallFunction (fallback : Y) (d : Common U X M T N) (v : V) : (Y → Bool) → Bool :=
  fun b => conditionedSmall (rankOrder G ψLaw ord) d.1.val rankLength_ge d.1.property
    (rankOrder_arc G ψLaw hYX fiber deleted ord hord hrank) d.2.1 (vertices d.2.2)
    (cell d.2.2) v fallback {y | b y = true}

def commonTransition (d : Common U X M T N) : Fin (cellCount d.2.1.val) :=
  transition (referenceBit (rankOrder G ψLaw ord) d.1.val rankLength_ge
    (.inl ⟨⟨d.2.1.val, by have := d.2.1.isLt; omega⟩, vertices d.2.2⟩)) (cell d.2.2)
    (reference_empty rankLength_ge d.1.property (rankOrder_arc G ψLaw hYX fiber deleted ord hord hrank) _)
    (reference_univ rankLength_ge d.1.property (rankOrder_arc G ψLaw hYX fiber deleted ord hord hrank) _)

theorem comparison_forces_deletion (d : ComparisonSupport (M := M) G ψLaw)
    (fallbackX : X) (fallbackY : Y)
    (hgoodU : Good (rankOrder G ψLaw ord) d.val.1.1.val rankLength_ge
      (.inl ⟨⟨d.val.1.2.1.val+1, by have := d.val.1.2.1.isLt; omega⟩,
        Fin.snoc (vertices d.val.1.2.2) (G.left d.val.2.1)⟩))
    (hgoodV : Good (rankOrder G ψLaw ord) d.val.1.1.val rankLength_ge
      (.inr ⟨d.val.1.2.1, vertices d.val.1.2.2, G.right d.val.2.1⟩))
    (hr : d.val.2.2.2.1 = commonTransition G ψLaw hYX fiber deleted ord hord hrank d.val.1)
    (hU : bigFunction G ψLaw hYX fiber deleted ord hord hrank fallbackX d.val.1 (G.left d.val.2.1)
      (Coupling.bigBits (fiber d.val.2.1) d.val.2.2.2.2) = true)
    (hV : smallFunction G ψLaw hYX fiber deleted ord hord hrank fallbackY d.val.1 (G.right d.val.2.1)
      (Coupling.smallBits d.val.2.2.2.2) = false) :
    deleted (.inr (.inr d)) = true := by
  by_contra h
  have hk : deleted (.inr (.inr d)) = false := Bool.eq_false_iff.mpr h
  have hp := TestGraph.comparison_path (wildSupport G ψLaw hYX) (compSupport G ψLaw fiber)
    ord (fun v => deleted v = false) hord hrank d hk
  apply comparison_forcing rankLength_ge (rankOrder G ψLaw ord) _ _ hgoodU hgoodV _ _ hp
  constructor
  · simpa only [bigFunction, conditionedBig, normalizedCondition, hgoodU, ↓reduceIte,
      bigStepBit, hr, commonTransition] using hU
  · simpa only [smallFunction, conditionedSmall, normalizedCondition, hgoodV, ↓reduceIte,
      hr, commonTransition] using hV

end DirectedFeedback.Construction

noncomputable section
open scoped Classical BigOperators
namespace DirectedFeedback.Pivotal
open Prefix
variable {I S : Type} [Fintype I] [DecidableEq I] {k : ℕ}

theorem omitted_crossing (cell : S → Fin k) (r : Fin k)
    (g : Set (S × I) → Bool) (hg : Monotone g) (f : (I → Bool) → Bool)
    (hf : ∀ b, f b = g (conditionedSet cell r {i | b i = true}))
    (o : LabelOrder I) (hh : omittedHit o.1 (pivotalEvent f o.1) o.2 = true) :
    ∃ q ≤ Fintype.card {i : I // i ≠ o.1}+1,
      let E := boundary (orderedCell cell o.2)
        ((Fintype.card {i : I // i ≠ o.1}+1)*r.val+q) \ {a | a.2 = o.1}
      g E = false ∧ g (E ∪ {a | a.2 = o.1}) = true := by
  obtain ⟨q,hq,hp⟩ := of_decide_eq_true hh
  have hp' := of_decide_eq_true hp
  have hs0 : {i | insertBit o.1 false (fun x => decide ((o.2 x).val < q)) i = true} =
      {i | i ≠ o.1 ∧ (o.2 i).val < q} := by
    ext i
    by_cases hi : i = o.1
    · subst i; simp
    · simp [insertBit, hi]
  have hs1 : {i | insertBit o.1 true (fun x => decide ((o.2 x).val < q)) i = true} =
      {i | i ≠ o.1 ∧ (o.2 i).val < q} ∪ {o.1} := by
    ext i
    by_cases hi : i = o.1
    · subst i; simp
    · simp [insertBit, hi]
  rw [hf, hf, hs0, hs1] at hp'
  exact ⟨q,hq, single_label_crossing cell o.2 r q hq o.1 g hg hp'.1 hp'.2⟩

end DirectedFeedback.Pivotal

namespace DirectedFeedback.RankGraph
open Prefix Pivotal
variable {U V X Y S I : Type} [Fintype I] [DecidableEq I]
variable {T N L K k : ℕ} {d : Tuple U V T} {ψ : Fin L → Fin N}

theorem ordered_wildcard_forcing (hL : L = 10*K+30)
    (o : LabelOrder I) (hk : k*(Fintype.card {i : I // i ≠ o.1}+1) ≤ K)
    (hψ : StrictMono ψ) (ord : Rank U V X Y T N → ℕ)
    (hg : Good ord ψ (by omega) d)
    (e : Domain U V X Y T d ≃ S × I) (cell : S → Fin k) (r : Fin k)
    (f : (I → Bool) → Bool)
    (hf : ∀ b, f b = referenceBit ord ψ (by omega) d
      (e ⁻¹' conditionedSet cell r {i | b i = true}))
    (hm : Monotone (fun A : Set (S × I) => referenceBit ord ψ (by omega) d (e ⁻¹' A)))
    (hpath : ∀ x y, belowWildcard d (fun a => orderedCell cell o.2 (e a))
        {a | (e a).2 = o.1}
        (fun j => ψ ⟨10*j.val+19, by have := j.isLt; omega⟩) x →
      aboveWildcard d (fun a => orderedCell cell o.2 (e a)) {a | (e a).2 = o.1}
        (fun j => ψ ⟨10*j.val+19, by have := j.isLt; omega⟩) y →
      ord (vertex d x) < ord (vertex d y)) :
    omittedHit o.1 (pivotalEvent f o.1) o.2 = false := by
  apply Bool.eq_false_iff.mpr
  intro hh
  obtain ⟨q,hq,hcross⟩ := omitted_crossing cell r
    (fun A => referenceBit ord ψ (by omega) d (e ⁻¹' A)) hm f hf o hh
  have hcut : (Fintype.card {i : I // i ≠ o.1}+1)*r.val+q ≤
      k*(Fintype.card {i : I // i ≠ o.1}+1) := by
    have h := Nat.mul_le_mul_left (Fintype.card {i : I // i ≠ o.1}+1) r.isLt
    simp only [Nat.mul_succ] at h
    rw [Nat.mul_comm k]
    omega
  apply wildcard_forcing hL hk hψ ord hg
    (fun a => orderedCell cell o.2 (e a)) {a | (e a).2 = o.1}
    _ hcut hpath
  simpa only [boundary, Set.preimage_sdiff, Set.preimage_union, Set.preimage_ofPred_eq] using hcross

end DirectedFeedback.RankGraph

namespace DirectedFeedback.Construction
open DirectedFeedback.SourceProbability FiniteDistribution
open RankGraph Prefix PrefixExperiment Games Pivotal
variable {U V E X Y : Type} [Fintype U] [Fintype V] [Fintype E]
  [Fintype X] [Fintype Y] [Nonempty X] [Nonempty Y]
variable {M T N : ℕ} [NeZero M] [NeZero T]
variable (G : Game U V E X Y) (ψLaw : FiniteDistribution (Emb (rankLength X T) N))
variable (hYX : Fintype.card Y ≤ Fintype.card X) (fiber : E → X ≃ Y × Bool)
variable (deleted : OutputVertex (M := M) G ψLaw → Bool)
variable (ord : OutputVertex (M := M) G ψLaw → ℕ)
variable (hord : ∀ {a b}, deleted a = false → deleted b = false →
  OutputArc G ψLaw hYX fiber a b → ord a < ord b)
variable (hrank : ∀ r, deleted (.inl r) = false)

def bigGood (d : Common U X M T N) (u : U) : Prop :=
  Good (rankOrder G ψLaw ord) d.1.val rankLength_ge
    (.inl ⟨⟨d.2.1.val+1, by have := d.2.1.isLt; omega⟩, Fin.snoc (vertices d.2.2) u⟩)
def smallGood (d : Common U X M T N) (v : V) : Prop :=
  Good (rankOrder G ψLaw ord) d.1.val rankLength_ge
    (.inr ⟨d.2.1, vertices d.2.2, v⟩)

theorem small_forces_deletion (d : (smallLaw (M := M) G ψLaw).Support) (fallback : Y)
    (hgood : smallGood G ψLaw ord d.val.1 d.val.2.1)
    (hh : omittedHit d.val.2.2.1 (pivotalEvent
      (smallFunction G ψLaw hYX fiber deleted ord hord hrank fallback d.val.1 d.val.2.1)
      d.val.2.2.1) d.val.2.2.2 = true) :
    deleted (.inr (.inl (.inr (.inr d)))) = true := by
  by_contra h
  have hk : deleted (.inr (.inl (.inr (.inr d)))) = false := Bool.eq_false_iff.mpr h
  have hf := ordered_wildcard_forcing (K := maxCells X T) rfl d.val.2.2
    (ordered_cells_bound hYX d.val.1.2.1 d.val.2.2) d.val.1.1.property
    (rankOrder G ψLaw ord) hgood (Equiv.refl _) (cell d.val.1.2.2)
    (commonTransition G ψLaw hYX fiber deleted ord hord hrank d.val.1)
    (smallFunction G ψLaw hYX fiber deleted ord hord hrank fallback d.val.1 d.val.2.1)
    (by intro b; simp only [smallFunction, conditionedSmall, normalizedCondition,
                               smallGood] at *
        simp only [hgood, ↓reduceIte]; rfl)
    (by intro A B hAB
        exact good_monotone rankLength_ge d.val.1.1.property
          (rankOrder_arc G ψLaw hYX fiber deleted ord hord hrank) _ hgood hAB)
    (by intro x y hx hy
        exact TestGraph.wildcard_path (wildSupport G ψLaw hYX) (compSupport G ψLaw fiber)
          ord (fun v => deleted v = false) hord hrank (.inr (.inr d)) hk x y hx hy)
  exact Bool.noConfusion (hh.symm.trans hf)

theorem big_forces_deletion (d : (bigLaw (M := M) G ψLaw).Support) (fallback : X)
    (hgood : bigGood G ψLaw ord d.val.1 d.val.2.1)
    (hh : omittedHit d.val.2.2.1 (pivotalEvent
      (bigFunction G ψLaw hYX fiber deleted ord hord hrank fallback d.val.1 d.val.2.1)
      d.val.2.2.1) d.val.2.2.2 = true) :
    deleted (.inr (.inl (.inr (.inl d)))) = true := by
  by_contra h
  have hk : deleted (.inr (.inl (.inr (.inl d)))) = false := Bool.eq_false_iff.mpr h
  have hf := ordered_wildcard_forcing (K := maxCells X T) rfl d.val.2.2
    (ordered_cells_bound le_rfl d.val.1.2.1 d.val.2.2) d.val.1.1.property
    (rankOrder G ψLaw ord) hgood (splitLast d.val.1.2.1.val) (cell d.val.1.2.2)
    (commonTransition G ψLaw hYX fiber deleted ord hord hrank d.val.1)
    (bigFunction G ψLaw hYX fiber deleted ord hord hrank fallback d.val.1 d.val.2.1)
    (by intro b; simp only [bigFunction, conditionedBig, normalizedCondition,
                               bigGood] at *
        simp only [hgood, ↓reduceIte]; rfl)
    (by intro A B hAB
        exact good_monotone rankLength_ge d.val.1.1.property
          (rankOrder_arc G ψLaw hYX fiber deleted ord hord hrank) _ hgood
          (Set.preimage_mono hAB))
    (by intro x y hx hy
        exact TestGraph.wildcard_path (wildSupport G ψLaw hYX) (compSupport G ψLaw fiber)
          ord (fun v => deleted v = false) hord hrank (.inr (.inl d)) hk x y hx hy)
  exact Bool.noConfusion (hh.symm.trans hf)

end DirectedFeedback.Construction

noncomputable section
open scoped Classical BigOperators
namespace DirectedFeedback.SourceProbability.FiniteDistribution
variable {Ω : Type*} [Fintype Ω]

theorem expectation_mono_support (μ : FiniteDistribution Ω) {f g : Ω → ℝ}
    (h : ∀ x, 0 < μ.weight x → f x ≤ g x) : μ.expectation f ≤ μ.expectation g := by
  unfold expectation
  apply Finset.sum_le_sum
  intro x _
  by_cases hx : 0 < μ.weight x
  · exact mul_le_mul_of_nonneg_left (h x hx) (μ.nonnegative x)
  · have hz : μ.weight x = 0 := le_antisymm (not_lt.mp hx) (μ.nonnegative x)
    simp [hz]

theorem probability_mono_support (μ : FiniteDistribution Ω) {f g : Ω → Bool}
    (h : ∀ x, 0 < μ.weight x → f x = true → g x = true) : μ.probability f ≤ μ.probability g := by
  simp only [probability_eq_expect]
  apply expectation_mono_support μ
  intro x hx
  cases hf : f x
  · cases g x <;> simp
  · simp [h x hx hf]

end DirectedFeedback.SourceProbability.FiniteDistribution

namespace DirectedFeedback.Pivotal
open DirectedFeedback.SourceProbability FiniteDistribution
variable {I Ω : Type*} [Fintype I] [DecidableEq I] [Nonempty I] [Fintype Ω]

theorem labelOrder_weight_pos (o : LabelOrder I) : 0 < labelOrderLaw.weight o := by
  simp only [labelOrderLaw, sigma, uniform]
  positivity

theorem averaged_budget_charge_support (μ : FiniteDistribution Ω) (f : Ω → (I → Bool) → Bool)
    (good : Ω → Bool) (deleted : Ω → LabelOrder I → Bool)
    (D ρ : ℝ) (hρ : Fintype.card I * ρ ≤ 1)
    (hbad : μ.probability (fun a => !(good a)) ≤ ρ)
    (hcost : Fintype.card I * μ.expectation (fun a => labelOrderLaw.probability (deleted a)) ≤ D)
    (hforce : ∀ a, 0 < μ.weight a → good a = true → ∀ o,
      omittedHit o.1 (pivotalEvent (f a) o.1) o.2 = true → deleted a o = true) :
    μ.expectation (fun a => budget (f a)) ≤ D+1 := by
  have hb (a : Ω) (ha : 0 < μ.weight a) : budget (f a) ≤
      Fintype.card I * labelOrderLaw.probability (deleted a) +
      Fintype.card I * (if !(good a) then 1 else 0 : ℝ) := by
    cases hg : good a
    · simp only [Bool.not_false, ↓reduceIte, mul_one]
      have hp := probability_nonnegative labelOrderLaw (deleted a)
      have hc : (0:ℝ) ≤ Fintype.card I := Nat.cast_nonneg _
      have h := budget_le_card (f a)
      nlinarith
    · simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte, mul_zero, add_zero]
      exact single_label_budget_charge (f a) (deleted a) (hforce a ha hg)
  have hm := expectation_mono_support μ hb
  rw [expectation_add, expectation_mul_left, expectation_mul_left, ← probability_eq_expect] at hm
  have hc : (0:ℝ) ≤ Fintype.card I := Nat.cast_nonneg _
  nlinarith [mul_le_mul_of_nonneg_left hbad hc]

omit [Fintype I] [DecidableEq I] [Nonempty I] in

theorem subset_function_properties (f : Set I → Bool)
    (hm : Monotone f) (h0 : f ∅ = false) (h1 : f Set.univ = true) :
    Monotone (fun b : I → Bool => f {i | b i = true}) ∧
      (fun b : I → Bool => f {i | b i = true}) (fun _ => false) = false ∧
      (fun b : I → Bool => f {i | b i = true}) (fun _ => true) = true := by
  refine ⟨?_, by simpa using h0, by simpa using h1⟩
  intro a b hab
  apply hm
  intro i hi
  exact Bool.le_iff_imp.mp (hab i) hi

end DirectedFeedback.Pivotal

namespace DirectedFeedback.Construction
open DirectedFeedback.SourceProbability FiniteDistribution
open RankGraph Prefix PrefixExperiment Games Pivotal
variable {U V E X Y : Type} [Fintype U] [Fintype V] [Fintype E]
  [Fintype X] [Fintype Y] [Nonempty X] [Nonempty Y]
variable {M T N : ℕ} [NeZero M] [NeZero T]
variable (G : Game U V E X Y) (ψLaw : FiniteDistribution (Emb (rankLength X T) N))
variable (hYX : Fintype.card Y ≤ Fintype.card X) (fiber : E → X ≃ Y × Bool)
variable (deleted : OutputVertex (M := M) G ψLaw → Bool)
variable (ord : OutputVertex (M := M) G ψLaw → ℕ)
variable (hord : ∀ {a b}, deleted a = false → deleted b = false →
  OutputArc G ψLaw hYX fiber a b → ord a < ord b)
variable (hrank : ∀ r, deleted (.inl r) = false)

end DirectedFeedback.Construction
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
