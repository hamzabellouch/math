import Mathlib.Algebra.Order.BigOperators.Expect
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Std

namespace OAI

section

/-!
The real-valued finite-expectation argument in Lemma 6.3 and equation (6.11).
The density's normalization and second-moment bound are inputs; the variance,
Cauchy--Schwarz comparison, parameter error, and transferred signal are proved.
The test is allowed to depend on every coordinate of the sampled map.
-/

namespace UniqueGamesTheorem.Soundness.ExpectationComparison

open scoped BigOperators

variable {ι : Type*}

/-- Centering a normalized density subtracts exactly one from its second moment. -/
theorem density_variance_identity (s : Finset ι) (hs : s.Nonempty)
    (d : ι → ℝ) (hd : (𝔼 i ∈ s, d i) = 1) :
    (𝔼 i ∈ s, (d i - 1) ^ 2) = (𝔼 i ∈ s, d i ^ 2) - 1 := by
  calc
    (𝔼 i ∈ s, (d i - 1) ^ 2)
        = (𝔼 i ∈ s, ((d i ^ 2 - 2 * d i) + 1)) := by
          apply Finset.expect_congr rfl
          intro i _
          ring
    _ = (𝔼 i ∈ s, d i ^ 2) - 1 := by
      rw [Finset.expect_add_distrib, Finset.expect_sub_distrib,
        ← Finset.mul_expect, Finset.expect_const hs, hd]
      ring

theorem density_variance_le (s : Finset ι) (hs : s.Nonempty)
    (d : ι → ℝ) (ε : ℝ) (hd : (𝔼 i ∈ s, d i) = 1)
    (hsecond : (𝔼 i ∈ s, d i ^ 2) ≤ 1 + ε) :
    (𝔼 i ∈ s, (d i - 1) ^ 2) ≤ ε := by
  rw [density_variance_identity s hs d hd]
  linarith

theorem bounded_test_second_moment (s : Finset ι) (hs : s.Nonempty)
    (H : ι → ℝ) (hH : ∀ i ∈ s, |H i| ≤ 1) :
    (𝔼 i ∈ s, H i ^ 2) ≤ 1 := by
  apply Finset.expect_le hs
  intro i hi
  exact (sq_le_one_iff_abs_le_one (H i)).mpr (hH i hi)

/-- Cauchy--Schwarz for an arbitrary whole-map test, in squared form. -/
theorem bounded_test_centered_square (s : Finset ι) (hs : s.Nonempty)
    (d H : ι → ℝ) (ε : ℝ) (hd : (𝔼 i ∈ s, d i) = 1)
    (hsecond : (𝔼 i ∈ s, d i ^ 2) ≤ 1 + ε)
    (hH : ∀ i ∈ s, |H i| ≤ 1) :
    (𝔼 i ∈ s, H i * (d i - 1)) ^ 2 ≤ ε := by
  have hcs := Finset.expect_mul_sq_le_sq_mul_sq s H (fun i => d i - 1)
  have hvnonneg : 0 ≤ (𝔼 i ∈ s, (d i - 1) ^ 2) :=
    Finset.expect_nonneg (fun i _ => sq_nonneg (d i - 1))
  have hHsecond := bounded_test_second_moment s hs H hH
  have hproduct := mul_le_mul_of_nonneg_right hHsecond hvnonneg
  have hvariance := density_variance_le s hs d ε hd hsecond
  nlinarith

/-- The actual difference of the two normalized finite expectations. -/
theorem bounded_test_expectation_comparison (s : Finset ι) (hs : s.Nonempty)
    (d H : ι → ℝ) (ε : ℝ) (hd : (𝔼 i ∈ s, d i) = 1)
    (hsecond : (𝔼 i ∈ s, d i ^ 2) ≤ 1 + ε)
    (hH : ∀ i ∈ s, |H i| ≤ 1) :
    |(𝔼 i ∈ s, H i * d i) - (𝔼 i ∈ s, H i)| ≤ Real.sqrt ε := by
  have hdiff : (𝔼 i ∈ s, H i * d i) - (𝔼 i ∈ s, H i) =
      (𝔼 i ∈ s, H i * (d i - 1)) := by
    rw [← Finset.expect_sub_distrib]
    apply Finset.expect_congr rfl
    intro i _
    ring
  rw [hdiff]
  exact Real.abs_le_sqrt (bounded_test_centered_square s hs d H ε hd hsecond hH)

/-- The squared parameter inequality implies error at most θ/4. -/
theorem comparison_error_le_quarter (ε θ : ℝ) (hθ : 0 ≤ θ)
    (hε : ε ≤ (θ / 4) ^ 2) : Real.sqrt ε ≤ θ / 4 := by
  exact (Real.sqrt_le_iff).mpr ⟨by positivity, hε⟩

/-- The real inequality selected by equation (4.4) gives its stated error. -/
theorem parameter_error_le_quarter (t k cap θ : ℝ) (hk : 0 < k)
    (hθ : 0 < θ) (hsize : 16 * t ^ 2 * cap / θ ^ 2 ≤ k) :
    Real.sqrt (t ^ 2 / k * cap) ≤ θ / 4 := by
  apply comparison_error_le_quarter _ θ hθ.le
  have hmult : 16 * t ^ 2 * cap ≤ k * θ ^ 2 :=
    (div_le_iff₀ (sq_pos_of_pos hθ)).mp hsize
  rw [div_mul_eq_mul_div]
  apply (div_le_iff₀ hk).mpr
  nlinarith

theorem map_law_parameter_error (t k L : ℕ) (θ : ℝ) (hk : 0 < k)
    (hθ : 0 < θ)
    (hsize : 16 * (t : ℝ) ^ 2 * (2 : ℝ) ^ (t * L) / θ ^ 2 ≤ (k : ℝ)) :
    Real.sqrt ((t : ℝ) ^ 2 / (k : ℝ) * (2 : ℝ) ^ (t * L)) ≤ θ / 4 := by
  exact parameter_error_le_quarter (t : ℝ) (k : ℝ) ((2 : ℝ) ^ (t * L)) θ
    (by exact_mod_cast hk) hθ hsize

theorem bounded_test_expectation_quarter (s : Finset ι) (hs : s.Nonempty)
    (d H : ι → ℝ) (ε θ : ℝ) (hθ : 0 ≤ θ)
    (hε : ε ≤ (θ / 4) ^ 2) (hd : (𝔼 i ∈ s, d i) = 1)
    (hsecond : (𝔼 i ∈ s, d i ^ 2) ≤ 1 + ε)
    (hH : ∀ i ∈ s, |H i| ≤ 1) :
    |(𝔼 i ∈ s, H i * d i) - (𝔼 i ∈ s, H i)| ≤ θ / 4 :=
  (bounded_test_expectation_comparison s hs d H ε hd hsecond hH).trans
    (comparison_error_le_quarter ε θ hθ hε)

/-- A signal at least θ under the uniform law stays at least θ/2 after transfer. -/
theorem transferred_signal_lower (s : Finset ι) (hs : s.Nonempty)
    (d H : ι → ℝ) (ε θ : ℝ) (hθ : 0 ≤ θ)
    (hε : ε ≤ (θ / 4) ^ 2) (hd : (𝔼 i ∈ s, d i) = 1)
    (hsecond : (𝔼 i ∈ s, d i ^ 2) ≤ 1 + ε)
    (hH : ∀ i ∈ s, |H i| ≤ 1) (hsignal : θ ≤ (𝔼 i ∈ s, H i)) :
    θ / 2 ≤ (𝔼 i ∈ s, H i * d i) := by
  have h := abs_le.mp
    (bounded_test_expectation_quarter s hs d H ε θ hθ hε hd hsecond hH)
  linarith

/-- Equation (6.10), allowing the chosen index and sign to depend on the row. -/
def wholeMapTest {Map Row Column Index : Type*} (row : Map → Row)
    (column : Map → Column) (sign : Row → ℝ) (value : Row → Column → ℝ)
    (chosen : Row → Index) (character : Index → Column → ℝ) (M : Map) : ℝ :=
  sign (row M) * value (row M) (column M) * character (chosen (row M)) (column M)

theorem wholeMapTest_abs_le_one {Map Row Column Index : Type*}
    (row : Map → Row) (column : Map → Column) (sign : Row → ℝ)
    (value : Row → Column → ℝ) (chosen : Row → Index)
    (character : Index → Column → ℝ)
    (hsign : ∀ r, |sign r| ≤ 1) (hvalue : ∀ r c, |value r c| ≤ 1)
    (hcharacter : ∀ t c, |character t c| ≤ 1) (M : Map) :
    |wholeMapTest row column sign value chosen character M| ≤ 1 := by
  simp only [wholeMapTest, abs_mul]
  have hfirst : |sign (row M)| * |value (row M) (column M)| ≤ 1 := by
    nlinarith [hsign (row M), hvalue (row M) (column M),
      abs_nonneg (sign (row M)), abs_nonneg (value (row M) (column M)),
      mul_le_mul (hsign (row M)) (hvalue (row M) (column M))
        (abs_nonneg (value (row M) (column M))) (by norm_num : (0 : ℝ) ≤ 1)]
  have hmul := mul_le_mul hfirst (hcharacter (chosen (row M)) (column M))
    (abs_nonneg (character (chosen (row M)) (column M))) (by norm_num : (0 : ℝ) ≤ 1)
  simpa using hmul

/-- Instantiate comparison with equation (6.10), including its row-dependent index. -/
theorem wholeMapTest_comparison {Map Row Column Index : Type*}
    (s : Finset Map) (hs : s.Nonempty) (d : Map → ℝ) (ε : ℝ)
    (row : Map → Row) (column : Map → Column) (sign : Row → ℝ)
    (value : Row → Column → ℝ) (chosen : Row → Index)
    (character : Index → Column → ℝ)
    (hd : (𝔼 M ∈ s, d M) = 1)
    (hsecond : (𝔼 M ∈ s, d M ^ 2) ≤ 1 + ε)
    (hsign : ∀ r, |sign r| ≤ 1) (hvalue : ∀ r c, |value r c| ≤ 1)
    (hcharacter : ∀ t c, |character t c| ≤ 1) :
    |(𝔼 M ∈ s, wholeMapTest row column sign value chosen character M * d M) -
      (𝔼 M ∈ s, wholeMapTest row column sign value chosen character M)|
      ≤ Real.sqrt ε := by
  apply bounded_test_expectation_comparison s hs d _ ε hd hsecond
  intro M _
  exact wholeMapTest_abs_le_one row column sign value chosen character
    hsign hvalue hcharacter M

/-- Average a uniform per-U error, allowing the map sample space to depend on U. -/
theorem averaged_expectation_comparison {U : Type*} (Map : U → Type*)
    (us : Finset U) (hus : us.Nonempty) (maps : (u : U) → Finset (Map u))
    (hmaps : ∀ u ∈ us, (maps u).Nonempty)
    (d H : (u : U) → Map u → ℝ) (ε : ℝ)
    (hd : ∀ u ∈ us, (𝔼 M ∈ maps u, d u M) = 1)
    (hsecond : ∀ u ∈ us, (𝔼 M ∈ maps u, d u M ^ 2) ≤ 1 + ε)
    (hH : ∀ u ∈ us, ∀ M ∈ maps u, |H u M| ≤ 1) :
    |(𝔼 u ∈ us, 𝔼 M ∈ maps u, H u M * d u M) -
      (𝔼 u ∈ us, 𝔼 M ∈ maps u, H u M)| ≤ Real.sqrt ε := by
  rw [← Finset.expect_sub_distrib]
  calc
    _ ≤ 𝔼 u ∈ us,
        |(𝔼 M ∈ maps u, H u M * d u M) - (𝔼 M ∈ maps u, H u M)| :=
      Finset.abs_expect_le _ _
    _ ≤ Real.sqrt ε := by
      apply Finset.expect_le hus
      intro u hu
      exact bounded_test_expectation_comparison (maps u) (hmaps u hu)
        (d u) (H u) ε (hd u hu) (hsecond u hu) (hH u hu)

/-- Equation (6.11): only the signal averaged over U is assumed large. -/
theorem averaged_transferred_signal_lower {U : Type*} (Map : U → Type*)
    (us : Finset U) (hus : us.Nonempty) (maps : (u : U) → Finset (Map u))
    (hmaps : ∀ u ∈ us, (maps u).Nonempty)
    (d H : (u : U) → Map u → ℝ) (ε θ : ℝ) (hθ : 0 ≤ θ)
    (hε : ε ≤ (θ / 4) ^ 2)
    (hd : ∀ u ∈ us, (𝔼 M ∈ maps u, d u M) = 1)
    (hsecond : ∀ u ∈ us, (𝔼 M ∈ maps u, d u M ^ 2) ≤ 1 + ε)
    (hH : ∀ u ∈ us, ∀ M ∈ maps u, |H u M| ≤ 1)
    (hsignal : θ ≤ (𝔼 u ∈ us, 𝔼 M ∈ maps u, H u M)) :
    θ / 2 ≤ (𝔼 u ∈ us, 𝔼 M ∈ maps u, H u M * d u M) := by
  have hcomparison := averaged_expectation_comparison Map us hus maps hmaps d H ε
    hd hsecond hH
  have hquarter := comparison_error_le_quarter ε θ hθ hε
  have hbounds := abs_le.mp (hcomparison.trans hquarter)
  linarith

/-- Uniform finite means in the quotient-of-sums convention. -/
theorem uniform_expect_eq_sum_div_card [Fintype ι] (f : ι → ℝ) :
    (𝔼 i, f i) = (∑ i, f i) / (Fintype.card ι : ℝ) :=
  Fintype.expect_eq_sum_div_card f

end UniqueGamesTheorem.Soundness.ExpectationComparison

end

section

namespace UniqueGamesTheorem.Soundness.IncidenceExtraction

abbrev Triple := Fin 3 → Bool

def xorTriple (x : Triple) : Bool := (x 0 ^^ x 1) ^^ x 2

structure Incidence (Occurrence Name : Type) where
  name : Occurrence → Fin 3 → Name
  rhs : Occurrence → Bool

def Incidence.accepts {Occurrence Name : Type}
    (g : Incidence Occurrence Name) (o : Occurrence) (i : Fin 3)
    (a : Triple) (b : Bool) : Prop :=
  xorTriple a = g.rhs o ∧ a i = b

/-- The incidence predicate as a game on the actual questions `(o,n)`, with the
    retained slot left internal to the verifier. -/
def Incidence.namedAccepts {Occurrence Name : Type}
    (g : Incidence Occurrence Name) (o : Occurrence) (n : Name)
    (a : Triple) (b : Bool) : Prop :=
  ∃ i, g.name o i = n ∧ g.accepts o i a b

theorem Incidence.accepts_implies_namedAccepts {Occurrence Name : Type}
    (g : Incidence Occurrence Name) (o : Occurrence) (i : Fin 3)
    (a : Triple) (b : Bool) (h : g.accepts o i a b) :
    g.namedAccepts o (g.name o i) a b :=
  ⟨i, rfl, h⟩

/-- Distinct names make the named-variable predicate equivalent to the sampled
    retained-slot predicate, without revealing that slot to either strategy. -/
theorem Incidence.namedAccepts_iff_accepts {Occurrence Name : Type}
    (g : Incidence Occurrence Name)
    (distinct : ∀ o i j, g.name o i = g.name o j → i = j)
    (o : Occurrence) (i : Fin 3) (a : Triple) (b : Bool) :
    g.namedAccepts o (g.name o i) a b ↔ g.accepts o i a b := by
  constructor
  · rintro ⟨j, hname, h⟩
    have hji := distinct o j i hname
    simpa [hji] using h
  · exact g.accepts_implies_namedAccepts o i a b

structure FullPoint (Position : Type) where
  homogeneous : Bool
  coords : Position → Triple

def FullPoint.valid {Position Occurrence Name : Type}
    (g : Incidence Occurrence Name) (u : Position → Occurrence)
    (e : FullPoint Position) : Prop :=
  ∀ j, xorTriple (e.coords j) = (g.rhs (u j) && e.homogeneous)

structure PartnerPoint (Position : Type) where
  homogeneous : Bool
  single : Position → Bool

/- Only the single positions matter to the extracted incidence game. -/
def AugmentedAccepts {Position Occurrence Name : Type}
    (g : Incidence Occurrence Name) (u : Position → Occurrence)
    (active : Position → Prop) (slot : Position → Fin 3)
    (eA : FullPoint Position) (eB : PartnerPoint Position) : Prop :=
  eA.valid g u ∧ eA.homogeneous = true ∧ eB.homogeneous = true ∧
  ∀ j, active j → eA.coords j (slot j) = eB.single j

def RepeatedAccepts {Position Occurrence Name : Type}
    (g : Incidence Occurrence Name) (u : Position → Occurrence)
    (slot : Position → Fin 3) (inside : Position → Prop)
    (answerA : Position → Triple) (answerB : Position → Bool) : Prop :=
  ∀ j, inside j → g.accepts (u j) (slot j) (answerA j) (answerB j)

/-- Acceptance of the augmented projection game implies acceptance of every
    incidence coordinate in any subset of the active positions. -/
theorem augmented_accepts_implies_repeated_accepts
    {Position Occurrence Name : Type}
    (g : Incidence Occurrence Name) (u : Position → Occurrence)
    (active inside : Position → Prop) (slot : Position → Fin 3)
    (eA : FullPoint Position) (eB : PartnerPoint Position)
    (hinside : ∀ j, inside j → active j)
    (haccept : AugmentedAccepts g u active slot eA eB) :
    RepeatedAccepts g u slot inside eA.coords eB.single := by
  obtain ⟨hvalid, hone, _, hagree⟩ := haccept
  intro j hj
  constructor
  · have heq := hvalid j
    simpa [hone] using heq
  · exact hagree j (hinside j hj)

/-- The same containment stated on the occurrence/name question vectors actually
    given to the two repeated-game players. -/
theorem augmented_accepts_implies_named_repeated_accepts
    {Position RepeatPosition Occurrence Name : Type}
    (g : Incidence Occurrence Name) (u : Position → Occurrence)
    (active : Position → Prop) (slot : Position → Fin 3)
    (embed : RepeatPosition → Position)
    (eA : FullPoint Position) (eB : PartnerPoint Position)
    (hinside : ∀ r, active (embed r))
    (haccept : AugmentedAccepts g u active slot eA eB) :
    ∀ r, g.namedAccepts (u (embed r))
      (g.name (u (embed r)) (slot (embed r)))
      (eA.coords (embed r)) (eB.single (embed r)) := by
  intro r
  apply g.accepts_implies_namedAccepts
  obtain ⟨hvalid, hone, _, hagree⟩ := haccept
  constructor
  · have heq := hvalid (embed r)
    simpa [hone] using heq
  · exact hagree (embed r) (hinside r)

/-!
The next definitions separate local strategies from arbitrary joint strategies.
Each question reconstruction and each answer extraction has access to only one
player's question. A value conditioned on by an analysis may occur as a fixed
parameter of a `LocalSimulation`; it cannot become an additional random input.
-/

structure Game (QA QB A B : Type) where
  accepts : QA → QB → A → B → Prop

structure Strategies (QA QB A B : Type) where
  first : QA → A
  second : QB → B

def Strategies.wins {QA QB A B : Type} (s : Strategies QA QB A B)
    (g : Game QA QB A B) (qa : QA) (qb : QB) : Prop :=
  g.accepts qa qb (s.first qa) (s.second qb)

structure LocalSimulation
    {InnerQA InnerQB InnerA InnerB OuterQA OuterQB OuterA OuterB : Type}
    (inner : Game InnerQA InnerQB InnerA InnerB)
    (outer : Game OuterQA OuterQB OuterA OuterB) where
  questionA : InnerQA → OuterQA
  questionB : InnerQB → OuterQB
  answerA : InnerQA → OuterA → InnerA
  answerB : InnerQB → OuterB → InnerB
  sound : ∀ qa qb a b,
    outer.accepts (questionA qa) (questionB qb) a b →
    inner.accepts qa qb (answerA qa a) (answerB qb b)

def LocalSimulation.induced
    {InnerQA InnerQB InnerA InnerB OuterQA OuterQB OuterA OuterB : Type}
    {inner : Game InnerQA InnerQB InnerA InnerB}
    {outer : Game OuterQA OuterQB OuterA OuterB}
    (r : LocalSimulation inner outer)
    (s : Strategies OuterQA OuterQB OuterA OuterB) :
    Strategies InnerQA InnerQB InnerA InnerB where
  first qa := r.answerA qa (s.first (r.questionA qa))
  second qb := r.answerB qb (s.second (r.questionB qb))

/-- A local simulation transports every deterministic strategy and contains
    its winning event pointwise. No shared access to the questions is used. -/
theorem LocalSimulation.induced_wins
    {InnerQA InnerQB InnerA InnerB OuterQA OuterQB OuterA OuterB : Type}
    {inner : Game InnerQA InnerQB InnerA InnerB}
    {outer : Game OuterQA OuterQB OuterA OuterB}
    (r : LocalSimulation inner outer)
    (s : Strategies OuterQA OuterQB OuterA OuterB)
    (qa : InnerQA) (qb : InnerQB)
    (hwins : s.wins outer (r.questionA qa) (r.questionB qb)) :
    (r.induced s).wins inner qa qb :=
  r.sound qa qb (s.first (r.questionA qa)) (s.second (r.questionB qb)) hwins

/-- Fixing strategy randomness gives another local deterministic strategy;
    the simulation proof applies to every seed, before any averaging. -/
theorem LocalSimulation.seeded_induced_wins
    {InnerQA InnerQB InnerA InnerB OuterQA OuterQB OuterA OuterB Seed : Type}
    {inner : Game InnerQA InnerQB InnerA InnerB}
    {outer : Game OuterQA OuterQB OuterA OuterB}
    (r : LocalSimulation inner outer)
    (strategy : Seed → Strategies OuterQA OuterQB OuterA OuterB)
    (seed : Seed) (qa : InnerQA) (qb : InnerQB)
    (hwins : (strategy seed).wins outer (r.questionA qa) (r.questionB qb)) :
    (r.induced (strategy seed)).wins inner qa qb :=
  r.induced_wins (strategy seed) qa qb hwins

end UniqueGamesTheorem.Soundness.IncidenceExtraction

end

end OAI
