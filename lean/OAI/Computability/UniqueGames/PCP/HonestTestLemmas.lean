import Mathlib.Logic.Equiv.Prod
import OAI.Computability.UniqueGames.Foundations.SamplingLemmas
import OAI.Computability.UniqueGames.PCP.ClauseVerifierLemmas
import OAI.Computability.UniqueGames.PCP.FourierResponseLemmas
import OAI.Computability.UniqueGames.PCP.SourceNoiseParameterLemmas
import OAI.Computability.UniqueGames.Reduction.ExplicitLemmas

namespace OAI

section

/-! Honest completeness of the actual three-query test. Compatible coordinate
dictators cancel the two uniform query tables, leaving exactly one noise bit.
The finite-tape form uses the proved product-noise pushforward law. -/

noncomputable section

namespace UniqueGamesTheorem.Foundations.Hastad

open scoped BigOperators
open UniqueGamesTheorem.Reduction.FiniteNoise

variable {I J : Type*} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]

omit [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J] in
/-- For compatible honest coordinates, the test parity is precisely the
selected noise coordinate, for every individual choice of query tables. -/
theorem dictator_test_parity (π : J → I) (i : I) (j : J) (hπ : π j = i)
    (f : Cube I) (g μ : Cube J) :
    (f i ^^ g j ^^ (thirdQuery π f g μ) j) = μ j := by
  simp only [thirdQuery, cubeXor, hπ]
  cases f i <;> cases g j <;> cases μ j <;> rfl

/-- The product noise law has the specified sign bias in every coordinate. -/
theorem noise_coordinate_sign (ε : ℝ) (j : J) :
    (∑ μ : Cube J, noiseWeight ε μ * bitSign (μ j)) = 1 - 2 * ε := by
  have hs : support (coordinateMask j) = {j} := by
    ext k
    simp [support, coordinateMask]
  have h := noise_walsh ε (coordinateMask j)
  simp_rw [walsh_symm (coordinateMask j), walsh_coordinateMask] at h
  simpa only [hs, Finset.card_singleton, pow_one] using h

/-- The probability of a false noise bit is exactly `1 - ε`. This is an
algebraic identity of the explicit product weights, valid for every real ε. -/
theorem noise_coordinate_false (ε : ℝ) (j : J) :
    (∑ μ : Cube J, noiseWeight ε μ * if μ j then (0 : ℝ) else 1) = 1 - ε := by
  have hind (b : Bool) : (if b then (0 : ℝ) else 1) =
      (1 + bitSign b) * (2 : ℝ)⁻¹ := by
    cases b <;> norm_num [bitSign]
  have ht (μ : Cube J) : noiseWeight ε μ * (if μ j then (0 : ℝ) else 1) =
      (noiseWeight ε μ + noiseWeight ε μ * bitSign (μ j)) * (2 : ℝ)⁻¹ := by
    rw [hind]
    ring
  simp_rw [ht]
  rw [← Finset.sum_mul, Finset.sum_add_distrib, noiseWeight_sum, noise_coordinate_sign]
  ring

/-- Exact honest acceptance for the actual three-bit test. -/
theorem testAcceptance_dictator (ε : ℝ) (π : J → I)
    (i : I) (j : J) (hπ : π j = i) :
    testAcceptance ε π (fun f => f i) (fun g => g j) = 1 - ε := by
  have hg (f : Cube I) (μ : Cube J) :
      (𝔼 g : Cube J, if f i ^^ g j ^^ (thirdQuery π f g μ) j then (0 : ℝ) else 1) =
        if μ j then 0 else 1 := by
    calc
      _ = 𝔼 _g : Cube J, if μ j then (0 : ℝ) else 1 := by
        apply Finset.expect_congr rfl
        intro g _
        rw [dictator_test_parity π i j hπ f g μ]
      _ = _ := Fintype.expect_const _
  change (𝔼 f : Cube I, ∑ μ : Cube J, noiseWeight ε μ *
    (𝔼 g : Cube J, if f i ^^ g j ^^ (thirdQuery π f g μ) j then (0 : ℝ) else 1)) = _
  simp_rw [hg]
  rw [Fintype.expect_const]
  exact noise_coordinate_false ε j

/-- Storing an honest dictator in the actual half-table representation gives
the same acceptance after applying the explicit folding correction. -/
theorem testAcceptance_folded_dictators (ε : ℝ) (π : J → I)
    (i₀ i : I) (j₀ j : J) (hπ : π j = i) :
    testAcceptance ε π (foldedAnswer i₀ (fun h => h.val i))
      (foldedAnswer j₀ (fun h => h.val j)) = 1 - ε := by
  have hA : foldedAnswer i₀ (fun h => h.val i) = (fun f : Cube I => f i) :=
    funext (foldedAnswer_dictator i₀ i)
  have hB : foldedAnswer j₀ (fun h => h.val j) = (fun g : Cube J => g j) :=
    funext (foldedAnswer_dictator j₀ j)
  rw [hA, hB]
  exact testAcceptance_dictator ε π i j hπ

/-- Honest valid local assignments remain dictators after both conditioning
and folding, so the concrete conditioned tables have the same completeness. -/
theorem testAcceptance_conditioned_dictators (ε : ℝ) (π : J → I)
    (validI : I → Bool) (validJ : J → Bool)
    (i₀ i : {i : I // validI i = true}) (j₀ j : {j : J // validJ j = true})
    (hπ : π j.val = i.val) :
    testAcceptance ε π
      (conditionedFoldedAnswer validI i₀ (fun h => h.val i))
      (conditionedFoldedAnswer validJ j₀ (fun h => h.val j)) = 1 - ε := by
  have hA : conditionedFoldedAnswer validI i₀ (fun h => h.val i) =
      (fun f : Cube I => f i.val) :=
    funext (conditionedFoldedAnswer_dictator validI i₀ i)
  have hB : conditionedFoldedAnswer validJ j₀ (fun h => h.val j) =
      (fun g : Cube J => g j.val) :=
    funext (conditionedFoldedAnswer_dictator validJ j₀ j)
  rw [hA, hB]
  exact testAcceptance_dictator ε π i.val j.val hπ

theorem testAcceptance_folded_conditioned_dictators (ε : ℝ) (π : J → I)
    (i₀ i : I) (valid : J → Bool)
    (j₀ j : {j : J // valid j = true}) (hπ : π j.val = i) :
    testAcceptance ε π (foldedAnswer i₀ (fun h => h.val i))
      (conditionedFoldedAnswer valid j₀ (fun h => h.val j)) = 1 - ε := by
  have hA : foldedAnswer i₀ (fun h => h.val i) = (fun f : Cube I => f i) :=
    funext (foldedAnswer_dictator i₀ i)
  have hB : conditionedFoldedAnswer valid j₀ (fun h => h.val j) =
      (fun g : Cube J => g j.val) :=
    funext (conditionedFoldedAnswer_dictator valid j₀ j)
  rw [hA, hB]
  exact testAcceptance_dictator ε π i j.val hπ

/-- The actual test using one uniform `Fin D` tape entry per noise coordinate. -/
def realizedTestAcceptance (D : Nat) (π : J → I)
    (A : Cube I → Bool) (B : Cube J → Bool) : ℝ :=
  𝔼 f : Cube I, 𝔼 z : J → Fin D, 𝔼 g : Cube J,
    if A f ^^ B g ^^ B (thirdQuery π f g (realizedNoise z)) then 0 else 1

/-- Exact equality between the finite uniform tape and the weighted product
noise test; no distributional acceptance premise is assumed. -/
theorem realizedTestAcceptance_eq_testAcceptance {D : Nat} (positive : 0 < D)
    (π : J → I) (A : Cube I → Bool) (B : Cube J → Bool) :
    realizedTestAcceptance D π A B = testAcceptance ((D : ℝ)⁻¹) π A B := by
  unfold realizedTestAcceptance testAcceptance
  apply Finset.expect_congr rfl
  intro f _
  exact expect_realizedNoise positive
    (fun μ => 𝔼 g : Cube J, if A f ^^ B g ^^ B (thirdQuery π f g μ) then 0 else 1)

/-- Exact honest completeness of the uniformly sampled finite-tape test. -/
theorem realizedTestAcceptance_dictator {D : Nat} (positive : 0 < D)
    (π : J → I) (i : I) (j : J) (hπ : π j = i) :
    realizedTestAcceptance D π (fun f => f i) (fun g => g j) = 1 - (D : ℝ)⁻¹ := by
  rw [realizedTestAcceptance_eq_testAcceptance positive]
  exact testAcceptance_dictator _ π i j hπ

theorem realizedTestAcceptance_folded_dictators {D : Nat} (positive : 0 < D)
    (π : J → I) (i₀ i : I) (j₀ j : J) (hπ : π j = i) :
    realizedTestAcceptance D π (foldedAnswer i₀ (fun h => h.val i))
      (foldedAnswer j₀ (fun h => h.val j)) = 1 - (D : ℝ)⁻¹ := by
  rw [realizedTestAcceptance_eq_testAcceptance positive]
  exact testAcceptance_folded_dictators _ π i₀ i j₀ j hπ

theorem realizedTestAcceptance_conditioned_dictators {D : Nat} (positive : 0 < D)
    (π : J → I) (validI : I → Bool) (validJ : J → Bool)
    (i₀ i : {i : I // validI i = true}) (j₀ j : {j : J // validJ j = true})
    (hπ : π j.val = i.val) :
    realizedTestAcceptance D π
      (conditionedFoldedAnswer validI i₀ (fun h => h.val i))
      (conditionedFoldedAnswer validJ j₀ (fun h => h.val j)) = 1 - (D : ℝ)⁻¹ := by
  rw [realizedTestAcceptance_eq_testAcceptance positive]
  exact testAcceptance_conditioned_dictators _ π validI validJ i₀ i j₀ j hπ

theorem realizedTestAcceptance_folded_conditioned_dictators {D : Nat} (positive : 0 < D)
    (π : J → I) (i₀ i : I) (valid : J → Bool)
    (j₀ j : {j : J // valid j = true}) (hπ : π j.val = i) :
    realizedTestAcceptance D π (foldedAnswer i₀ (fun h => h.val i))
      (conditionedFoldedAnswer valid j₀ (fun h => h.val j)) = 1 - (D : ℝ)⁻¹ := by
  rw [realizedTestAcceptance_eq_testAcceptance positive]
  exact testAcceptance_folded_conditioned_dictators _ π i₀ i valid j₀ j hπ

end UniqueGamesTheorem.Foundations.Hastad

end

end

section

noncomputable section

namespace UniqueGamesTheorem.Foundations.Hastad.SourceTape

open scoped BigOperators
open UniqueGamesTheorem.Reduction.FiniteNoise

/-- Two full Boolean query tables and one finite noise entry per right index. -/
abbrev TestTape (I J : Type*) (D : ℕ) :=
  Cube I × ((J → Fin D) × Cube J)

abbrev FairTestTape (I J : Type*) (D : ℕ) := TestTape I J D × Bool

section Expectations

variable {X Y : Type*} [Fintype X] [Fintype Y]

theorem expect_prod (H : X × Y → ℝ) :
    (𝔼 p : X × Y, H p) = 𝔼 x : X, 𝔼 y : Y, H (x, y) := by
  simpa only [Finset.univ_product_univ] using
    (Finset.expect_product (Finset.univ : Finset X) (Finset.univ : Finset Y) H)

end Expectations

section Tape

variable {I J : Type*} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J] {D : ℕ}

theorem card_testTape :
    Fintype.card (TestTape I J D) =
      2 ^ Fintype.card I * (D ^ Fintype.card J * 2 ^ Fintype.card J) := by
  simp [TestTape, Cube]

theorem card_fairTestTape :
    Fintype.card (FairTestTape I J D) =
      (2 ^ Fintype.card I * (D ^ Fintype.card J * 2 ^ Fintype.card J)) * 2 := by
  rw [Fintype.card_prod, card_testTape]
  rfl

theorem expect_testTape (H : TestTape I J D → ℝ) :
    (𝔼 t : TestTape I J D, H t) =
      𝔼 f : Cube I, 𝔼 z : J → Fin D, 𝔼 g : Cube J, H (f, z, g) := by
  rw [expect_prod]
  apply Finset.expect_congr rfl
  intro f _
  exact expect_prod _

/-- Any explicit finite enumeration equivalence preserves the exact tape law. -/
theorem expect_equivTape {E : Type*} [Fintype E]
    (e : E ≃ TestTape I J D) (H : TestTape I J D → ℝ) :
    (𝔼 s : E, H (e s)) = 𝔼 t : TestTape I J D, H t :=
  Fintype.expect_equiv e _ _ (fun _ => rfl)

theorem expect_fairTestTape (H : FairTestTape I J D → ℝ) :
    (𝔼 t : FairTestTape I J D, H t) =
      𝔼 t : TestTape I J D, (H (t, false) + H (t, true)) / 2 := by
  rw [expect_prod]
  apply Finset.expect_congr rfl
  intro t _
  rw [Fintype.expect_eq_sum_div_card]
  simp [add_comm]

theorem expect_fairTestTape_ignore (H : TestTape I J D → ℝ) :
    (𝔼 t : FairTestTape I J D, H t.1) = 𝔼 t : TestTape I J D, H t := by
  rw [expect_prod]
  simp only [Fintype.expect_const]

/-- The three actual query tables read from a uniform finite tape. -/
def tapeQueries (π : J → I) (t : TestTape I J D) : Cube I × Cube J × Cube J :=
  (t.1, t.2.2, thirdQuery π t.1 t.2.2 (realizedNoise t.2.1))

/-- Exact joint law of all three queries, for every real-valued observable. -/
theorem expect_tapeQueries (positive : 0 < D) (π : J → I)
    (H : Cube I × Cube J × Cube J → ℝ) :
    (𝔼 t : TestTape I J D, H (tapeQueries π t)) =
      𝔼 f : Cube I, ∑ μ : Cube J, noiseWeight ((D : ℝ)⁻¹) μ *
        (𝔼 g : Cube J, H (f, g, thirdQuery π f g μ)) := by
  rw [expect_testTape]
  apply Finset.expect_congr rfl
  intro f _
  exact expect_realizedNoise positive
    (fun μ => 𝔼 g : Cube J, H (f, g, thirdQuery π f g μ))

def tapeAcceptance (D : ℕ) (π : J → I)
    (A : Cube I → Bool) (B : Cube J → Bool) : ℝ :=
  𝔼 t : TestTape I J D,
    if A t.1 ^^ B t.2.2 ^^ B (thirdQuery π t.1 t.2.2 (realizedNoise t.2.1))
      then 0 else 1

theorem tapeAcceptance_eq_realizedTestAcceptance (D : ℕ) (π : J → I)
    (A : Cube I → Bool) (B : Cube J → Bool) :
    tapeAcceptance D π A B = realizedTestAcceptance D π A B :=
  expect_testTape _

theorem tapeAcceptance_eq_testAcceptance (positive : 0 < D) (π : J → I)
    (A : Cube I → Bool) (B : Cube J → Bool) :
    tapeAcceptance D π A B = testAcceptance ((D : ℝ)⁻¹) π A B := by
  rw [tapeAcceptance_eq_realizedTestAcceptance,
    realizedTestAcceptance_eq_testAcceptance positive]

theorem tapeAcceptance_eq_sum_div_card (D : ℕ) (π : J → I)
    (A : Cube I → Bool) (B : Cube J → Bool) :
    tapeAcceptance D π A B =
      (∑ t : TestTape I J D,
        if A t.1 ^^ B t.2.2 ^^ B (thirdQuery π t.1 t.2.2 (realizedNoise t.2.1))
          then (0 : ℝ) else 1) / Fintype.card (TestTape I J D) :=
  Fintype.expect_eq_sum_div_card _

end Tape

section Restriction

variable {X Λ : Type*}

def restrictFunction (P : X → Prop) (f : X → Λ) : {x : X // P x} → Λ :=
  fun x => f x.val

/-- Uniform full functions push forward to uniform functions on any subtype.
Nonempty values ensure that the unused coordinates can be filled. -/
theorem expect_restrictFunction [Fintype X] [DecidableEq X] [Fintype Λ] [Nonempty Λ]
    (P : X → Prop) [DecidablePred P] (H : ({x : X // P x} → Λ) → ℝ) :
    (𝔼 f : X → Λ, H (restrictFunction P f)) =
      𝔼 g : {x : X // P x} → Λ, H g := by
  classical
  calc
    _ = 𝔼 p : ({x : X // P x} → Λ) × ({x : X // ¬ P x} → Λ), H p.1 :=
      Fintype.expect_equiv (Equiv.piEquivPiSubtypeProd P (fun _ => Λ)) _ _
        (fun _ => rfl)
    _ = _ := by
      rw [expect_prod]
      simp only [Fintype.expect_const]

variable {I J : Type*}

def restrictTape (P : I → Prop) (Q : J → Prop) {D : ℕ}
    (t : TestTape I J D) : TestTape {i : I // P i} {j : J // Q j} D :=
  (restrictFunction P t.1, restrictFunction Q t.2.1, restrictFunction Q t.2.2)

theorem expect_restrictTape [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
    (P : I → Prop) (Q : J → Prop) [DecidablePred P] [DecidablePred Q]
    {D : ℕ} (positive : 0 < D)
    (H : TestTape {i : I // P i} {j : J // Q j} D → ℝ) :
    (𝔼 t : TestTape I J D, H (restrictTape P Q t)) =
      𝔼 t : TestTape {i : I // P i} {j : J // Q j} D, H t := by
  let : Nonempty (Fin D) := ⟨⟨0, positive⟩⟩
  rw [expect_testTape, expect_testTape]
  change (𝔼 f : Cube I, 𝔼 z : J → Fin D, 𝔼 g : Cube J,
    H (restrictFunction P f, restrictFunction Q z, restrictFunction Q g)) = _
  have hg (f : Cube I) (z : J → Fin D) :
      (𝔼 g : Cube J,
        H (restrictFunction P f, restrictFunction Q z, restrictFunction Q g)) =
      𝔼 g : Cube {j : J // Q j}, H (restrictFunction P f, restrictFunction Q z, g) :=
    expect_restrictFunction (Λ := Bool) Q
      (fun g => H (restrictFunction P f, restrictFunction Q z, g))
  simp_rw [hg]
  have hz (f : Cube I) :
      (𝔼 z : J → Fin D, 𝔼 g : Cube {j : J // Q j},
        H (restrictFunction P f, restrictFunction Q z, g)) =
      𝔼 z : {j : J // Q j} → Fin D, 𝔼 g : Cube {j : J // Q j},
        H (restrictFunction P f, z, g) :=
    expect_restrictFunction (Λ := Fin D) Q
      (fun z => 𝔼 g : Cube {j : J // Q j}, H (restrictFunction P f, z, g))
  simp_rw [hz]
  exact expect_restrictFunction (Λ := Bool) P
    (fun f => 𝔼 z : {j : J // Q j} → Fin D, 𝔼 g : Cube {j : J // Q j}, H (f, z, g))

def restrictedProjection (P : I → Prop) (Q : J → Prop) (π : J → I)
    (hπ : ∀ j, Q j → P (π j)) : {j : J // Q j} → {i : I // P i} :=
  fun j => ⟨π j.val, hπ j.val j.property⟩

theorem restrict_realizedNoise (Q : J → Prop) {D : ℕ} (z : J → Fin D) :
    restrictFunction Q (realizedNoise z) = realizedNoise (restrictFunction Q z) := rfl

theorem restrict_thirdQuery (P : I → Prop) (Q : J → Prop) (π : J → I)
    (hπ : ∀ j, Q j → P (π j)) (f : Cube I) (g μ : Cube J) :
    restrictFunction Q (thirdQuery π f g μ) =
      thirdQuery (restrictedProjection P Q π hπ)
        (restrictFunction P f) (restrictFunction Q g) (restrictFunction Q μ) := rfl

/-- The contextual three-query law is the same joint law as sampling directly
on the contextual domains, whenever the contextual projection is defined. -/
theorem expect_restricted_queries [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
    (P : I → Prop) (Q : J → Prop) [DecidablePred P] [DecidablePred Q]
    (π : J → I) (hπ : ∀ j, Q j → P (π j)) {D : ℕ} (positive : 0 < D)
    (H : Cube {i : I // P i} × Cube {j : J // Q j} × Cube {j : J // Q j} → ℝ) :
    (𝔼 t : TestTape I J D,
      H (restrictFunction P t.1, restrictFunction Q t.2.2,
        restrictFunction Q (thirdQuery π t.1 t.2.2 (realizedNoise t.2.1)))) =
    𝔼 t : TestTape {i : I // P i} {j : J // Q j} D,
      H (tapeQueries (restrictedProjection P Q π hπ) t) := by
  exact expect_restrictTape P Q positive
    (fun t => H (tapeQueries (restrictedProjection P Q π hπ) t))

def restrictRightTape (Q : J → Prop) {D : ℕ} (t : TestTape I J D) :
    TestTape I {j : J // Q j} D :=
  (t.1, restrictFunction Q t.2.1, restrictFunction Q t.2.2)

theorem expect_restrictRightTape [Fintype I] [DecidableEq I]
    [Fintype J] [DecidableEq J] (Q : J → Prop) [DecidablePred Q]
    {D : ℕ} (positive : 0 < D) (H : TestTape I {j : J // Q j} D → ℝ) :
    (𝔼 t : TestTape I J D, H (restrictRightTape Q t)) =
      𝔼 t : TestTape I {j : J // Q j} D, H t := by
  let : Nonempty (Fin D) := ⟨⟨0, positive⟩⟩
  rw [expect_testTape, expect_testTape]
  apply Finset.expect_congr rfl
  intro f _
  change (𝔼 z : J → Fin D, 𝔼 g : Cube J,
    H (f, restrictFunction Q z, restrictFunction Q g)) = _
  have hg (z : J → Fin D) :
      (𝔼 g : Cube J, H (f, restrictFunction Q z, restrictFunction Q g)) =
      𝔼 g : Cube {j : J // Q j}, H (f, restrictFunction Q z, g) :=
    expect_restrictFunction (Λ := Bool) Q (fun g => H (f, restrictFunction Q z, g))
  simp_rw [hg]
  exact expect_restrictFunction (Λ := Fin D) Q
    (fun z => 𝔼 g : Cube {j : J // Q j}, H (f, z, g))

/-- Joint contextual law with the full left domain unchanged. No compatibility
premise is needed: the right projection is simply restricted to valid indices. -/
theorem expect_rightRestricted_queries [Fintype I] [DecidableEq I]
    [Fintype J] [DecidableEq J] (Q : J → Prop) [DecidablePred Q]
    (π : J → I) {D : ℕ} (positive : 0 < D)
    (H : Cube I × Cube {j : J // Q j} × Cube {j : J // Q j} → ℝ) :
    (𝔼 t : TestTape I J D,
      H (t.1, restrictFunction Q t.2.2,
        restrictFunction Q (thirdQuery π t.1 t.2.2 (realizedNoise t.2.1)))) =
    𝔼 t : TestTape I {j : J // Q j} D,
      H (tapeQueries (fun j => π j.val) t) := by
  exact expect_restrictRightTape Q positive
    (fun t => H (tapeQueries (fun j => π j.val) t))

end Restriction

end UniqueGamesTheorem.Foundations.Hastad.SourceTape

end

end

section

noncomputable section
namespace UniqueGamesTheorem.Foundations.Hastad.SourceGame

open scoped BigOperators
open Target PCP Games SourceContexts

theorem event_nonempty (F : Formula) (hne : F.clauses ≠ []) :
    Nonempty (RandomEvent F) :=
  ⟨(⟨0, List.length_pos_iff.mpr hne⟩, .first)⟩

def eventLaw (F : Formula) (hne : F.clauses ≠ []) :
    FiniteDistribution (RandomEvent F) := by
  let : Nonempty (RandomEvent F) := event_nonempty F hne
  exact FiniteDistribution.uniform _

def visibleQuestion (F : Formula) (e : RandomEvent F) :
    Fin F.variables × Fin F.clauses.length :=
  (nameAt (clauseAt F e.1) e.2, e.1)

def baseGame (F : Formula) (hne : F.clauses ≠ []) :
    Game (Fin F.variables) (Fin F.clauses.length) Bool ClauseAnswer where
  questions := (eventLaw F hne).pushforward (visibleQuestion F)
  accepts := baseAccepts F

@[simp] theorem baseGame_accepts (F : Formula) (hne : F.clauses ≠ [])
    (v : Fin F.variables) (c : Fin F.clauses.length) (i : Bool) (j : ClauseAnswer) :
    (baseGame F hne).accepts v c i j = baseAccepts F v c i j := rfl

theorem eventLaw_probability (F : Formula) (hne : F.clauses ≠ [])
    (P : RandomEvent F → Bool) :
    (eventLaw F hne).probability P =
      (∑ e : RandomEvent F, if P e then (1 : ℝ) else 0) /
        (3 * F.clauses.length : ℕ) := by
  classical
  simp only [eventLaw, FiniteDistribution.uniform, FiniteDistribution.probability]
  simp_rw [div_eq_mul_inv]
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro e _
  cases P e <;> simp [RandomEvent, Fintype.card_prod, card_slot, Nat.mul_comm]

theorem sum_slots (H : Slot → ℝ) :
    (∑ s : Slot, H s) = H .first + H .second + H .third := by
  have hu : (Finset.univ : Finset Slot) = {.first, .second, .third} := by
    ext s
    cases s <;> simp
  rw [hu]
  simp only [Finset.sum_insert, Finset.mem_insert, Finset.mem_singleton,
    reduceCtorEq, or_self, not_false_eq_true, Finset.sum_singleton]
  ring

theorem sum_slot_accepts (F : Formula) (alice : AliceStrategy F)
    (bob : BobStrategy F) (c : Fin F.clauses.length) :
    (∑ s : Slot, if accepts F alice bob (c,s) then (1 : ℝ) else 0) =
      (acceptedSlots (clauseAt F c) (alice c)
        (honestAnswer (clauseAt F c) bob) : ℕ) := by
  rw [sum_slots]
  by_cases hs : localSatisfies (clauseAt F c) (alice c) = true
  · by_cases h₁ : (alice c).first = bob (clauseAt F c)[0].variableIndex <;>
      by_cases h₂ : (alice c).second = bob (clauseAt F c)[1].variableIndex <;>
      by_cases h₃ : (alice c).third = bob (clauseAt F c)[2].variableIndex <;>
      norm_num [accepts, hs, acceptedSlots, matchingSlots, honestAnswer, answerAt, nameAt,
        h₁, h₂, h₃]
  · simp [accepts, acceptedSlots, hs]

theorem failureCount_eq_sum_map (F : Formula) (bob : BobStrategy F)
    (cs : List (Fin F.clauses.length)) :
    failureCount F bob cs =
      (cs.map (fun c => clauseFailure (clauseAt F c) bob)).sum := by
  induction cs with
  | nil => rfl
  | cons c cs ih => simp only [failureCount, List.map_cons, List.sum_cons, ih]

theorem failureCount_allIndices (F : Formula) (bob : BobStrategy F) :
    failureCount F bob (allIndices F) =
      ∑ c : Fin F.clauses.length, clauseFailure (clauseAt F c) bob := by
  rw [failureCount_eq_sum_map]
  unfold allIndices
  rw [← List.sum_toFinset _ (List.nodup_finRange _), List.toFinset_finRange]

/-- The local three-slot rejection inequality controls the actual uniform
incidence law, including repeated variable names and repeated clauses. -/
theorem verifier_probability_plus_failure (F : Formula) (hne : F.clauses ≠ [])
    (alice : AliceStrategy F) (bob : BobStrategy F) :
    (eventLaw F hne).probability (accepts F alice bob) +
      (failureCount F bob (allIndices F) : ℝ) / (3 * F.clauses.length : ℕ) ≤ 1 := by
  have hm : (0 : ℝ) < (3 * F.clauses.length : ℕ) := by
    exact_mod_cast Nat.mul_pos (by decide : 0 < 3) (List.length_pos_iff.mpr hne)
  have hlocal (c : Fin F.clauses.length) :
      (∑ s : Slot, if accepts F alice bob (c,s) then (1 : ℝ) else 0) +
        (clauseFailure (clauseAt F c) bob : ℝ) ≤ 3 := by
    rw [sum_slot_accepts]
    exact_mod_cast local_rejection_bound (clauseAt F c) (alice c) bob
  have hsum := Finset.sum_le_sum (fun c (_ : c ∈ (Finset.univ : Finset _)) => hlocal c)
  simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul] at hsum
  rw [eventLaw_probability, failureCount_allIndices]
  push_cast
  push_cast at hm
  rw [Fintype.sum_prod_type, ← add_div]
  apply (div_le_one hm).mpr
  simpa only [Nat.cast_mul, Nat.cast_ofNat, mul_comm] using hsum

theorem base_success_le_verifier (F : Formula) (hne : F.clauses ≠ [])
    (strategy : Strategy (Fin F.variables) (Fin F.clauses.length) Bool ClauseAnswer) :
    (baseGame F hne).success strategy ≤
      (eventLaw F hne).probability (accepts F strategy.2 strategy.1) := by
  unfold Game.success baseGame
  rw [FiniteDistribution.probability_pushforward]
  apply FiniteDistribution.probability_mono
  intro e he
  exact baseAccepts_implies_sampled F e.1 e.2 _ _ he

/-- A concrete clause-count gap supplies the base-game value bound. -/
theorem base_value_le_of_clause_gap (F : Formula) (hne : F.clauses ≠ [])
    (δ : ℝ) (hgap : ∀ bob : BobStrategy F,
      δ * F.clauses.length ≤ (failureCount F bob (allIndices F) : ℝ)) :
    (baseGame F hne).value ≤ 1 - δ / 3 := by
  apply (Game.value_le_iff _ _).mpr
  intro strategy
  have hbase := base_success_le_verifier F hne strategy
  have hprob := verifier_probability_plus_failure F hne strategy.2 strategy.1
  have hm : (0 : ℝ) < F.clauses.length :=
    Nat.cast_pos.mpr (List.length_pos_iff.mpr hne)
  have hg : δ / 3 ≤ (failureCount F strategy.1 (allIndices F) : ℝ) /
      (3 * F.clauses.length : ℕ) := by
    have hden : (0 : ℝ) < (3 * F.clauses.length : ℕ) := by
      exact_mod_cast Nat.mul_pos (by decide : 0 < 3) (List.length_pos_iff.mpr hne)
    apply (le_div_iff₀ hden).mpr
    calc
      δ / 3 * (3 * F.clauses.length : ℕ) = δ * F.clauses.length := by push_cast; ring
      _ ≤ _ := hgap strategy.1
  linarith

theorem pushforward_comp {X Y Z : Type*} [Fintype X] [Fintype Y] [Fintype Z]
    (μ : FiniteDistribution X) (f : X → Y) (g : Y → Z) :
    (μ.pushforward f).pushforward g = μ.pushforward (g ∘ f) := by
  classical
  apply FiniteDistribution.eq_of_weight_eq
  intro z
  simp only [FiniteDistribution.pushforward]
  calc
    _ = ∑ y : Y, ∑ x : X, if f x = y then
        (if g y = z then μ.weight x else 0) else 0 := by
      apply Finset.sum_congr rfl
      intro y _
      by_cases h : g y = z <;> simp [h]
    _ = _ := by rw [Finset.sum_comm]; simp

theorem expectation_pushforward {X Y : Type*} [Fintype X] [Fintype Y]
    (μ : FiniteDistribution X) (f : X → Y) (H : Y → ℝ) :
    (μ.pushforward f).expectation H = μ.expectation (H ∘ f) := by
  classical
  simp only [FiniteDistribution.expectation, FiniteDistribution.pushforward,
    Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x _
  simp [ite_mul]

def repeatedVisible (F : Formula) (u : ℕ) (events : Fin u → RandomEvent F) :
    VariableContext F u × ClauseContext F u :=
  (fun t => nameAt (clauseAt F (events t).1) (events t).2,
   fun t => (events t).1)

/-- This identifies the repeated game law with the actual uniformly sampled
incidence tuples, retaining all collisions of their visible questions. -/
theorem repeated_questions (F : Formula) (hne : F.clauses ≠ []) (u : ℕ) :
    ((baseGame F hne).repetition u).questions =
      ((eventLaw F hne).iid u).pushforward (repeatedVisible F u) := by
  change (((eventLaw F hne).pushforward (visibleQuestion F)).iid u).transport
    (Game.tupleQuestionEquiv u) = _
  rw [FiniteDistribution.iid_pushforward, ← FiniteDistribution.pushforward_equiv,
    pushforward_comp]
  rfl

theorem repeated_expectation (F : Formula) (hne : F.clauses ≠ []) (u : ℕ)
    (H : VariableContext F u × ClauseContext F u → ℝ) :
    ((baseGame F hne).repetition u).questions.expectation H =
      𝔼 events : Fin u → RandomEvent F, H (repeatedVisible F u events) := by
  let : Nonempty (RandomEvent F) := event_nonempty F hne
  rw [repeated_questions, expectation_pushforward]
  change ((FiniteDistribution.uniform (RandomEvent F)).iid u).expectation _ = _
  rw [FiniteDistribution.iid_uniform, FiniteDistribution.expectation_uniform,
    Fintype.expect_eq_sum_div_card]
  rfl

/-- The concrete constructor enumerates clause tuples and slot tuples as
separate lexicographic factors; this is exactly the same question law. -/
theorem repeated_expectation_split (F : Formula) (hne : F.clauses ≠ []) (u : ℕ)
    (H : VariableContext F u × ClauseContext F u → ℝ) :
    ((baseGame F hne).repetition u).questions.expectation H =
      𝔼 c : ClauseContext F u, 𝔼 s : SlotContext u,
        H (sampledVariables F c s, c) := by
  rw [repeated_expectation]
  calc
    _ = 𝔼 p : ClauseContext F u × SlotContext u,
        H (sampledVariables F p.1 p.2, p.1) :=
      Fintype.expect_equiv
        (Game.tupleQuestionEquiv (Q₁ := Fin F.clauses.length) (Q₂ := Slot) u)
        _ _ (fun _ => rfl)
    _ = _ := SourceTape.expect_prod _

def sourceProjectionGame (F : Formula) (hne : F.clauses ≠ []) (u : ℕ) :
    Game (VariableContext F u) (ClauseContext F u) (I u) (J u) :=
  projectionGame ((baseGame F hne).repetition u).questions
    (fun v c => pi F c v) (validJ F)

/-- The projection game has exactly the repeated question law, and its
legal right answers satisfy every coordinate of the original game. -/
theorem projection_value_le_repetition (F : Formula) (hne : F.clauses ≠ [])
    (u : ℕ) :
    (sourceProjectionGame F hne u).value ≤ ((baseGame F hne).repetition u).value := by
  apply (Game.value_le_iff _ _).mpr
  intro strategy
  have h : (sourceProjectionGame F hne u).success strategy ≤
      ((baseGame F hne).repetition u).success strategy := by
    apply FiniteDistribution.probability_mono
    intro q hq
    have hlegal : pi F q.2 q.1 (strategy.2 q.2) = strategy.1 q.1 ∧
        validJ F q.2 (strategy.2 q.2) = true := by
      simpa only [Game.wins, sourceProjectionGame, projectionGame,
        decide_eq_true_eq] using hq
    apply (Game.repetition_accepts_iff _ _ _ _ _ _).mpr
    intro t
    exact projection_implies_coordinate_accepts F q.2 q.1
      (strategy.1 q.1) (strategy.2 q.2) hlegal.2 hlegal.1 t
  exact h.trans (Game.success_le_value _ strategy)

theorem source_acceptance_le (F : Formula) (hne : F.clauses ≠ []) (u : ℕ)
    (ε δ : ℝ) (i₀ : VariableContext F u → I u)
    (tableA : ∀ v, HalfCube (i₀ v) → Bool)
    (right : ∀ c : ClauseContext F u, ConditionedOracle (validJ F c))
    (hε : 0 < ε) (hε' : ε ≤ 1 / 2) (hδ : 0 ≤ δ)
    (hvalue : ((baseGame F hne).repetition u).value ≤ 4 * ε * δ ^ 2) :
    (𝔼 events : Fin u → RandomEvent F,
      questionAcceptance ε (fun v c => pi F c v)
        (fun v => foldedAnswer (i₀ v) (tableA v)) (fun c => (right c).answer)
        (repeatedVisible F u events)) ≤ (1 + δ) / 2 := by
  rw [← repeated_expectation F hne u]
  exact conditionedOracle_acceptance_bound _ ε δ _ (validJ F) i₀ tableA
    (fun _ => default) right hε hε' hδ
    ((projection_value_le_repetition F hne u).trans hvalue)

theorem source_acceptance_le_split (F : Formula) (hne : F.clauses ≠ []) (u : ℕ)
    (ε δ : ℝ) (i₀ : VariableContext F u → I u)
    (tableA : ∀ v, HalfCube (i₀ v) → Bool)
    (right : ∀ c : ClauseContext F u, ConditionedOracle (validJ F c))
    (hε : 0 < ε) (hε' : ε ≤ 1 / 2) (hδ : 0 ≤ δ)
    (hvalue : ((baseGame F hne).repetition u).value ≤ 4 * ε * δ ^ 2) :
    (𝔼 c : ClauseContext F u, 𝔼 s : SlotContext u,
      testAcceptance ε (pi F c (sampledVariables F c s))
        (foldedAnswer (i₀ (sampledVariables F c s)) (tableA (sampledVariables F c s)))
        (right c).answer) ≤ (1 + δ) / 2 := by
  have h := conditionedOracle_acceptance_bound
    ((baseGame F hne).repetition u).questions ε δ (fun v c => pi F c v)
    (validJ F) i₀ tableA (fun _ => default) right hε hε' hδ
    ((projection_value_le_repetition F hne u).trans hvalue)
  rw [repeated_expectation_split] at h
  exact h

end UniqueGamesTheorem.Foundations.Hastad.SourceGame

end

end

end OAI
