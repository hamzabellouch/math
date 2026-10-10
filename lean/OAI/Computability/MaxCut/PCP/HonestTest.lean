import Mathlib
import OAI.Computability.MaxCut.PCP.ClauseVerifier
import OAI.Computability.MaxCut.PCP.Folding
import OAI.Computability.MaxCut.Games.FiniteNoise

namespace OAI

/-! Honest completeness of the actual three-query test. Compatible coordinate
dictators cancel the two uniform query tables, leaving exactly one noise bit.
The finite-tape form uses the proved product-noise pushforward law. -/

noncomputable section

namespace MaxCutGames.Foundations.Hastad

open scoped BigOperators
open MaxCutGames.Reduction.FiniteNoise

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

end MaxCutGames.Foundations.Hastad

namespace MaxCutGames.Foundations.Hastad.SourceTape

open scoped BigOperators
open MaxCutGames.Reduction.FiniteNoise

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

end MaxCutGames.Foundations.Hastad.SourceTape

end

namespace MaxCutGames.Foundations.Hastad.SourceContexts

open Target PCP

/-- Executable tuple encoding of the eight clause answers. -/
def clauseAnswerEquiv : ClauseAnswer ≃ Bool × Bool × Bool where
  toFun a := (a.first, a.second, a.third)
  invFun a := ⟨a.1, a.2.1, a.2.2⟩
  left_inv a := by cases a; rfl
  right_inv a := by rcases a with ⟨a, b, c⟩; rfl

def clauseAnswerFinEquiv : ClauseAnswer ≃ Fin 8 :=
  clauseAnswerEquiv.trans
    ((Equiv.prodCongr finTwoEquiv.symm
      (Equiv.prodCongr finTwoEquiv.symm finTwoEquiv.symm)).trans
      ((Equiv.prodCongr (Equiv.refl (Fin 2)) finProdFinEquiv).trans finProdFinEquiv))

instance clauseAnswerFintype : Fintype ClauseAnswer :=
  Fintype.ofEquiv (Bool × Bool × Bool) clauseAnswerEquiv.symm

instance clauseAnswerInhabited : Inhabited ClauseAnswer := ⟨⟨false, false, false⟩⟩

instance slotFintype : Fintype Slot where
  elems := {.first, .second, .third}
  complete s := by cases s <;> simp

instance slotInhabited : Inhabited Slot := ⟨.first⟩

@[simp] theorem card_clauseAnswer : Fintype.card ClauseAnswer = 8 := by
  rw [Fintype.card_congr clauseAnswerFinEquiv]
  rfl

@[simp] theorem card_slot : Fintype.card Slot = 3 := by decide

abbrev I (u : ℕ) := Fin u → Bool
abbrev J (u : ℕ) := Fin u → ClauseAnswer
abbrev ClauseContext (F : Formula) (u : ℕ) := Fin u → Fin F.clauses.length
abbrev VariableContext (F : Formula) (u : ℕ) := Fin u → Fin F.«variables»
abbrev SlotContext (u : ℕ) := Fin u → Slot

@[simp] theorem card_I (u : ℕ) : Fintype.card (I u) = 2 ^ u := by simp [I]
@[simp] theorem card_J (u : ℕ) : Fintype.card (J u) = 8 ^ u := by simp [J]
@[simp] theorem card_ClauseContext (F : Formula) (u : ℕ) :
    Fintype.card (ClauseContext F u) = F.clauses.length ^ u := by simp [ClauseContext]
@[simp] theorem card_VariableContext (F : Formula) (u : ℕ) :
    Fintype.card (VariableContext F u) = F.«variables» ^ u := by simp [VariableContext]
@[simp] theorem card_SlotContext (u : ℕ) :
    Fintype.card (SlotContext u) = 3 ^ u := by simp [SlotContext]

def localConsistent {n : ℕ} (clause : Clause n) (answer : ClauseAnswer) : Bool :=
  decide (∀ s s' : Slot, nameAt clause s = nameAt clause s' →
    answerAt answer s = answerAt answer s')

@[simp] theorem localConsistent_eq_true_iff {n : ℕ}
    (clause : Clause n) (answer : ClauseAnswer) :
    localConsistent clause answer = true ↔
      ∀ s s' : Slot, nameAt clause s = nameAt clause s' →
        answerAt answer s = answerAt answer s' := by
  simp [localConsistent]

/-- Satisfaction and consistency over all `3*u` occurrence slots. -/
def validJ (F : Formula) {u : ℕ} (c : ClauseContext F u) (j : J u) : Bool :=
  decide ((∀ t, localSatisfies (clauseAt F (c t)) (j t) = true) ∧
    ∀ t t' s s', nameAt (clauseAt F (c t)) s = nameAt (clauseAt F (c t')) s' →
      answerAt (j t) s = answerAt (j t') s')

@[simp] theorem validJ_eq_true_iff (F : Formula) {u : ℕ}
    (c : ClauseContext F u) (j : J u) :
    validJ F c j = true ↔
      (∀ t, localSatisfies (clauseAt F (c t)) (j t) = true) ∧
      ∀ t t' s s', nameAt (clauseAt F (c t)) s = nameAt (clauseAt F (c t')) s' →
        answerAt (j t) s = answerAt (j t') s' := by
  simp [validJ]

theorem validJ_satisfies (F : Formula) {u : ℕ} (c : ClauseContext F u)
    (j : J u) (hj : validJ F c j = true) (t : Fin u) :
    localSatisfies (clauseAt F (c t)) (j t) = true :=
  ((validJ_eq_true_iff F c j).mp hj).1 t

theorem validJ_consistent (F : Formula) {u : ℕ} (c : ClauseContext F u)
    (j : J u) (hj : validJ F c j = true) (t : Fin u) (s : Slot)
    (t' : Fin u) (s' : Slot)
    (hname : nameAt (clauseAt F (c t)) s = nameAt (clauseAt F (c t')) s') :
    answerAt (j t) s = answerAt (j t') s' :=
  ((validJ_eq_true_iff F c j).mp hj).2 t t' s s' hname

theorem validJ_localConsistent (F : Formula) {u : ℕ} (c : ClauseContext F u)
    (j : J u) (hj : validJ F c j = true) (t : Fin u) :
    localConsistent (clauseAt F (c t)) (j t) = true := by
  apply (localConsistent_eq_true_iff _ _).mpr
  intro s s' hs
  exact validJ_consistent F c j hj t s t s' hs

/-- First matching visible occurrence, with the third slot as an off-support
default. Its inputs contain no hidden incidence choice. -/
def canonicalSlot {n : ℕ} (clause : Clause n) (v : Fin n) : Slot :=
  if nameAt clause .first = v then .first
  else if nameAt clause .second = v then .second else .third

theorem canonicalSlot_name {n : ℕ} (clause : Clause n) (v : Fin n)
    (hv : ∃ s, nameAt clause s = v) : nameAt clause (canonicalSlot clause v) = v := by
  by_cases hfirst : nameAt clause .first = v
  · simp [canonicalSlot, hfirst]
  by_cases hsecond : nameAt clause .second = v
  · simp [canonicalSlot, hfirst, hsecond]
  obtain ⟨s, hs⟩ := hv
  cases s with
  | first => exact False.elim (hfirst hs)
  | second => exact False.elim (hsecond hs)
  | third => simpa [canonicalSlot, hfirst, hsecond] using hs

def pi (F : Formula) {u : ℕ} (c : ClauseContext F u) (v : VariableContext F u)
    (j : J u) : I u :=
  fun t => answerAt (j t) (canonicalSlot (clauseAt F (c t)) (v t))

def sampledVariables (F : Formula) {u : ℕ} (c : ClauseContext F u)
    (s : SlotContext u) : VariableContext F u :=
  fun t => nameAt (clauseAt F (c t)) (s t)

theorem sampledVariables_supported (F : Formula) {u : ℕ}
    (c : ClauseContext F u) (s : SlotContext u) :
    ∀ t, ∃ slot, nameAt (clauseAt F (c t)) slot = sampledVariables F c s t :=
  fun t => ⟨s t, rfl⟩

theorem sampled_eq_pi (F : Formula) {u : ℕ} (c : ClauseContext F u)
    (v : VariableContext F u) (j : J u) (hj : validJ F c j = true)
    (t : Fin u) (s : Slot) (hs : nameAt (clauseAt F (c t)) s = v t) :
    answerAt (j t) s = pi F c v j t := by
  exact validJ_consistent F c j hj t s t
    (canonicalSlot (clauseAt F (c t)) (v t))
    (hs.trans (canonicalSlot_name _ _ ⟨s, hs⟩).symm)

/-- Two hidden choices with the same visible variable tuple give the same
selected answers for every valid label. -/
theorem sampled_answers_eq_of_visible_eq (F : Formula) {u : ℕ}
    (c : ClauseContext F u) (s s' : SlotContext u) (j : J u)
    (hj : validJ F c j = true)
    (hvisible : sampledVariables F c s = sampledVariables F c s') :
    (fun t => answerAt (j t) (s t)) = fun t => answerAt (j t) (s' t) := by
  funext t
  exact validJ_consistent F c j hj t (s t) t (s' t) (congrFun hvisible t)

def honestJ (F : Formula) {u : ℕ} (c : ClauseContext F u)
    (assignment : Fin F.«variables» → Bool) : J u :=
  fun t => honestAnswer (clauseAt F (c t)) assignment

def honestI (F : Formula) {u : ℕ} (v : VariableContext F u)
    (assignment : Fin F.«variables» → Bool) : I u :=
  fun t => assignment (v t)

theorem honestJ_valid (F : Formula) {u : ℕ} (c : ClauseContext F u)
    (assignment : Fin F.«variables» → Bool)
    (hs : ∀ clause ∈ F.clauses, clause.eval assignment = true) :
    validJ F c (honestJ F c assignment) = true := by
  apply (validJ_eq_true_iff F c _).mpr
  constructor
  · intro t
    exact (honest_satisfies _ assignment).trans (hs _ (List.getElem_mem _))
  · intro t t' s s' hname
    simp only [honestJ, honest_answerAt]
    exact congrArg assignment hname

theorem pi_honest (F : Formula) {u : ℕ} (c : ClauseContext F u)
    (v : VariableContext F u) (assignment : Fin F.«variables» → Bool)
    (hsupport : ∀ t, ∃ s, nameAt (clauseAt F (c t)) s = v t) :
    pi F c v (honestJ F c assignment) = honestI F v assignment := by
  funext t
  exact (honest_answerAt _ assignment _).trans
    (congrArg assignment (canonicalSlot_name _ _ (hsupport t)))

theorem pi_honest_sampled (F : Formula) {u : ℕ} (c : ClauseContext F u)
    (s : SlotContext u) (assignment : Fin F.«variables» → Bool) :
    pi F c (sampledVariables F c s) (honestJ F c assignment) =
      honestI F (sampledVariables F c s) assignment :=
  pi_honest F c _ assignment (sampledVariables_supported F c s)

def baseAccepts (F : Formula) (v : Fin F.«variables») (c : Fin F.clauses.length)
    (i : Bool) (j : ClauseAnswer) : Bool :=
  decide (localSatisfies (clauseAt F c) j = true ∧
    localConsistent (clauseAt F c) j = true ∧
    answerAt j (canonicalSlot (clauseAt F c) v) = i)

@[simp] theorem baseAccepts_eq_true_iff (F : Formula) (v : Fin F.«variables»)
    (c : Fin F.clauses.length) (i : Bool) (j : ClauseAnswer) :
    baseAccepts F v c i j = true ↔
      localSatisfies (clauseAt F c) j = true ∧
      localConsistent (clauseAt F c) j = true ∧
      answerAt j (canonicalSlot (clauseAt F c) v) = i := by
  simp [baseAccepts]

theorem projection_implies_coordinate_accepts (F : Formula) {u : ℕ}
    (c : ClauseContext F u) (v : VariableContext F u) (i : I u) (j : J u)
    (hj : validJ F c j = true) (hpi : pi F c v j = i) (t : Fin u) :
    baseAccepts F (v t) (c t) (i t) (j t) = true := by
  exact (baseAccepts_eq_true_iff F _ _ _ _).mpr
    ⟨validJ_satisfies F c j hj t, validJ_localConsistent F c j hj t, congrFun hpi t⟩

theorem baseAccepts_implies_sampled (F : Formula) (c : Fin F.clauses.length)
    (s : Slot) (i : Bool) (j : ClauseAnswer)
    (h : baseAccepts F (nameAt (clauseAt F c) s) c i j = true) :
    (localSatisfies (clauseAt F c) j && decide (answerAt j s = i)) = true := by
  obtain ⟨hsat, hcons, heq⟩ := (baseAccepts_eq_true_iff F _ _ _ _).mp h
  have hname := canonicalSlot_name (clauseAt F c) (nameAt (clauseAt F c) s) ⟨s, rfl⟩
  have hans := (localConsistent_eq_true_iff _ _).mp hcons s
    (canonicalSlot (clauseAt F c) (nameAt (clauseAt F c) s)) hname.symm
  simp [hsat, hans.trans heq]

/-- Every coordinate of the original repeated clause-slot verifier accepts
the decoded answers. Each answer tuple may depend on its whole private context. -/
theorem projection_implies_sampled_accepts (F : Formula) {u : ℕ}
    (c : ClauseContext F u) (s : SlotContext u) (i : I u) (j : J u)
    (hj : validJ F c j = true) (hpi : pi F c (sampledVariables F c s) j = i) :
    ∀ t, (localSatisfies (clauseAt F (c t)) (j t) &&
      decide (answerAt (j t) (s t) = i t)) = true := by
  intro t
  exact baseAccepts_implies_sampled F (c t) (s t) (i t) (j t)
    (projection_implies_coordinate_accepts F c _ i j hj hpi t)

end MaxCutGames.Foundations.Hastad.SourceContexts

end OAI
