import Mathlib
import OAI.Computability.MinUncut.PCP.Folding
import OAI.Computability.MinUncut.Games.FiniteNoise

namespace OAI

noncomputable section

namespace MinUncutGames.Foundations.Hastad

open scoped BigOperators
open MinUncutGames.Reduction.FiniteNoise

variable {I J : Type*} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]

omit [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J] in

theorem dictator_test_parity (π : J → I) (i : I) (j : J) (hπ : π j = i)
    (f : Cube I) (g μ : Cube J) :
    (f i ^^ g j ^^ (thirdQuery π f g μ) j) = μ j := by
  simp only [thirdQuery, cubeXor, hπ]
  cases f i <;> cases g j <;> cases μ j <;> rfl

theorem noise_coordinate_sign (ε : ℝ) (j : J) :
    (∑ μ : Cube J, noiseWeight ε μ * bitSign (μ j)) = 1 - 2 * ε := by
  have hs : support (coordinateMask j) = {j} := by
    ext k
    simp [support, coordinateMask]
  have h := noise_walsh ε (coordinateMask j)
  simp_rw [walsh_symm (coordinateMask j), walsh_coordinateMask] at h
  simpa only [hs, Finset.card_singleton, pow_one] using h

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

def realizedTestAcceptance (D : Nat) (π : J → I)
    (A : Cube I → Bool) (B : Cube J → Bool) : ℝ :=
  𝔼 f : Cube I, 𝔼 z : J → Fin D, 𝔼 g : Cube J,
    if A f ^^ B g ^^ B (thirdQuery π f g (realizedNoise z)) then 0 else 1

theorem realizedTestAcceptance_eq_testAcceptance {D : Nat} (positive : 0 < D)
    (π : J → I) (A : Cube I → Bool) (B : Cube J → Bool) :
    realizedTestAcceptance D π A B = testAcceptance ((D : ℝ)⁻¹) π A B := by
  unfold realizedTestAcceptance testAcceptance
  apply Finset.expect_congr rfl
  intro f _
  exact expect_realizedNoise positive
    (fun μ => 𝔼 g : Cube J, if A f ^^ B g ^^ B (thirdQuery π f g μ) then 0 else 1)

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

end MinUncutGames.Foundations.Hastad

namespace MinUncutGames.Foundations.Hastad.SourceTape

open scoped BigOperators
open MinUncutGames.Reduction.FiniteNoise

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

def tapeQueries (π : J → I) (t : TestTape I J D) : Cube I × Cube J × Cube J :=
  (t.1, t.2.2, thirdQuery π t.1 t.2.2 (realizedNoise t.2.1))

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

end MinUncutGames.Foundations.Hastad.SourceTape

end

end OAI
