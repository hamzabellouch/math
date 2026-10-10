import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.List.FinRange
import Mathlib.Logic.Equiv.Prod
import OAI.Computability.BinPacking.Information.EmptyContext
import OAI.Computability.BinPacking.PCP.SourceEncoding
import OAI.Computability.BinPacking.Reductions.FiniteNoise

namespace OAI

noncomputable section

namespace BinPackingGames.Foundations.Hastad

open scoped BigOperators
open BinPackingGames.Reduction.FiniteNoise

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

end BinPackingGames.Foundations.Hastad

namespace BinPackingGames.Foundations.Hastad.SourceTape

open scoped BigOperators
open BinPackingGames.Reduction.FiniteNoise

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

end BinPackingGames.Foundations.Hastad.SourceTape

namespace BinPackingGames.Foundations.Hastad.SourceOccurrences

open BinPackingGames.Reduction.CloneGap
open scoped BigOperators

structure Encoding (α : Type) where
  size : ℕ
  code : α ≃ Fin size

namespace Encoding

def fin (n : ℕ) : Encoding (Fin n) := ⟨n, Equiv.refl _⟩
def bool : Encoding Bool := ⟨2, finTwoEquiv.symm⟩
def unit : Encoding Unit := ⟨1, finOneEquiv.symm⟩

def prod {α β : Type} (a : Encoding α) (b : Encoding β) : Encoding (α × β) :=
  ⟨a.size * b.size, (Equiv.prodCongr a.code b.code).trans finProdFinEquiv⟩

def sum {α β : Type} (a : Encoding α) (b : Encoding β) : Encoding (α ⊕ β) :=
  ⟨a.size + b.size, (Equiv.sumCongr a.code b.code).trans finSumFinEquiv⟩

def function {α β : Type} (a : Encoding α) (b : Encoding β) : Encoding (α → β) where
  size := b.size ^ a.size
  code := (show (α → β) ≃ (Fin a.size → Fin b.size) from
    { toFun := fun f i => b.code (f (a.code.symm i))
      invFun := fun f x => b.code.symm (f (a.code x))
      left_inv := by intro f; funext x; simp
      right_inv := by intro f; funext i; simp }).trans finFunctionFinEquiv

def enumerate {α : Type} (a : Encoding α) : List α := List.ofFn a.code.symm

@[simp] theorem length_enumerate {α : Type} (a : Encoding α) :
    a.enumerate.length = a.size := by simp [enumerate]

theorem mem_enumerate {α : Type} (a : Encoding α) (x : α) : x ∈ a.enumerate := by
  rw [enumerate, List.mem_ofFn']
  exact ⟨a.code x, a.code.symm_apply_apply x⟩

theorem nodup_enumerate {α : Type} (a : Encoding α) : a.enumerate.Nodup :=
  List.nodup_ofFn_ofInjective a.code.symm.injective

theorem card_eq_size {α : Type} [Fintype α] (a : Encoding α) :
    Fintype.card α = a.size := by
  simpa only [Fintype.card_fin] using Fintype.card_congr a.code

end Encoding

abbrev GlobalKey (V C I J : Type) := (V × Cube I) ⊕ ((C × Cube J) ⊕ Unit)

def globalEncoding {V C I J : Type}
    (v : Encoding V) (c : Encoding C) (i : Encoding I) (j : Encoding J) :
    Encoding (GlobalKey V C I J) :=
  (v.prod (i.function Encoding.bool)).sum
    ((c.prod (j.function Encoding.bool)).sum Encoding.unit)

@[simp] theorem globalEncoding_size {V C I J : Type}
    (v : Encoding V) (c : Encoding C) (i : Encoding I) (j : Encoding J) :
    (globalEncoding v c i j).size =
      v.size * 2 ^ i.size + (c.size * 2 ^ j.size + 1) := rfl

def extendRestricted {J : Type} (valid : J → Bool)
    (f : Cube {j : J // valid j = true}) : Cube J :=
  fun j => if h : valid j = true then f ⟨j, h⟩ else false

@[simp] theorem extendRestricted_valid {J : Type} (valid : J → Bool)
    (f : Cube {j : J // valid j = true}) (j : {j : J // valid j = true}) :
    extendRestricted valid f j.val = f j := by simp [extendRestricted, j.property]

theorem extendRestricted_injective {J : Type} (valid : J → Bool) :
    Function.Injective (extendRestricted valid) := by
  intro f g h
  funext j
  have := congrFun h j.val
  simpa only [extendRestricted_valid] using this

@[simp] theorem restrictQuery_extendRestricted {J : Type} (valid : J → Bool)
    (f : Cube {j : J // valid j = true}) :
    restrictQuery valid (extendRestricted valid f) = f := by
  funext j
  exact extendRestricted_valid valid f j

@[simp] theorem canonicalInput_half {I : Type} [Fintype I] [DecidableEq I]
    (i₀ : I) (f : HalfCube i₀) :
    canonicalInput i₀ f.val = f := by
  apply Subtype.ext
  simp [canonicalInput, representative, f.property]

def assignmentOfKey {V C I J : Type}
    (v : Encoding V) (c : Encoding C) (i : Encoding I) (j : Encoding J)
    (bits : GlobalKey V C I J → Bool) : Fin (globalEncoding v c i j).size → Bool :=
  fun q => bits ((globalEncoding v c i j).code.symm q)

@[simp] theorem assignmentOfKey_code {V C I J : Type}
    (v : Encoding V) (c : Encoding C) (i : Encoding I) (j : Encoding J)
    (bits : GlobalKey V C I J → Bool) (key : GlobalKey V C I J) :
    assignmentOfKey v c i j bits ((globalEncoding v c i j).code key) = bits key := by
  exact congrArg bits ((globalEncoding v c i j).code.symm_apply_apply key)

theorem assignmentOfKey_surjective {V C I J : Type}
    (v : Encoding V) (c : Encoding C) (i : Encoding I) (j : Encoding J) :
    Function.Surjective (assignmentOfKey v c i j) := by
  intro bits
  refine ⟨fun key => bits ((globalEncoding v c i j).code key), ?_⟩
  funext q
  exact congrArg bits ((globalEncoding v c i j).code.apply_symm_apply q)

section LocalEquations

variable {V C I J : Type} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]

def localAddress (vE : Encoding V) (cE : Encoding C) (iE : Encoding I) (jE : Encoding J)
    (v : V) (c : C) (valid : J → Bool) (i₀ : I) (j₀ : {j : J // valid j = true}) :
    FoldedEquation.Address i₀ j₀ → Fin (globalEncoding vE cE iE jE).size
  | .inl f => (globalEncoding vE cE iE jE).code (.inl (v, f.val))
  | .inr g => (globalEncoding vE cE iE jE).code (.inr (.inl (c, extendRestricted valid g.val)))

omit [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J] in
theorem localAddress_injective
    (vE : Encoding V) (cE : Encoding C) (iE : Encoding I) (jE : Encoding J)
    (v : V) (c : C) (valid : J → Bool) (i₀ : I) (j₀ : {j : J // valid j = true}) :
    Function.Injective (localAddress vE cE iE jE v c valid i₀ j₀) := by
  intro a b h
  cases a with
  | inl a =>
    cases b with
    | inl b =>
      have h' := (globalEncoding vE cE iE jE).code.injective h
      have hval : a.val = b.val := congrArg Prod.snd (Sum.inl.inj h')
      exact congrArg Sum.inl (Subtype.ext hval)
    | inr b =>
      have h' := (globalEncoding vE cE iE jE).code.injective h
      cases h'
  | inr a =>
    cases b with
    | inl b =>
      have h' := (globalEncoding vE cE iE jE).code.injective h
      cases h'
    | inr b =>
      have h' := (globalEncoding vE cE iE jE).code.injective h
      have hext := congrArg Prod.snd (Sum.inl.inj (Sum.inr.inj h'))
      exact congrArg Sum.inr (Subtype.ext (extendRestricted_injective valid hext))

def conditionedOccurrence
    (vE : Encoding V) (cE : Encoding C) (iE : Encoding I) (jE : Encoding J)
    (v : V) (c : C) (valid : J → Bool) (π : J → I)
    (i₀ : I) (j₀ : {j : J // valid j = true}) (f : Cube I) (g μ : Cube J) :
    Equation (Fin (globalEncoding vE cE iE jE).size) :=
  mapEquation (localAddress vE cE iE jE v c valid i₀ j₀)
    (FoldedEquation.conditionedEquation valid π i₀ j₀ f g μ)

omit [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J] in
theorem conditionedOccurrence_satisfied
    (vE : Encoding V) (cE : Encoding C) (iE : Encoding I) (jE : Encoding J)
    (v : V) (c : C) (valid : J → Bool) (π : J → I)
    (i₀ : I) (j₀ : {j : J // valid j = true})
    (bits : Fin (globalEncoding vE cE iE jE).size → Bool)
    (f : Cube I) (g μ : Cube J) :
    satisfied (conditionedOccurrence vE cE iE jE v c valid π i₀ j₀ f g μ) bits =
      !(foldedAnswer i₀ (fun h => bits ((globalEncoding vE cE iE jE).code (.inl (v, h.val)))) f ^^
        conditionedFoldedAnswer valid j₀
          (fun h => bits ((globalEncoding vE cE iE jE).code
            (.inr (.inl (c, extendRestricted valid h.val))))) g ^^
        conditionedFoldedAnswer valid j₀
          (fun h => bits ((globalEncoding vE cE iE jE).code
            (.inr (.inl (c, extendRestricted valid h.val))))) (thirdQuery π f g μ)) := by
  rw [conditionedOccurrence, satisfied_mapEquation]
  let tableA : HalfCube i₀ → Bool :=
    fun h => bits ((globalEncoding vE cE iE jE).code (.inl (v, h.val)))
  let tableB : HalfCube j₀ → Bool :=
    fun h => bits ((globalEncoding vE cE iE jE).code
      (.inr (.inl (c, extendRestricted valid h.val))))
  have hbits : bits ∘ localAddress vE cE iE jE v c valid i₀ j₀ =
      FoldedEquation.storedAssignment tableA tableB := by
    funext a
    cases a <;> rfl
  rw [hbits]
  exact FoldedEquation.conditionedEquation_satisfied valid π i₀ j₀ tableA tableB f g μ

end LocalEquations

def findValid {J : Type} (valid : J → Bool) : List J → Option {j : J // valid j = true}
  | [] => none
  | j :: rest => if h : valid j = true then some ⟨j, h⟩ else findValid valid rest

theorem findValid_none_iff {J : Type} (valid : J → Bool) (xs : List J) :
    findValid valid xs = none ↔ ∀ j ∈ xs, valid j = false := by
  induction xs with
  | nil => simp [findValid]
  | cons j xs ih =>
    by_cases hj : valid j = true
    · simp [findValid, hj]
    · simp [findValid, hj, ih]

def firstValid {J : Type} (e : Encoding J) (valid : J → Bool) :
    Option {j : J // valid j = true} := findValid valid e.enumerate

theorem firstValid_none_iff {J : Type} (e : Encoding J) (valid : J → Bool) :
    firstValid e valid = none ↔ ∀ j, valid j = false := by
  rw [firstValid, findValid_none_iff]
  exact ⟨fun h j => h j (e.mem_enumerate j), fun h j _ => h j⟩

def occurrenceList {Tape Name : Type} (tape : Encoding Tape)
    (emit : Tape → Equation Name) : List (Equation Name) := tape.enumerate.map emit

@[simp] theorem occurrenceList_length {Tape Name : Type} (tape : Encoding Tape)
    (emit : Tape → Equation Name) : (occurrenceList tape emit).length = tape.size := by
  simp [occurrenceList]

private theorem countP_cast_eq_sum {α : Type} (xs : List α) (p : α → Bool) :
    (xs.countP p : ℝ) = (xs.map (fun x => if p x then (1 : ℝ) else 0)).sum := by
  induction xs with
  | nil => simp
  | cons x xs ih => cases hp : p x <;> simp [hp, ih, add_comm]

theorem countP_enumerate {Tape : Type} [Fintype Tape]
    (tape : Encoding Tape) (p : Tape → Bool) :
    (tape.enumerate.countP p : ℝ) = ∑ x, if p x then (1 : ℝ) else 0 := by
  rw [countP_cast_eq_sum]
  simp only [Encoding.enumerate, List.map_ofFn, List.sum_ofFn]
  exact Fintype.sum_equiv tape.code.symm _ _ (fun _ => rfl)

theorem occurrenceList_acceptance {Tape Name : Type} [Fintype Tape]
    (tape : Encoding Tape) (emit : Tape → Equation Name) (bits : Name → Bool) :
    ((occurrenceList tape emit).countP (fun e => satisfied e bits) : ℝ) /
        (occurrenceList tape emit).length =
      𝔼 x, if satisfied (emit x) bits then (1 : ℝ) else 0 := by
  rw [occurrenceList_length, Fintype.expect_eq_sum_div_card, tape.card_eq_size]
  congr 1
  simpa only [occurrenceList, List.countP_map, Function.comp_def] using
    countP_enumerate tape (fun x => satisfied (emit x) bits)

open SourceContexts
open BinPackingGames.Reduction.FiniteNoise

def clauseAnswerEncoding : Encoding PCP.ClauseAnswer := ⟨8, clauseAnswerFinEquiv⟩

def slotEncoding : Encoding PCP.Slot where
  size := 3
  code :=
    { toFun := fun s => match s with | .first => 0 | .second => 1 | .third => 2
      invFun := fun i => if i.val = 0 then .first else if i.val = 1 then .second else .third
      left_inv := by intro s; cases s <;> rfl
      right_inv := by decide }

def iEncoding (u : ℕ) : Encoding (I u) := (Encoding.fin u).function Encoding.bool
def jEncoding (u : ℕ) : Encoding (J u) := (Encoding.fin u).function clauseAnswerEncoding
def variableEncoding (F : Target.Formula) (u : ℕ) : Encoding (VariableContext F u) :=
  (Encoding.fin u).function (Encoding.fin F.variables)
def clauseEncoding (F : Target.Formula) (u : ℕ) : Encoding (ClauseContext F u) :=
  (Encoding.fin u).function (Encoding.fin F.clauses.length)
def slotContextEncoding (u : ℕ) : Encoding (SlotContext u) :=
  (Encoding.fin u).function slotEncoding

def proofEncoding (F : Target.Formula) (u : ℕ) :
    Encoding (GlobalKey (VariableContext F u) (ClauseContext F u) (I u) (J u)) :=
  globalEncoding (variableEncoding F u) (clauseEncoding F u) (iEncoding u) (jEncoding u)

def nBits (F : Target.Formula) (u : ℕ) : ℕ := (proofEncoding F u).size

@[simp] theorem nBits_eq (F : Target.Formula) (u : ℕ) :
    nBits F u = F.variables ^ u * 2 ^ (2 ^ u) +
      (F.clauses.length ^ u * 2 ^ (8 ^ u) + 1) := rfl

def dummyIndex (F : Target.Formula) (u : ℕ) : Fin (nBits F u) :=
  (proofEncoding F u).code (.inr (.inr ()))

def leftAnchor (u : ℕ) : I u := fun _ => false

def rightAnchor (F : Target.Formula) {u : ℕ} (c : ClauseContext F u) :
    Option {j : J u // validJ F c j = true} := firstValid (jEncoding u) (validJ F c)

theorem rightAnchor_none_iff (F : Target.Formula) {u : ℕ} (c : ClauseContext F u) :
    rightAnchor F c = none ↔ ∀ j : J u, validJ F c j = false :=
  firstValid_none_iff _ _

def halfTableKeyAssignment (F : Target.Formula) (u : ℕ)
    (a : VariableContext F u → HalfCube (leftAnchor u) → Bool)
    (b : ∀ c : ClauseContext F u, ∀ j₀ : {j : J u // validJ F c j = true},
      HalfCube j₀ → Bool) :
    GlobalKey (VariableContext F u) (ClauseContext F u) (I u) (J u) → Bool
  | .inl (v, f) => a v (canonicalInput (leftAnchor u) f)
  | .inr (.inl (c, g)) =>
    match rightAnchor F c with
    | none => false
    | some j₀ => b c j₀ (canonicalInput j₀ (restrictQuery (validJ F c) g))
  | .inr (.inr _) => false

def extendHalfTables (F : Target.Formula) (u : ℕ)
    (a : VariableContext F u → HalfCube (leftAnchor u) → Bool)
    (b : ∀ c : ClauseContext F u, ∀ j₀ : {j : J u // validJ F c j = true},
      HalfCube j₀ → Bool) : Fin (nBits F u) → Bool :=
  assignmentOfKey (variableEncoding F u) (clauseEncoding F u) (iEncoding u) (jEncoding u)
    (halfTableKeyAssignment F u a b)

@[simp] theorem extendHalfTables_left (F : Target.Formula) (u : ℕ)
    (a : VariableContext F u → HalfCube (leftAnchor u) → Bool)
    (b : ∀ c : ClauseContext F u, ∀ j₀ : {j : J u // validJ F c j = true},
      HalfCube j₀ → Bool) (v : VariableContext F u) (h : HalfCube (leftAnchor u)) :
    extendHalfTables F u a b ((proofEncoding F u).code (.inl (v, h.val))) = a v h := by
  calc
    _ = halfTableKeyAssignment F u a b (.inl (v, h.val)) :=
      assignmentOfKey_code (variableEncoding F u) (clauseEncoding F u) (iEncoding u)
        (jEncoding u) (halfTableKeyAssignment F u a b) (.inl (v, h.val))
    _ = a v h := congrArg (a v) (canonicalInput_half (leftAnchor u) h)

theorem extendHalfTables_right (F : Target.Formula) (u : ℕ)
    (a : VariableContext F u → HalfCube (leftAnchor u) → Bool)
    (b : ∀ c : ClauseContext F u, ∀ j₀ : {j : J u // validJ F c j = true},
      HalfCube j₀ → Bool) (c : ClauseContext F u)
    (j₀ : {j : J u // validJ F c j = true}) (hanchor : rightAnchor F c = some j₀)
    (h : HalfCube j₀) :
    extendHalfTables F u a b ((proofEncoding F u).code
      (.inr (.inl (c, extendRestricted (validJ F c) h.val)))) = b c j₀ h := by
  calc
    _ = halfTableKeyAssignment F u a b
        (.inr (.inl (c, extendRestricted (validJ F c) h.val))) :=
      assignmentOfKey_code (variableEncoding F u) (clauseEncoding F u) (iEncoding u)
        (jEncoding u) (halfTableKeyAssignment F u a b) _
    _ = b c j₀ h := by
      simp only [halfTableKeyAssignment, hanchor]
      rw [restrictQuery_extendRestricted, canonicalInput_half]

def emptyAddress (F : Target.Formula) (u : ℕ) (v : VariableContext F u) :
    EmptyContext.Address (leftAnchor u) → Fin (nBits F u)
  | .inl h => (proofEncoding F u).code (.inl (v, h.val))
  | .inr _ => dummyIndex F u

def contextEquation (F : Target.Formula) (u D : ℕ)
    (c : ClauseContext F u) (v : VariableContext F u)
    (t : SourceTape.TestTape (I u) (J u) D) : Equation (Fin (nBits F u)) :=
  match rightAnchor F c with
  | none => mapEquation (emptyAddress F u v) (EmptyContext.equation (leftAnchor u) t.1)
  | some j₀ => conditionedOccurrence (variableEncoding F u) (clauseEncoding F u)
      (iEncoding u) (jEncoding u) v c (validJ F c) (pi F c v) (leftAnchor u) j₀
      t.1 t.2.2 (realizedNoise t.2.1)

def leftResponse (F : Target.Formula) (u : ℕ) (bits : Fin (nBits F u) → Bool)
    (v : VariableContext F u) : Cube (I u) → Bool :=
  foldedAnswer (leftAnchor u) (fun h => bits ((proofEncoding F u).code (.inl (v, h.val))))

def rightResponse (F : Target.Formula) (u : ℕ) (bits : Fin (nBits F u) → Bool)
    (c : ClauseContext F u) : Cube (J u) → Bool :=
  match rightAnchor F c with
  | none => fun _ => false
  | some j₀ => conditionedFoldedAnswer (validJ F c) j₀
      (fun h => bits ((proofEncoding F u).code (.inr (.inl (c, extendRestricted (validJ F c) h.val)))))

theorem contextEquation_satisfied (F : Target.Formula) (u D : ℕ)
    (c : ClauseContext F u) (v : VariableContext F u)
    (t : SourceTape.TestTape (I u) (J u) D) (bits : Fin (nBits F u) → Bool) :
    satisfied (contextEquation F u D c v t) bits =
      !(leftResponse F u bits v t.1 ^^ rightResponse F u bits c t.2.2 ^^
        rightResponse F u bits c (thirdQuery (pi F c v) t.1 t.2.2 (realizedNoise t.2.1))) := by
  cases ha : rightAnchor F c with
  | none =>
    simp only [contextEquation, ha, satisfied_mapEquation, EmptyContext.equation_satisfied,
      rightResponse, Bool.xor_false]
    rfl
  | some j₀ =>
    simp only [contextEquation, ha, rightResponse]
    exact conditionedOccurrence_satisfied (variableEncoding F u) (clauseEncoding F u)
      (iEncoding u) (jEncoding u) v c (validJ F c) (pi F c v) (leftAnchor u) j₀
      bits t.1 t.2.2 (realizedNoise t.2.1)

def testTapeEncoding (u D : ℕ) : Encoding (SourceTape.TestTape (I u) (J u) D) :=
  ((iEncoding u).function Encoding.bool).prod
    (((jEncoding u).function (Encoding.fin D)).prod ((jEncoding u).function Encoding.bool))

abbrev SourceIndex (F : Target.Formula) (u D : ℕ) :=
  (ClauseContext F u × SlotContext u) × SourceTape.TestTape (I u) (J u) D

def sourceIndexEncoding (F : Target.Formula) (u D : ℕ) : Encoding (SourceIndex F u D) :=
  ((clauseEncoding F u).prod (slotContextEncoding u)).prod (testTapeEncoding u D)

def sourceEquation (F : Target.Formula) (u D : ℕ) (p : SourceIndex F u D) :
    Equation (Fin (nBits F u)) :=
  contextEquation F u D p.1.1 (sampledVariables F p.1.1 p.1.2) p.2

def rawSourceList (F : Target.Formula) (u D : ℕ) : List (Equation (Fin (nBits F u))) :=
  occurrenceList (sourceIndexEncoding F u D) (sourceEquation F u D)

@[simp] theorem rawSourceList_length (F : Target.Formula) (u D : ℕ) :
    (rawSourceList F u D).length =
      (F.clauses.length ^ u * 3 ^ u) *
        (2 ^ (2 ^ u) * (D ^ (8 ^ u) * 2 ^ (8 ^ u))) := by
  rw [rawSourceList, occurrenceList_length]
  rfl

theorem rawSourceList_acceptance (F : Target.Formula) (u D : ℕ)
    (hD : 0 < D) (bits : Fin (nBits F u) → Bool) :
    ((rawSourceList F u D).countP (fun e => satisfied e bits) : ℝ) /
        (rawSourceList F u D).length =
      𝔼 c : ClauseContext F u, 𝔼 s : SlotContext u,
        testAcceptance ((D : ℝ)⁻¹) (pi F c (sampledVariables F c s))
          (leftResponse F u bits (sampledVariables F c s)) (rightResponse F u bits c) := by
  rw [rawSourceList, occurrenceList_acceptance, SourceTape.expect_prod]
  rw [SourceTape.expect_prod]
  apply Finset.expect_congr rfl
  intro c _
  apply Finset.expect_congr rfl
  intro s _
  rw [← SourceTape.tapeAcceptance_eq_testAcceptance hD]
  unfold SourceTape.tapeAcceptance
  apply Finset.expect_congr rfl
  intro t _
  rw [sourceEquation, contextEquation_satisfied]
  cases h : leftResponse F u bits (sampledVariables F c s) t.1 ^^
    rightResponse F u bits c t.2.2 ^^
      rightResponse F u bits c
        (thirdQuery (pi F c (sampledVariables F c s)) t.1 t.2.2 (realizedNoise t.2.1)) <;> rfl

def emptyFormulaEquation (F : Target.Formula) (u : ℕ) : Equation (Fin (nBits F u)) :=
  ⟨dummyIndex F u, dummyIndex F u, dummyIndex F u, false⟩

def sourceList (F : Target.Formula) (u D : ℕ) : List (Equation (Fin (nBits F u))) :=
  if F.clauses.isEmpty then [emptyFormulaEquation F u] else rawSourceList F u D

theorem sourceList_empty (F : Target.Formula) (u D : ℕ) (h : F.clauses = []) :
    sourceList F u D = [emptyFormulaEquation F u] := by simp [sourceList, h]

theorem sourceList_nonempty (F : Target.Formula) (u D : ℕ) (h : F.clauses ≠ []) :
    sourceList F u D = rawSourceList F u D := by
  unfold sourceList
  rw [List.isEmpty_eq_false_iff.mpr h]
  rfl

theorem sourceList_length_le_raw_add_one (F : Target.Formula) (u D : ℕ) :
    (sourceList F u D).length ≤ (rawSourceList F u D).length + 1 := by
  by_cases h : F.clauses = []
  · rw [sourceList_empty F u D h]
    rw [List.length_singleton]
    omega
  · rw [sourceList_nonempty F u D h]
    omega

theorem sourceList_ne_nil (F : Target.Formula) (u D : ℕ) (hD : 0 < D) :
    sourceList F u D ≠ [] := by
  by_cases h : F.clauses = []
  · rw [sourceList_empty F u D h]
    simp
  · rw [sourceList_nonempty F u D h]
    apply List.length_pos_iff.mp
    rw [rawSourceList_length]
    have hc : 0 < F.clauses.length := List.length_pos_iff.mpr h
    positivity

def sourceInput (F : Target.Formula) (u D : ℕ) (hD : 0 < D) :
    BinPackingGames.Reduction.SourceEncoding.Input :=
  ⟨nBits F u, sourceList F u D, sourceList_ne_nil F u D hD⟩

theorem emptyFormulaEquation_satisfied (F : Target.Formula) (u : ℕ)
    (bits : Fin (nBits F u) → Bool) :
    satisfied (emptyFormulaEquation F u) bits = !(bits (dummyIndex F u)) := by
  cases h : bits (dummyIndex F u) <;> simp [emptyFormulaEquation, satisfied, h]

end BinPackingGames.Foundations.Hastad.SourceOccurrences

namespace BinPackingGames.Foundations.Hastad.SourceGame

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

end BinPackingGames.Foundations.Hastad.SourceGame

namespace BinPackingGames.Foundations.Hastad.SourceHonest

open BinPackingGames.Reduction.CloneGap
open BinPackingGames.Reduction.FiniteNoise
open scoped BigOperators

def taggedAssignment {V C I J : Type} (left : V → I) (right : C → J) :
    (V × Cube I) ⊕ ((C × Cube J) ⊕ Unit) → Bool
  | .inl (v, f) => f (left v)
  | .inr (.inl (c, g)) => g (right c)
  | .inr (.inr _) => false

@[simp] theorem taggedAssignment_left {V C I J : Type}
    (left : V → I) (right : C → J) (v : V) (f : Cube I) :
    taggedAssignment left right (.inl (v, f)) = f (left v) := rfl

@[simp] theorem taggedAssignment_right {V C I J : Type}
    (left : V → I) (right : C → J) (c : C) (g : Cube J) :
    taggedAssignment left right (.inr (.inl (c, g))) = g (right c) := rfl

theorem taggedAssignment_right_restriction {V C I J : Type}
    (left : V → I) (right : C → J) (c : C) (valid : J → Bool)
    (honest : {j : J // valid j = true}) (hright : right c = honest.val)
    (extend : Cube {j : J // valid j = true} → Cube J)
    (hextend : ∀ (g : Cube {j : J // valid j = true})
      (j : {j : J // valid j = true}), extend g j.val = g j)
    (j₀ : {j : J // valid j = true}) (h : HalfCube j₀) :
    taggedAssignment left right (.inr (.inl (c, extend h.val))) = h.val honest := by
  change extend h.val (right c) = h.val honest
  rw [hright]
  exact hextend h.val honest

section Local

variable {I J : Type}

theorem conditioned_equation_honest_satisfied
    (valid : J → Bool) (π : J → I) (i₀ i : I)
    (j₀ j : {j : J // valid j = true}) (hπ : π j.val = i)
    (f : Cube I) (g μ : Cube J) :
    satisfied (FoldedEquation.conditionedEquation valid π i₀ j₀ f g μ)
        (FoldedEquation.storedAssignment (fun h => h.val i) (fun h => h.val j)) =
      !(μ j.val) := by
  rw [FoldedEquation.conditionedEquation_satisfied, foldedAnswer_dictator,
    conditionedFoldedAnswer_dictator, conditionedFoldedAnswer_dictator,
    dictator_test_parity π i j.val hπ]

theorem mapped_conditioned_equation_honest_satisfied {Name : Type}
    (valid : J → Bool) (π : J → I) (i₀ i : I)
    (j₀ j : {j : J // valid j = true}) (hπ : π j.val = i)
    (rename : FoldedEquation.Address i₀ j₀ → Name) (assignment : Name → Bool)
    (hleft : ∀ h, assignment (rename (.inl h)) = h.val i)
    (hright : ∀ h, assignment (rename (.inr h)) = h.val j)
    (f : Cube I) (g μ : Cube J) :
    satisfied (mapEquation rename
        (FoldedEquation.conditionedEquation valid π i₀ j₀ f g μ)) assignment =
      !(μ j.val) := by
  have hlocal : assignment ∘ rename =
      FoldedEquation.storedAssignment (fun h => h.val i) (fun h => h.val j) := by
    funext a
    cases a with
    | inl h => exact hleft h
    | inr h => exact hright h
  rw [satisfied_mapEquation, hlocal]
  exact conditioned_equation_honest_satisfied valid π i₀ i j₀ j hπ f g μ

variable [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]

theorem tapeAcceptance_conditioned_dictators {D : ℕ} (positive : 0 < D)
    (valid : J → Bool) (π : J → I) (i₀ i : I)
    (j₀ j : {j : J // valid j = true}) (hπ : π j.val = i) :
    SourceTape.tapeAcceptance D π
      (foldedAnswer i₀ (fun h => h.val i))
      (conditionedFoldedAnswer valid j₀ (fun h => h.val j)) =
        1 - (D : ℝ)⁻¹ := by
  rw [SourceTape.tapeAcceptance_eq_realizedTestAcceptance]
  exact realizedTestAcceptance_folded_conditioned_dictators positive π i₀ i valid j₀ j hπ

end Local

section NumberedStorage

open SourceOccurrences

variable {V C I J : Type}

theorem numbered_assignment_restriction
    (vE : Encoding V) (cE : Encoding C) (iE : Encoding I) (jE : Encoding J)
    (left : V → I) (right : C → J) (v : V) (c : C)
    (valid : J → Bool) (i₀ : I) (j₀ j : {j : J // valid j = true})
    (hright : right c = j.val) :
    assignmentOfKey vE cE iE jE (taggedAssignment left right) ∘
      localAddress vE cE iE jE v c valid i₀ j₀ =
      FoldedEquation.storedAssignment (fun h => h.val (left v)) (fun h => h.val j) := by
  funext a
  cases a with
  | inl h =>
    simp only [Function.comp_apply, localAddress, assignmentOfKey_code,
      taggedAssignment_left, FoldedEquation.storedAssignment, Sum.elim_inl]
  | inr h =>
    simp only [Function.comp_apply, localAddress, assignmentOfKey_code,
      taggedAssignment_right, hright, extendRestricted_valid,
      FoldedEquation.storedAssignment, Sum.elim_inr]

theorem conditionedOccurrence_honest_satisfied
    (vE : Encoding V) (cE : Encoding C) (iE : Encoding I) (jE : Encoding J)
    (left : V → I) (right : C → J) (v : V) (c : C)
    (valid : J → Bool) (π : J → I) (i₀ : I)
    (j₀ j : {j : J // valid j = true})
    (hright : right c = j.val) (hπ : π j.val = left v)
    (f : Cube I) (g μ : Cube J) :
    satisfied (conditionedOccurrence vE cE iE jE v c valid π i₀ j₀ f g μ)
      (assignmentOfKey vE cE iE jE (taggedAssignment left right)) = !(μ j.val) := by
  rw [conditionedOccurrence, satisfied_mapEquation,
    numbered_assignment_restriction vE cE iE jE left right v c valid i₀ j₀ j hright]
  exact conditioned_equation_honest_satisfied valid π i₀ (left v) j₀ j hπ f g μ

variable [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]

theorem conditionedOccurrenceList_honest_acceptance {D : ℕ} (positive : 0 < D)
    (vE : Encoding V) (cE : Encoding C) (iE : Encoding I) (jE : Encoding J)
    (left : V → I) (right : C → J) (v : V) (c : C)
    (valid : J → Bool) (π : J → I) (i₀ : I)
    (j₀ j : {j : J // valid j = true})
    (hright : right c = j.val) (hπ : π j.val = left v)
    (tape : Encoding (SourceTape.TestTape I J D)) :
    let equations := occurrenceList tape (fun t =>
      conditionedOccurrence vE cE iE jE v c valid π i₀ j₀
        t.1 t.2.2 (realizedNoise t.2.1))
    ((equations.countP (fun e => satisfied e
      (assignmentOfKey vE cE iE jE (taggedAssignment left right)))) : ℝ) /
        equations.length = 1 - (D : ℝ)⁻¹ := by
  dsimp only
  rw [occurrenceList_acceptance]
  calc
    _ = SourceTape.tapeAcceptance D π (fun f => f (left v)) (fun g => g j.val) := by
      unfold SourceTape.tapeAcceptance
      apply Finset.expect_congr rfl
      intro t _
      rw [conditionedOccurrence_honest_satisfied vE cE iE jE left right v c
        valid π i₀ j₀ j hright hπ, dictator_test_parity π (left v) j.val hπ]
      cases realizedNoise t.2.1 j.val <;> rfl
    _ = _ := by
      rw [SourceTape.tapeAcceptance_eq_realizedTestAcceptance]
      exact realizedTestAcceptance_dictator positive π (left v) j.val hπ

end NumberedStorage

open SourceContexts
open SourceOccurrences

def honestGlobal (F : Target.Formula) (u : ℕ)
    (assignment : Fin F.variables → Bool) :
    (VariableContext F u × Cube (I u)) ⊕
      ((ClauseContext F u × Cube (J u)) ⊕ Unit) → Bool :=
  taggedAssignment (fun v => honestI F v assignment) (fun c => honestJ F c assignment)

def honestBits (F : Target.Formula) (u : ℕ)
    (assignment : Fin F.variables → Bool) : Fin (nBits F u) → Bool :=
  assignmentOfKey (variableEncoding F u) (clauseEncoding F u) (iEncoding u)
    (jEncoding u) (honestGlobal F u assignment)

@[simp] theorem honestBits_code (F : Target.Formula) (u : ℕ)
    (assignment : Fin F.variables → Bool)
    (key : GlobalKey (VariableContext F u) (ClauseContext F u) (I u) (J u)) :
    honestBits F u assignment ((proofEncoding F u).code key) =
      honestGlobal F u assignment key :=
  assignmentOfKey_code (variableEncoding F u) (clauseEncoding F u)
    (iEncoding u) (jEncoding u) (honestGlobal F u assignment) key

@[simp] theorem honestBits_dummy (F : Target.Formula) (u : ℕ)
    (assignment : Fin F.variables → Bool) :
    honestBits F u assignment (dummyIndex F u) = false := by
  rw [dummyIndex, honestBits_code]
  rfl

def honestValidJ (F : Target.Formula) {u : ℕ} (c : ClauseContext F u)
    (assignment : Fin F.variables → Bool)
    (hs : ∀ clause ∈ F.clauses, clause.eval assignment = true) :
    {j : J u // validJ F c j = true} :=
  ⟨honestJ F c assignment, honestJ_valid F c assignment hs⟩

theorem validJ_nonempty_of_satisfying (F : Target.Formula) {u : ℕ}
    (c : ClauseContext F u) (assignment : Fin F.variables → Bool)
    (hs : ∀ clause ∈ F.clauses, clause.eval assignment = true) :
    Nonempty {j : J u // validJ F c j = true} :=
  ⟨honestValidJ F c assignment hs⟩

theorem leftResponse_honest (F : Target.Formula) (u : ℕ)
    (assignment : Fin F.variables → Bool) (v : VariableContext F u) :
    leftResponse F u (honestBits F u assignment) v =
      fun f => f (honestI F v assignment) := by
  funext f
  simp only [leftResponse, honestBits_code, honestGlobal, taggedAssignment,
    foldedAnswer_dictator]

theorem rightResponse_honest (F : Target.Formula) (u : ℕ)
    (assignment : Fin F.variables → Bool)
    (hs : ∀ clause ∈ F.clauses, clause.eval assignment = true)
    (c : ClauseContext F u) :
    rightResponse F u (honestBits F u assignment) c =
      fun g => g (honestJ F c assignment) := by
  funext g
  cases ha : rightAnchor F c with
  | none =>
    have hf := (rightAnchor_none_iff F c).mp ha (honestJ F c assignment)
    rw [honestJ_valid F c assignment hs] at hf
    cases hf
  | some j₀ =>
    simp only [rightResponse, ha, honestBits_code, honestGlobal, taggedAssignment]
    have ht : (fun h : HalfCube j₀ =>
        extendRestricted (validJ F c) h.val (honestJ F c assignment)) =
        fun h => h.val (honestValidJ F c assignment hs) := by
      funext h
      exact extendRestricted_valid (validJ F c) h.val (honestValidJ F c assignment hs)
    rw [ht]
    exact conditionedFoldedAnswer_dictator (validJ F c) j₀
      (honestValidJ F c assignment hs) g

theorem context_tapeAcceptance {D : ℕ} (positive : 0 < D)
    (F : Target.Formula) {u : ℕ} (c : ClauseContext F u) (s : SlotContext u)
    (assignment : Fin F.variables → Bool)
    (hs : ∀ clause ∈ F.clauses, clause.eval assignment = true)
    (i₀ : I u) (j₀ : {j : J u // validJ F c j = true}) :
    SourceTape.tapeAcceptance D (pi F c (sampledVariables F c s))
      (foldedAnswer i₀ (fun h => h.val (honestI F (sampledVariables F c s) assignment)))
      (conditionedFoldedAnswer (validJ F c) j₀
        (fun h => h.val (honestValidJ F c assignment hs))) =
      1 - (D : ℝ)⁻¹ := by
  exact tapeAcceptance_conditioned_dictators positive (validJ F c)
    (pi F c (sampledVariables F c s)) i₀ _ j₀ _
    (pi_honest_sampled F c s assignment)

theorem sourceEquation_honest_satisfied (F : Target.Formula) (u D : ℕ)
    (assignment : Fin F.variables → Bool)
    (hs : ∀ clause ∈ F.clauses, clause.eval assignment = true)
    (p : SourceIndex F u D) :
    satisfied (sourceEquation F u D p) (honestBits F u assignment) =
      !(realizedNoise p.2.2.1 (honestJ F p.1.1 assignment)) := by
  simp only [sourceEquation, contextEquation_satisfied, leftResponse_honest,
    rightResponse_honest F u assignment hs]
  rw [dictator_test_parity _ _ _ (pi_honest_sampled F p.1.1 p.1.2 assignment)]

theorem rawSourceList_honest_acceptance (F : Target.Formula) (u D : ℕ)
    (hD : 0 < D) (hF : F.clauses ≠ [])
    (assignment : Fin F.variables → Bool)
    (hs : ∀ clause ∈ F.clauses, clause.eval assignment = true) :
    ((rawSourceList F u D).countP
      (fun e => satisfied e (honestBits F u assignment)) : ℝ) /
        (rawSourceList F u D).length = 1 - (D : ℝ)⁻¹ := by
  have hc : 0 < F.clauses.length := List.length_pos_iff.mpr hF
  let : Nonempty (Fin F.clauses.length) := ⟨⟨0, hc⟩⟩
  rw [rawSourceList_acceptance F u D hD]
  have heq (c : ClauseContext F u) (s : SlotContext u) :
      testAcceptance ((D : ℝ)⁻¹) (pi F c (sampledVariables F c s))
        (leftResponse F u (honestBits F u assignment) (sampledVariables F c s))
        (rightResponse F u (honestBits F u assignment) c) = 1 - (D : ℝ)⁻¹ := by
    rw [leftResponse_honest, rightResponse_honest F u assignment hs]
    exact testAcceptance_dictator _ _ _ _ (pi_honest_sampled F c s assignment)
  simp_rw [heq]
  simp only [Fintype.expect_const]

theorem sourceList_honest_acceptance_nonempty (F : Target.Formula) (u D : ℕ)
    (hD : 0 < D) (hF : F.clauses ≠ [])
    (assignment : Fin F.variables → Bool)
    (hs : ∀ clause ∈ F.clauses, clause.eval assignment = true) :
    ((sourceList F u D).countP
      (fun e => satisfied e (honestBits F u assignment)) : ℝ) /
        (sourceList F u D).length = 1 - (D : ℝ)⁻¹ := by
  rw [sourceList_nonempty F u D hF]
  exact rawSourceList_honest_acceptance F u D hD hF assignment hs

theorem sourceList_honest_acceptance (F : Target.Formula) (u D : ℕ)
    (hD : 0 < D) (assignment : Fin F.variables → Bool)
    (hs : ∀ clause ∈ F.clauses, clause.eval assignment = true) :
    1 - (D : ℝ)⁻¹ ≤ ((sourceList F u D).countP
      (fun e => satisfied e (honestBits F u assignment)) : ℝ) /
        (sourceList F u D).length := by
  by_cases hF : F.clauses = []
  · rw [sourceList_empty F u D hF]
    simp only [List.countP_cons, List.countP_nil, emptyFormulaEquation_satisfied,
      honestBits_dummy, Bool.not_false, ↓reduceIte,
      Nat.zero_add, Nat.cast_one, List.length_cons, List.length_nil, div_one]
    exact sub_le_self _ (inv_nonneg.mpr (Nat.cast_nonneg D))
  · exact (sourceList_honest_acceptance_nonempty F u D hD hF assignment hs).ge

theorem sourceList_honest_acceptance_rat (F : Target.Formula) (u D : ℕ)
    (hD : 0 < D) (assignment : Fin F.variables → Bool)
    (hs : ∀ clause ∈ F.clauses, clause.eval assignment = true) :
    1 - (D : ℚ)⁻¹ ≤ ((sourceList F u D).countP
      (fun e => satisfied e (honestBits F u assignment)) : ℚ) /
        (sourceList F u D).length := by
  apply (Rat.cast_le (K := ℝ)).mp
  simpa only [Rat.cast_sub, Rat.cast_one, Rat.cast_inv, Rat.cast_natCast, Rat.cast_div] using
    sourceList_honest_acceptance F u D hD assignment hs

theorem sourceList_honest_acceptance_nonempty_rat (F : Target.Formula) (u D : ℕ)
    (hD : 0 < D) (hF : F.clauses ≠ [])
    (assignment : Fin F.variables → Bool)
    (hs : ∀ clause ∈ F.clauses, clause.eval assignment = true) :
    ((sourceList F u D).countP
      (fun e => satisfied e (honestBits F u assignment)) : ℚ) /
        (sourceList F u D).length = 1 - (D : ℚ)⁻¹ := by
  apply Rat.cast_injective (α := ℝ)
  simpa only [Rat.cast_sub, Rat.cast_one, Rat.cast_inv, Rat.cast_natCast, Rat.cast_div] using
    sourceList_honest_acceptance_nonempty F u D hD hF assignment hs

end BinPackingGames.Foundations.Hastad.SourceHonest

end

end OAI
