import Mathlib
import OAI.Computability.DirectedFeedback.RankGraph.CloneGap

namespace OAI


noncomputable section

namespace DFVSGames.Foundations.Hastad.SourceTape

open scoped BigOperators
open DFVSGames.Reduction.FiniteNoise

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


end DFVSGames.Foundations.Hastad.SourceTape

end


namespace DFVSGames.Foundations.Hastad.SourceContexts

open Target PCP

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

theorem projection_implies_sampled_accepts (F : Formula) {u : ℕ}
    (c : ClauseContext F u) (s : SlotContext u) (i : I u) (j : J u)
    (hj : validJ F c j = true) (hpi : pi F c (sampledVariables F c s) j = i) :
    ∀ t, (localSatisfies (clauseAt F (c t)) (j t) &&
      decide (answerAt (j t) (s t) = i t)) = true := by
  intro t
  exact baseAccepts_implies_sampled F (c t) (s t) (i t) (j t)
    (projection_implies_coordinate_accepts F c _ i j hj hpi t)

end DFVSGames.Foundations.Hastad.SourceContexts


namespace DFVSGames.Reduction.SourceEncoding

open DFVSGames.Foundations.Complexity

structure Input where
  «variables» : Nat
  equations : List (CloneGap.Equation (Fin «variables»))
  nonempty : equations ≠ []

abbrev Table := Input

def equationWords {n : Nat} (e : CloneGap.Equation (Fin n)) : List Nat :=
  [e.first.val, e.second.val, e.third.val, if e.rhs then 1 else 0]

def inputWords (input : Input) : List Nat :=
  [input.«variables», input.equations.length] ++ input.equations.flatMap equationWords

def inputBits (input : Input) : List Bool := encodeWords (inputWords input)

def parseEquation («variables» : Nat) :
    List Nat → Option (CloneGap.Equation (Fin «variables») × List Nat)
  | first :: second :: third :: rhs :: rest =>
      if hfirst : first < «variables» then
        if hsecond : second < «variables» then
          if hthird : third < «variables» then
            if rhs = 0 then
              some (⟨⟨first, hfirst⟩, ⟨second, hsecond⟩, ⟨third, hthird⟩, false⟩, rest)
            else if rhs = 1 then
              some (⟨⟨first, hfirst⟩, ⟨second, hsecond⟩, ⟨third, hthird⟩, true⟩, rest)
            else none
          else none
        else none
      else none
  | _ => none

@[simp] theorem parseEquation_encoded {n : Nat} (e : CloneGap.Equation (Fin n))
    (rest : List Nat) :
    parseEquation n (equationWords e ++ rest) = some (e, rest) := by
  cases e with
  | mk first second third rhs =>
      cases rhs <;> simp [equationWords, parseEquation, first.isLt, second.isLt, third.isLt]

def parseEquations («variables» : Nat) :
    Nat → List Nat → Option (List (CloneGap.Equation (Fin «variables»)) × List Nat)
  | 0, words => some ([], words)
  | count + 1, words => do
      let (equation, words) ← parseEquation «variables» words
      let (equations, words) ← parseEquations «variables» count words
      return (equation :: equations, words)

@[simp] theorem parseEquations_encoded {n : Nat}
    (equations : List (CloneGap.Equation (Fin n))) (rest : List Nat) :
    parseEquations n equations.length (equations.flatMap equationWords ++ rest) =
      some (equations, rest) := by
  induction equations with
  | nil => rfl
  | cons e equations ih =>
      simp [List.append_assoc, parseEquations, parseEquation_encoded, ih]

def decodeInputWords : List Nat → Option Input
  | «variables» :: count :: words => do
      let (equations, trailing) ← parseEquations «variables» count words
      if trailing = [] then
        if nonempty : 0 < equations.length then
          some ⟨«variables», equations, List.length_pos_iff.mp nonempty⟩
        else none
      else none
  | _ => none

@[simp] theorem decodeInputWords_encoded (input : Input) :
    decodeInputWords (inputWords input) = some input := by
  cases input with
  | mk «variables» equations nonempty =>
      have parsed := parseEquations_encoded equations []
      have positive := List.length_pos_iff.mpr nonempty
      simp only [List.append_nil] at parsed
      simp [decodeInputWords, inputWords, parsed, positive]

def decodeInputBits (bits : List Bool) : Option Input :=
  decodeWords bits >>= decodeInputWords

@[simp] theorem decodeInputBits_encoded (input : Input) :
    decodeInputBits (inputBits input) = some input := by
  simp [decodeInputBits, inputBits]

theorem inputWords_injective {first second : Input}
    (same : inputWords first = inputWords second) : first = second := by
  have parsed := congrArg decodeInputWords same
  simpa only [decodeInputWords_encoded, Option.some.injEq] using parsed

theorem inputBits_injective {first second : Input}
    (same : inputBits first = inputBits second) : first = second := by
  have parsed := congrArg decodeInputBits same
  simpa only [decodeInputBits_encoded, Option.some.injEq] using parsed

@[simp] theorem equationWords_length {n : Nat} (e : CloneGap.Equation (Fin n)) :
    (equationWords e).length = 4 := by simp [equationWords]

theorem equationsWords_length {n : Nat} (equations : List (CloneGap.Equation (Fin n))) :
    (equations.flatMap equationWords).length = 4 * equations.length := by
  induction equations with
  | nil => rfl
  | cons e equations ih =>
      simp only [List.flatMap_cons, List.length_append, equationWords_length,
        List.length_cons, ih, Nat.mul_add, Nat.mul_one]
      omega

@[simp] theorem inputWords_length (input : Input) :
    (inputWords input).length = 2 + 4 * input.equations.length := by
  simp only [inputWords, List.length_append, List.length_cons, List.length_nil,
    equationsWords_length]

theorem equationBits_length_le {n : Nat} (e : CloneGap.Equation (Fin n)) :
    (encodeWords (equationWords e)).length ≤ 3 * n + 2 := by
  have hfirst := e.first.isLt
  have hsecond := e.second.isLt
  have hthird := e.third.isLt
  cases hrhs : e.rhs <;> simp [equationWords, hrhs] <;> omega

theorem equationsBits_length_le {n : Nat} (equations : List (CloneGap.Equation (Fin n))) :
    (encodeWords (equations.flatMap equationWords)).length ≤
      equations.length * (3 * n + 2) := by
  induction equations with
  | nil => simp [encodeWords]
  | cons e equations ih =>
      have he := equationBits_length_le e
      simp only [List.flatMap_cons, encodeWords_append, List.length_append,
        List.length_cons, Nat.add_mul, Nat.one_mul]
      omega

theorem inputBits_length (input : Input) :
    (inputBits input).length = input.«variables» + input.equations.length + 2 +
      (encodeWords (input.equations.flatMap equationWords)).length := by
  simp only [inputBits, inputWords, encodeWords_append, List.length_append,
    encodeWords, encodeWord_length, List.length_nil]
  omega

theorem inputBits_length_le (input : Input) :
    (inputBits input).length ≤ input.«variables» + input.equations.length + 2 +
      input.equations.length * (3 * input.«variables» + 2) := by
  rw [inputBits_length]
  exact Nat.add_le_add_left (equationsBits_length_le input.equations) _

theorem inputBits_length_ge_variables (input : Input) :
    input.«variables» ≤ (inputBits input).length := by rw [inputBits_length]; omega

theorem inputBits_length_ge_equations (input : Input) :
    input.equations.length ≤ (inputBits input).length := by rw [inputBits_length]; omega

end DFVSGames.Reduction.SourceEncoding

end OAI
