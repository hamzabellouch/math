import Mathlib
import OAI.Computability.DirectedFeedback.Encoding.RawPrivateTable

namespace OAI

namespace DFVSGames.Soundness.RepeatedGameBounds

open scoped BigOperators

noncomputable section

def uniformAverage {Ω K : Type*} [Fintype Ω] [Field K] (f : Ω → K) : K :=
  (∑ ω, f ω) / (Fintype.card Ω : K)

def zeroCount {I C : Type*} [Fintype I] [Zero C] [DecidableEq C]
    (omega : I → C) : Nat :=
  (Finset.univ.filter fun j => omega j = 0).card

theorem power_zeroCount_eq_prod {I C K : Type*} [Fintype I] [Zero C] [DecidableEq C]
    [CommMonoid K] (a : K) (omega : I → C) :
    a ^ zeroCount omega = ∏ j, if omega j = 0 then a else 1 := by
  rw [← Finset.prod_filter]
  simp [zeroCount]

theorem sum_one_zero_weight {C K : Type*} [Fintype C] [Zero C]
    [DecidableEq C] [Field K] (a : K) :
    (∑ c : C, if c = 0 then a else 1) = (Fintype.card C : K) + a - 1 := by
  classical
  have hpoint : (fun c : C => if c = 0 then a else (1 : K)) =
      fun c => 1 + if c = 0 then a - 1 else 0 := by
    funext c
    split_ifs <;> ring
  rw [hpoint, Finset.sum_add_distrib]
  simp
  ring

theorem sum_power_zeroCount {C K : Type*} [Fintype C] [Zero C]
    [DecidableEq C] [Field K] (a : K) (t : Nat) :
    (∑ omega : Fin t → C, a ^ zeroCount omega) =
      ((Fintype.card C : K) + a - 1) ^ t := by
  simp_rw [power_zeroCount_eq_prod]
  rw [← Fintype.sum_pow (fun c : C => if c = 0 then a else 1) t,
    sum_one_zero_weight]

theorem uniformAverage_power_zeroCount {C K : Type*} [Fintype C] [Zero C]
    [DecidableEq C] [Field K] [CharZero K] (a : K) (t : Nat) :
    uniformAverage (fun omega : Fin t → C => a ^ zeroCount omega) =
      (1 - (1 / (Fintype.card C : K)) * (1 - a)) ^ t := by
  have hC : (Fintype.card C : K) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  unfold uniformAverage
  rw [sum_power_zeroCount]
  simp only [Fintype.card_fun, Fintype.card_fin, Nat.cast_pow]
  rw [← div_pow]
  congr 1
  field_simp
  ring

abbrev BinaryCoefficient (m : Nat) := Fin m → ZMod 2

theorem card_binaryCoefficient (m : Nat) : Fintype.card (BinaryCoefficient m) = 2 ^ m := by
  simp [BinaryCoefficient]

theorem uniform_binary_coefficient_moment {K : Type*} [Field K] [CharZero K]
    (a : K) (m t : Nat) :
    uniformAverage (fun omega : Fin t → BinaryCoefficient m => a ^ zeroCount omega) =
      (1 - (1 / 2 : K) ^ m * (1 - a)) ^ t := by
  rw [uniformAverage_power_zeroCount, card_binaryCoefficient]
  simp

theorem uniformAverage_mono {Ω K : Type*} [Fintype Ω]
    [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    {f g : Ω → K} (h : ∀ ω, f ω ≤ g ω) : uniformAverage f ≤ uniformAverage g := by
  unfold uniformAverage
  exact div_le_div_of_nonneg_right (Finset.sum_le_sum fun ω _ => h ω) (Nat.cast_nonneg _)

theorem uniformAverage_const {Ω K : Type*} [Fintype Ω] [Nonempty Ω]
    [Field K] [CharZero K] (c : K) : uniformAverage (fun _ : Ω => c) = c := by
  have hΩ : (Fintype.card Ω : K) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  simp [uniformAverage, mul_div_cancel_left₀, hΩ]

theorem uniformAverage_prod {Ω Γ K : Type*} [Fintype Ω] [Fintype Γ]
    [Field K] (f : Ω × Γ → K) :
    uniformAverage f = uniformAverage (fun ω => uniformAverage fun γ => f (ω, γ)) := by
  simp only [uniformAverage, Fintype.card_prod, Nat.cast_mul,
    Fintype.sum_prod_type, div_eq_mul_inv, ← Finset.sum_mul, mul_inv_rev]
  ring

theorem uniformAverage_equiv {Ω Γ K : Type*} [Fintype Ω] [Fintype Γ]
    [Field K] (e : Ω ≃ Γ) (f : Γ → K) :
    uniformAverage (fun omega => f (e omega)) = uniformAverage f := by
  unfold uniformAverage
  rw [e.sum_comp, Fintype.card_congr e]

theorem uniformAverage_product_left {Ω Γ K : Type*} [Fintype Ω] [Fintype Γ]
    [Nonempty Γ] [Field K] [CharZero K] (f : Ω → K) :
    uniformAverage (fun omega : Ω × Γ => f omega.1) = uniformAverage f := by
  rw [uniformAverage_prod]
  simp_rw [uniformAverage_const]

theorem uniformAverage_coordinate_product {I C K : Type*} [Fintype I] [DecidableEq I] [Fintype C]
    [Field K] (f : I → C → K) :
    uniformAverage (fun omega : I → C => ∏ i, f i (omega i)) =
      ∏ i, uniformAverage (f i) := by
  classical
  unfold uniformAverage
  rw [← Fintype.prod_sum]
  simp only [Fintype.card_pi, Nat.cast_prod]
  rw [Finset.prod_div_distrib]

theorem uniformAverage_power_zeroCount_indexed {I C K : Type*} [Fintype I] [DecidableEq I]
    [Fintype C] [Zero C] [DecidableEq C] [Field K] [CharZero K] (a : K) :
    uniformAverage (fun omega : I → C => a ^ zeroCount omega) =
      (1 - (1 / (Fintype.card C : K)) * (1 - a)) ^ Fintype.card I := by
  simp_rw [power_zeroCount_eq_prod]
  rw [uniformAverage_coordinate_product (fun _ c => if c = 0 then a else 1)]
  simp only [uniformAverage, sum_one_zero_weight, Finset.prod_const, Finset.card_univ]
  congr 1
  have hC : (Fintype.card C : K) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  field_simp
  ring

open ConditionalIncidences in
def splitRawCoefficients {P C : Type} (J : Finset P) :
    RawCoefficients J C ≃ (PositionInside J → C) ×
      (Option (PositionOutside J × Fin 2) → C) where
  toFun gamma := (fun j => gamma (some (.inr j)), fun slot =>
    match slot with
    | none => gamma none
    | some j => gamma (some (.inl j)))
  invFun pieces slot := match slot with
    | none => pieces.2 none
    | some (.inl j) => pieces.2 (some j)
    | some (.inr j) => pieces.1 j
  left_inv gamma := by
    funext slot
    cases slot with
    | none => rfl
    | some slot => cases slot <;> rfl
  right_inv pieces := by
    apply Prod.ext
    · rfl
    · funext slot; cases slot <;> rfl

theorem zeroSet_card_eq_zeroCount {P C : Type} [DecidableEq P] [Zero C]
    [DecidableEq C] (J : Finset P) (gamma : ConditionalIncidences.RawCoefficients J C) :
    (ConditionalIncidences.zeroSet J gamma).card =
      zeroCount ((splitRawCoefficients J) gamma).1 := by
  simp [ConditionalIncidences.zeroSet, zeroCount, splitRawCoefficients]
  rfl

theorem uniform_raw_coefficient_moment {P C K : Type} [Fintype P] [DecidableEq P]
    [Fintype C] [Zero C] [DecidableEq C] [Field K] [CharZero K]
    (J : Finset P) (a : K) :
    uniformAverage (fun gamma : ConditionalIncidences.RawCoefficients J C =>
      a ^ (ConditionalIncidences.zeroSet J gamma).card) =
      (1 - (1 / (Fintype.card C : K)) * (1 - a)) ^ J.card := by
  simp_rw [zeroSet_card_eq_zeroCount]
  rw [uniformAverage_equiv (splitRawCoefficients J)
    (fun pieces => a ^ zeroCount pieces.1)]
  rw [uniformAverage_product_left
    (fun omega : ConditionalIncidences.PositionInside J → C => a ^ zeroCount omega),
    uniformAverage_power_zeroCount_indexed]
  simp [ConditionalIncidences.PositionInside]

theorem uniform_binary_coefficient_upper {K : Type*}
    [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    (a : K) (m t : Nat) (success : (Fin t → BinaryCoefficient m) → K)
    (bound : ∀ omega, success omega ≤ a ^ zeroCount omega) :
    uniformAverage success ≤ (1 - (1 / 2 : K) ^ m * (1 - a)) ^ t := by
  calc
    uniformAverage success ≤ uniformAverage
        (fun omega : Fin t → BinaryCoefficient m => a ^ zeroCount omega) :=
      uniformAverage_mono bound
    _ = _ := uniform_binary_coefficient_moment a m t

open Foundations.Games

namespace Simulation

abbrev PredicateGame := IncidenceExtraction.Game
abbrev PredicateStrategies := IncidenceExtraction.Strategies

variable {QA QB A B OA OB X Y : Type}
  [Fintype QA] [Fintype QB] [Fintype A] [Fintype B]
  [Fintype OA] [Fintype OB] [Fintype X] [Fintype Y]

def predicateGame (G : Game QA QB A B) : PredicateGame QA QB A B :=
  ⟨fun qa qb a b => G.accepts qa qb a b = true⟩

def strategyPair (s : PredicateStrategies QA QB A B) : Strategy QA QB A B :=
  (s.first, s.second)

def weightedGame (G : PredicateGame QA QB A B)
    (questions : FiniteDistribution (QA × QB)) : Game QA QB A B := by
  classical
  exact ⟨questions, fun qa qb a b => decide (G.accepts qa qb a b)⟩

def reconstructedGame (inner : Game QA QB A B) (outer : PredicateGame OA OB X Y)
    (r : IncidenceExtraction.LocalSimulation (predicateGame inner) outer) :
    Game OA OB X Y :=
  weightedGame outer (inner.questions.pushforward fun questions =>
    (r.questionA questions.1, r.questionB questions.2))

theorem reconstructedGame_success_le
    (inner : Game QA QB A B) (outer : PredicateGame OA OB X Y)
    (r : IncidenceExtraction.LocalSimulation (predicateGame inner) outer)
    (s : PredicateStrategies OA OB X Y) :
    (reconstructedGame inner outer r).success (strategyPair s) ≤
      inner.success (strategyPair (r.induced s)) := by
  classical
  unfold Game.success
  change (inner.questions.pushforward fun questions =>
      (r.questionA questions.1, r.questionB questions.2)).probability _ ≤ _
  rw [FiniteDistribution.probability_pushforward]
  apply FiniteDistribution.probability_mono
  intro questions hwin
  have houter : s.wins outer (r.questionA questions.1) (r.questionB questions.2) := by
    exact of_decide_eq_true hwin
  exact r.induced_wins s questions.1 questions.2 houter

theorem reconstructed_repetition_success_le
    (G : Game QA QB A B) (n : Nat) (outer : PredicateGame OA OB X Y)
    (r : IncidenceExtraction.LocalSimulation (predicateGame (G.repetition n)) outer)
    (s : PredicateStrategies OA OB X Y) :
    (reconstructedGame (G.repetition n) outer r).success (strategyPair s) ≤
      (G.repetition n).success (strategyPair (r.induced s)) :=
  reconstructedGame_success_le (G.repetition n) outer r s

end Simulation

namespace ActualProjection

open IncidenceExtraction

abbrev FirstAnswer (P : Type) := Bool × (P → Triple)
abbrev SecondAnswer (P : Type) := Bool × (P → Triple) × (P → Bool)

def project {P : Type} (single : P → Bool) (indices : P → Fin 3)
    (answer : FirstAnswer P) : SecondAnswer P :=
  (answer.1, ZeroInformation.projectFull single answer.2,
    ZeroInformation.projectSingles single indices answer.2)

def accepts {P R O N : Type} (g : Incidence O N) (single : P → Bool)
    (qa : ZeroInformation.FirstInput P R O)
    (qb : ZeroInformation.SecondInput P R O N)
    (answerA : FirstAnswer P) (answerB : SecondAnswer P) : Prop :=
  (∀ j, xorTriple (answerA.2 j) = (g.rhs (qa.question j) && answerA.1)) ∧
  answerA.1 = true ∧ ∃ indices : P → Fin 3,
    qb.question = ZeroInformation.partnerQuestion single qa.question
      (fun j => g.name (qa.question j) (indices j)) ∧
    answerB = project single indices answerA

def predicateGame {P R O N : Type} (g : Incidence O N) (single : P → Bool) :
    IncidenceExtraction.Game
      (ZeroInformation.FirstInput P R O) (ZeroInformation.SecondInput P R O N)
      (FirstAnswer P) (SecondAnswer P) :=
  ⟨accepts g single⟩

theorem actual_partnerProjection_accepts
    {P R O N : Type} (g : Incidence O N) (positions : List P)
    (single : P → Bool) (zeta0 : ZeroInformation.Bits R)
    (zeta1 zeta2 omega : P → ZeroInformation.Bits R)
    (occurrences : P → O) (indices : P → Fin 3)
    (point : ZeroInformation.FirstPoint g.rhs occurrences)
    (hone : point.val.1 = true) :
    accepts g single
      (ZeroInformation.firstInput positions single zeta0 zeta1 zeta2 omega
        occurrences indices)
      (ZeroInformation.secondInput positions single zeta0 zeta1 zeta2 omega
        occurrences (fun j => g.name (occurrences j) (indices j)))
      point.val
      (ZeroInformation.partnerProjection single g.rhs occurrences
        (fun j => g.name (occurrences j) (indices j)) indices point).val := by
  exact ⟨point.property, hone, indices, rfl, rfl⟩

theorem accepts_implies_named_incidence
    {P R O N : Type} (g : Incidence O N) (single : P → Bool)
    (qa : ZeroInformation.FirstInput P R O)
    (qb : ZeroInformation.SecondInput P R O N)
    (answerA : FirstAnswer P) (answerB : SecondAnswer P)
    (h : accepts g single qa qb answerA answerB)
    (j : P) (hj : single j = true) (name : N)
    (hname : qb.question j = Sum.inr name) :
    g.namedAccepts (qa.question j) name (answerA.2 j) (answerB.2.2 j) := by
  obtain ⟨hvalid, hone, indices, hquestions, hproject⟩ := h
  refine ⟨indices j, ?_, ?_, ?_⟩
  · have hq := congrFun hquestions j
    simp [ZeroInformation.partnerQuestion, hj, hname] at hq
    exact hq.symm
  · simpa [hone] using hvalid j
  · subst answerB
    simp [project, ZeroInformation.projectSingles, hj]

end ActualProjection

end
end DFVSGames.Soundness.RepeatedGameBounds

namespace DFVSGames.Soundness.ActualPointAnswers
open DFVSGames.Integration.BinaryLinear
open DFVSGames.Reduction
open PartnerProjection PartnerMapCoordinates RawPartnerTarget
open RepeatedGameBounds

noncomputable section
attribute [local instance] Classical.propDecidable

variable {k : Nat}

def sourceTau : ActualHomogeneous.E k →ₗ[F2] F2 := LinearMap.fst F2 F2 _
def partnerTau (J : Finset (Fin k)) : RawPoint J →ₗ[F2] F2 := LinearMap.proj none

theorem tau_projection (rhs : Fin k → Bool) (J : Finset (Fin k))
    (slot : Fin k → Slot) : (partnerTau J).comp (rawProjection rhs J slot) = sourceTau := by
  apply LinearMap.ext
  intro x
  change ofBit (toBit x.1) = x.1
  exact ofBit_toBit _

def firstAnswer (rhs : Fin k → Bool) (x : ActualHomogeneous.E k) :
    ActualProjection.FirstAnswer (Fin k) :=
  let p := (PartnerLinear.sourceLinearEquiv rhs).symm x
  (p.homogeneous, fun j => ConcreteExtraction.tripleCoordinates (p.coordinates j))

def secondAnswer (rhs : Fin k → Bool) (J : Finset (Fin k)) (v : RawPoint J) :
    ActualProjection.SecondAnswer (Fin k) :=
  let y := (pointEquiv rhs J).symm v
  (y.homogeneous, (fun j => ConcreteExtraction.tripleCoordinates (y.full j)), y.single)

private theorem triple_eq_of_first_second_parity_inline_ActualPointAnswers (a b : PartnerProjection.Triple)
    (h₁ : a.first = b.first) (h₂ : a.second = b.second) (hp : parity a = parity b) : a = b := by
  rcases a with ⟨a₁, a₂, a₃⟩
  rcases b with ⟨b₁, b₂, b₃⟩
  dsimp only at h₁ h₂
  subst b₁
  subst b₂
  simp only [parity] at hp
  have h₃ := congrArg (fun z => (a₁ ^^ a₂) ^^ z) hp
  have cancel (c d : Bool) : (c ^^ (c ^^ d)) = d := by
    cases c <;> cases d <;> rfl
  simp only [cancel] at h₃
  cases h₃
  rfl

theorem secondAnswer_projection (rhs rhs' : Fin k → Bool) (J : Finset (Fin k))
    (slot : Fin k → Slot) (x : ActualHomogeneous.E k)
    (hout : ∀ j, j ∉ J → rhs' j = rhs j) :
    secondAnswer rhs' J (rawProjection rhs J slot x) =
      ActualProjection.project (activeOf J) (fun j => ConcreteExtraction.slotIndex (slot j))
        (firstAnswer rhs x) := by
  let p := (PartnerLinear.sourceLinearEquiv rhs).symm x
  let y := (pointEquiv rhs' J).symm (rawProjection rhs J slot x)
  let z := PartnerLinear.projection rhs (activeOf J) slot p
  have hr : pointEquiv rhs' J y = pointEquiv rhs J z :=
    (pointEquiv rhs' J).apply_symm_apply _
  have hh : y.homogeneous = z.homogeneous := by
    have h := congrArg toBit (congrFun hr none)
    simpa only [pointEquiv_none, toBit_ofBit] using h
  have hfull : y.full = z.full := by
    funext j
    by_cases hj : j ∈ J
    · rw [y.full_zero j (by simp [activeOf, hj]), z.full_zero j (by simp [activeOf, hj])]
    · have h₁ : (y.full j).first = (z.full j).first := by
        have h := congrArg toBit (congrFun hr (some (.inl (⟨j,hj⟩,(0:Fin 2)))))
        simpa only [pointEquiv_full_first, toBit_ofBit] using h
      have h₂ : (y.full j).second = (z.full j).second := by
        have h := congrArg toBit (congrFun hr (some (.inl (⟨j,hj⟩,(1:Fin 2)))))
        simpa only [pointEquiv_full_second, toBit_ofBit] using h
      have hp : parity (y.full j) = parity (z.full j) := by
        rw [y.full_valid j (by simp [activeOf, hj]),
          z.full_valid j (by simp [activeOf, hj]), hout j hj, hh]
      exact triple_eq_of_first_second_parity_inline_ActualPointAnswers _ _ h₁ h₂ hp
  have hsingle : y.single = z.single := by
    funext j
    by_cases hj : j ∈ J
    · have h := congrArg toBit (congrFun hr (some (.inr ⟨j,hj⟩)))
      simpa only [pointEquiv_single, toBit_ofBit] using h
    · rw [y.single_zero j (by simp [activeOf, hj]), z.single_zero j (by simp [activeOf, hj])]
  change (y.homogeneous, (fun j => ConcreteExtraction.tripleCoordinates (y.full j)), y.single) = _
  rw [hh, hfull, hsingle]
  apply Prod.ext
  · rfl
  · apply Prod.ext
    · funext j i
      change ConcreteExtraction.tripleCoordinates
          (if decide (j ∈ J) then zeroTriple else p.coordinates j) i =
        (if decide (j ∈ J) then false else ConcreteExtraction.tripleCoordinates (p.coordinates j) i)
      cases h : decide (j ∈ J) <;> simp [ConcreteExtraction.tripleCoordinates, zeroTriple]
    · funext j
      change (if decide (j ∈ J) then retained (slot j) (p.coordinates j) else false) =
        (if decide (j ∈ J) then ConcreteExtraction.tripleCoordinates (p.coordinates j)
          (ConcreteExtraction.slotIndex (slot j)) else false)
      rw [ConcreteExtraction.retained_coordinates]

def displayedRhs {Id Name : Type} (rhs : Id → Bool) (question : Fin k → Sum Id Name) :
    Fin k → Bool := fun j => match question j with
  | .inl o => rhs o
  | .inr _ => false

theorem displayedRhs_full {Id Name : Type} (rhs : Id → Bool)
    (J : Finset (Fin k)) (names : Id → Fin 3 → Name)
    (occ : Fin k → Id) (slot : Fin k → Slot) (j : Fin k) (hj : j ∉ J) :
    displayedRhs rhs (RawPrivateTable.displayed J names occ slot) j = rhs (occ j) := by
  simp [displayedRhs, RawPrivateTable.displayed, hj]

theorem actual_accepts {Q Id Name : Type} (J : Finset (Fin k))
    (g : IncidenceExtraction.Incidence Id Name)
    (qa : ZeroInformation.FirstInput (Fin k) Q Id)
    (qb : ZeroInformation.SecondInput (Fin k) Q Id Name)
    (slot : Fin k → Slot)
    (hquestion : qb.question = RawPrivateTable.displayed J g.name qa.question slot)
    (x : ActualHomogeneous.E k) (v : RawPoint J)
    (hone : sourceTau x = 1)
    (hprojection : rawProjection (fun j => g.rhs (qa.question j)) J slot x = v) :
    ActualProjection.accepts g (activeOf J) qa qb
      (firstAnswer (fun j => g.rhs (qa.question j)) x)
      (secondAnswer (displayedRhs g.rhs qb.question) J v) := by
  let p := (PartnerLinear.sourceLinearEquiv (fun j => g.rhs (qa.question j))).symm x
  have hp : p.homogeneous = true := by
    change toBit x.1 = true
    change x.1 = 1 at hone
    rw [hone]
    decide
  refine ⟨?_, hp, (fun j => ConcreteExtraction.slotIndex (slot j)), ?_, ?_⟩
  · intro j
    exact (ConcreteExtraction.parity_coordinates _).trans (p.valid j)
  · rw [hquestion]
    funext j
    by_cases hj : j ∈ J <;>
      simp [RawPrivateTable.displayed, ZeroInformation.partnerQuestion, activeOf, hj]
  · rw [← hprojection]
    exact secondAnswer_projection _ _ J slot x (fun j hj => by
      rw [hquestion]
      exact displayedRhs_full g.rhs J g.name qa.question slot j hj)

end
end DFVSGames.Soundness.ActualPointAnswers

namespace DFVSGames.Soundness.ActualInputRows
open DFVSGames.Integration.BinaryLinear
open DFVSGames.Reduction
open ConditionalIncidences PartnerMapCoordinates RawPartnerTarget BinaryRowTransport

noncomputable section
attribute [local instance] Classical.propDecidable

variable {k : Nat} {Q Id Name : Type}

def restrictedFirst (rhs : Id → Bool)
    (qa : ZeroInformation.FirstInput (Fin k) Q Id) (x : ActualHomogeneous.E k) : Q → F2 :=
  let p := (PartnerLinear.sourceLinearEquiv (fun j => rhs (qa.question j))).symm x
  fun q => ofBit (qa.row p.homogeneous
    (fun j => ConcreteExtraction.tripleCoordinates (p.coordinates j)) q)

def firstMap (rhs : Id → Bool) (qa : ZeroInformation.FirstInput (Fin k) Q Id) :
    ActualHomogeneous.E k →ₗ[F2] (Q → F2) :=
  if h : ∃ Z : ActualHomogeneous.E k →ₗ[F2] (Q → F2),
    ∀ x, Z x = restrictedFirst rhs qa x then Classical.choose h else 0

theorem firstMap_eq (rhs : Id → Bool) (qa : ZeroInformation.FirstInput (Fin k) Q Id)
    (Z : ActualHomogeneous.E k →ₗ[F2] (Q → F2))
    (hZ : ∀ x, restrictedFirst rhs qa x = Z x) : firstMap rhs qa = Z := by
  have h : ∃ W : ActualHomogeneous.E k →ₗ[F2] (Q → F2),
      ∀ x, W x = restrictedFirst rhs qa x := ⟨Z, fun x => (hZ x).symm⟩
  unfold firstMap
  rw [dite_eq_left h]
  exact LinearMap.ext (fun x => (Classical.choose_spec h x).trans (hZ x))

def restrictedSecond (J : Finset (Fin k))
    (qb : ZeroInformation.SecondInput (Fin k) Q Id Name) (v : RawPoint J) : Q → F2 :=
  let y := (pointEquiv (fun _ : Fin k => false) J).symm v
  fun q => ofBit (qb.row y.homogeneous
    (fun j => ConcreteExtraction.tripleCoordinates (y.full j)) y.single q)

def secondMap (J : Finset (Fin k))
    (qb : ZeroInformation.SecondInput (Fin k) Q Id Name) : RawPoint J →ₗ[F2] (Q → F2) :=
  if h : ∃ Y : RawPoint J →ₗ[F2] (Q → F2),
    ∀ v, Y v = restrictedSecond J qb v then Classical.choose h else 0

theorem secondMap_eq (J : Finset (Fin k))
    (qb : ZeroInformation.SecondInput (Fin k) Q Id Name) (Y : RawPoint J →ₗ[F2] (Q → F2))
    (hY : ∀ v, restrictedSecond J qb v = Y v) : secondMap J qb = Y := by
  have h : ∃ W : RawPoint J →ₗ[F2] (Q → F2),
      ∀ v, W v = restrictedSecond J qb v := ⟨Y, fun v => (hY v).symm⟩
  unfold secondMap
  rw [dite_eq_left h]
  exact LinearMap.ext (fun v => (Classical.choose_spec h v).trans (hY v))

theorem firstMap_actual [Fintype Q] [DecidableEq Q]
    (J : Finset (Fin k)) (rhs : Id → Bool) (occ : Fin k → Id)
    (slot : Fin k → PartnerProjection.Slot) (Y : RawPoint J →ₗ[F2] (Q → F2)) :
    firstMap rhs (actualFirst J (rowCoefficients J (gammaOfRawMap J Y))
      (fun j => (occ j, ConcreteExtraction.slotIndex (slot j)))) =
      Y.comp (rawProjection (fun j => rhs (occ j)) J slot) := by
  apply firstMap_eq
  intro x
  let p := (PartnerLinear.sourceLinearEquiv (fun j => rhs (occ j))).symm x
  have h := actual_pullbackRow (fun j => rhs (occ j)) J (gammaOfRawMap J Y) slot p
  rw [← rawMap_on_partner (fun j => rhs (occ j)) J Y] at h
  funext q
  have he := congrArg ofBit (congrFun h q).symm
  simp only [rowBits, ofBit_toBit, restrictedFirst, actualFirst,
    ZeroInformation.firstInput, rawProjection, p, LinearMap.comp_apply,
    LinearEquiv.coe_toLinearMap] at he ⊢
  convert he using 1
  congr 5

theorem secondMap_actual [Fintype Q] [DecidableEq Q]
    (J : Finset (Fin k)) (names : Id → Fin 3 → Name) (draw : Draw (Fin k) Id)
    (Y : RawPoint J →ₗ[F2] (Q → F2)) :
    secondMap J (actualSecond J names (rowCoefficients J (gammaOfRawMap J Y)) draw) = Y := by
  apply secondMap_eq
  intro v
  let y := (pointEquiv (fun _ : Fin k => false) J).symm v
  have h := actual_partnerRow (fun _ : Fin k => false) J (gammaOfRawMap J Y) y
  rw [← rawMap_on_partner (fun _ : Fin k => false) J Y] at h
  have hy : pointEquiv (fun _ : Fin k => false) J y = v :=
    (pointEquiv (fun _ : Fin k => false) J).apply_symm_apply v
  rw [hy] at h
  funext q
  have he := congrArg ofBit (congrFun h q).symm
  simpa only [rowBits, ofBit_toBit, restrictedSecond, actualSecond,
    ZeroInformation.secondInput, y] using he

end
end DFVSGames.Soundness.ActualInputRows

namespace DFVSGames.Clean.AnswerBridge

open Integration.BinaryLinear
open Reduction
open Soundness
open Soundness.RepeatedGameBounds
open Soundness.RawPartnerTarget

noncomputable section
attribute [local instance] Classical.propDecidable

variable {k : ℕ} {Q Id Name : Type}

abbrev FirstInput := ZeroInformation.FirstInput (Fin k) Q Id
abbrev SecondInput := ZeroInformation.SecondInput (Fin k) Q Id Name

abbrev SourceAnswer (k : ℕ) := {x : ActualHomogeneous.E k // ActualHomogeneous.tau x = 1}
abbrev TargetAnswer (J : Finset (Fin k)) := {v : RawPoint J // v none = 1}

abbrev PointStrategies (J : Finset (Fin k)) := IncidenceExtraction.Strategies
  (FirstInput (k := k) (Q := Q) (Id := Id))
  (SecondInput (k := k) (Q := Q) (Id := Id) (Name := Name))
  (SourceAnswer k) (TargetAnswer J)

theorem firstAnswer_eq_embed (rhs : Fin k → Bool) (x : ActualHomogeneous.E k) :
    ActualPointAnswers.firstAnswer rhs x =
      (toBit x.1, fun j i =>
        toBit ((ActualHomogeneous.embed (fun j => ofBit (rhs j)) x).2 j i)) := by
  apply Prod.ext
  · rfl
  · funext j i
    fin_cases i
    · rfl
    · rfl
    · change (((rhs j && toBit x.1) ^^ toBit (x.2 j).1) ^^ toBit (x.2 j).2) =
        toBit (ofBit (rhs j) * x.1 + (x.2 j).1 + (x.2 j).2)
      have h := congrArg toBit (ActualCanonicalPullback.ofBit_and (rhs j) (toBit x.1))
      rw [toBit_ofBit, ofBit_toBit] at h
      rw [toBit_add, toBit_add, ← h]

def toOuterStrategy (J : Finset (Fin k)) (g : IncidenceExtraction.Incidence Id Name)
    (strategy : PointStrategies (Q := Q) (Id := Id) (Name := Name) J) :
    IncidenceExtraction.Strategies
      (FirstInput (k := k) (Q := Q) (Id := Id))
      (SecondInput (k := k) (Q := Q) (Id := Id) (Name := Name))
      (ActualProjection.FirstAnswer (Fin k)) (ActualProjection.SecondAnswer (Fin k)) where
  first qa := ActualPointAnswers.firstAnswer (fun j => g.rhs (qa.question j))
    (strategy.first qa).val
  second qb := ActualPointAnswers.secondAnswer
    (ActualPointAnswers.displayedRhs g.rhs qb.question) J (strategy.second qb).val

theorem toOuterStrategy_wins (J : Finset (Fin k))
    (g : IncidenceExtraction.Incidence Id Name)
    (strategy : PointStrategies (Q := Q) (Id := Id) (Name := Name) J)
    (qa : FirstInput (k := k) (Q := Q) (Id := Id))
    (qb : SecondInput (k := k) (Q := Q) (Id := Id) (Name := Name))
    (slot : Fin k → PartnerProjection.Slot)
    (hquestion : qb.question = RawPrivateTable.displayed J g.name qa.question slot)
    (hagreement : rawProjection (fun j => g.rhs (qa.question j)) J slot
      (strategy.first qa).val = (strategy.second qb).val) :
    (toOuterStrategy J g strategy).wins
      (ActualProjection.predicateGame g (PartnerMapCoordinates.activeOf J)) qa qb := by
  exact ActualPointAnswers.actual_accepts J g qa qb slot hquestion
    (strategy.first qa).val (strategy.second qb).val (strategy.first qa).property hagreement

open Soundness.ConditionalIncidences Soundness.BinaryRowTransport
open scoped BigOperators

variable {D : Type} [AddCommGroup D] [Module F2 D]

def finiteCoordinates [FiniteDimensional F2 D] :
    D ≃ₗ[F2] (Fin (Module.finrank F2 D) → F2) :=
  (Module.finBasis F2 D).equivFun

def bitsCoordinatesEquiv (coordinates : D ≃ₗ[F2] (Q → F2)) :
    D ≃ ZeroInformation.Bits Q :=
  coordinates.toEquiv.trans rowBitsEquiv

def encodeCoefficients (coordinates : D ≃ₗ[F2] (Q → F2))
    (J : Finset (Fin k)) (gamma : RawCoefficients J D) :
    RawCoefficients J (ZeroInformation.Bits Q) :=
  fun s => rowBits (coordinates (gamma s))

def coefficientsEquiv (coordinates : D ≃ₗ[F2] (Q → F2)) (J : Finset (Fin k)) :
    RawCoefficients J D ≃ RawCoefficients J (ZeroInformation.Bits Q) :=
  Equiv.piCongrRight (fun _ => bitsCoordinatesEquiv coordinates)

theorem uniform_encoded_coefficients [Fintype D] [Fintype Q]
    (coordinates : D ≃ₗ[F2] (Q → F2)) (J : Finset (Fin k))
    (F : RawCoefficients J (ZeroInformation.Bits Q) → ℝ) :
    (𝔼 gamma : RawCoefficients J D, F (encodeCoefficients coordinates J gamma)) =
      𝔼 bits : RawCoefficients J (ZeroInformation.Bits Q), F bits :=
  Fintype.expect_equiv (coefficientsEquiv coordinates J) _ F (fun _ => rfl)

theorem encoded_map_coefficients (coordinates : D ≃ₗ[F2] (Q → F2))
    (J : Finset (Fin k)) (Y : RawPoint J →ₗ[F2] D) :
    rowCoefficients J (gammaOfRawMap J (coordinates.toLinearMap.comp Y)) =
      encodeCoefficients coordinates J (gammaOfRawMap J Y) := rfl

theorem zeroSet_encodeCoefficients [Fintype Q] [DecidableEq Q] [DecidableEq D]
    (coordinates : D ≃ₗ[F2] (Q → F2))
    (J : Finset (Fin k)) (gamma : RawCoefficients J D) :
    zeroSet J (encodeCoefficients coordinates J gamma) = zeroSet J gamma := by
  ext j
  simp only [mem_zeroSet, encodeCoefficients]
  apply exists_congr
  intro hj
  change (rowBits (coordinates (gamma (some (.inr ⟨j, hj⟩)))) = ZeroInformation.zero) ↔
    gamma (some (.inr ⟨j, hj⟩)) = 0
  rw [rowBits_eq_zero]
  rw [← coordinates.map_zero]
  exact coordinates.injective.eq_iff

def rowPointStrategies (coordinates : D ≃ₗ[F2] (Q → F2))
    (J : Finset (Fin k)) (rhs : Id → Bool)
    (first : (Fin k → Id) → (ActualHomogeneous.E k →ₗ[F2] D) → SourceAnswer k)
    (second : (Fin k → Sum Id Name) → (RawPoint J →ₗ[F2] D) → TargetAnswer J) :
    PointStrategies (Q := Q) (Id := Id) (Name := Name) J where
  first qa := first qa.question
    (coordinates.symm.toLinearMap.comp (ActualInputRows.firstMap rhs qa))
  second qb := second qb.question
    (coordinates.symm.toLinearMap.comp (ActualInputRows.secondMap J qb))

theorem rowPointStrategies_first_actual [Fintype Q] [DecidableEq Q]
    (coordinates : D ≃ₗ[F2] (Q → F2))
    (J : Finset (Fin k)) (rhs : Id → Bool)
    (first : (Fin k → Id) → (ActualHomogeneous.E k →ₗ[F2] D) → SourceAnswer k)
    (second : (Fin k → Sum Id Name) → (RawPoint J →ₗ[F2] D) → TargetAnswer J)
    (occ : Fin k → Id) (slot : Fin k → PartnerProjection.Slot)
    (Y : RawPoint J →ₗ[F2] D) :
    (rowPointStrategies coordinates J rhs first second).first
      (actualFirst J
        (rowCoefficients J (gammaOfRawMap J (coordinates.toLinearMap.comp Y)))
        (fun j => (occ j, ConcreteExtraction.slotIndex (slot j)))) =
      first occ (Y.comp (rawProjection (fun j => rhs (occ j)) J slot)) := by
  change first occ (coordinates.symm.toLinearMap.comp
    (ActualInputRows.firstMap rhs _)) = _
  rw [ActualInputRows.firstMap_actual]
  congr 1
  apply LinearMap.ext
  intro x
  simp

theorem rowPointStrategies_second_actual [Fintype Q] [DecidableEq Q]
    (coordinates : D ≃ₗ[F2] (Q → F2))
    (J : Finset (Fin k)) (rhs : Id → Bool) (names : Id → Fin 3 → Name)
    (first : (Fin k → Id) → (ActualHomogeneous.E k →ₗ[F2] D) → SourceAnswer k)
    (second : (Fin k → Sum Id Name) → (RawPoint J →ₗ[F2] D) → TargetAnswer J)
    (draw : Draw (Fin k) Id) (Y : RawPoint J →ₗ[F2] D) :
    (rowPointStrategies coordinates J rhs first second).second
      (actualSecond J names
        (rowCoefficients J (gammaOfRawMap J (coordinates.toLinearMap.comp Y))) draw) =
      second
        (actualSecond J names
          (rowCoefficients J (gammaOfRawMap J (coordinates.toLinearMap.comp Y))) draw).question
        Y := by
  change second _ (coordinates.symm.toLinearMap.comp
    (ActualInputRows.secondMap J _)) = _
  rw [ActualInputRows.secondMap_actual]
  congr 1
  apply LinearMap.ext
  intro x
  simp

def defaultTargetAnswer (J : Finset (Fin k)) : TargetAnswer J :=
  ⟨Pi.single none 1, by simp⟩

def extendSupportedPolicy (J : Finset (Fin k)) (names : Id → Fin 3 → Name)
    (policy : RawPrivateTable.SupportedV J names → (RawPoint J →ₗ[F2] D) → TargetAnswer J)
    (question : Fin k → Sum Id Name) (Y : RawPoint J →ₗ[F2] D) : TargetAnswer J :=
  if h : question ∈ Set.range
      (fun e : RawPrivateTable.Extension k Id => RawPrivateTable.displayed J names e.1 e.2)
  then policy ⟨question, h⟩ Y else defaultTargetAnswer J

theorem extendSupportedPolicy_apply (J : Finset (Fin k)) (names : Id → Fin 3 → Name)
    (policy : RawPrivateTable.SupportedV J names → (RawPoint J →ₗ[F2] D) → TargetAnswer J)
    (V : RawPrivateTable.SupportedV J names) (Y : RawPoint J →ₗ[F2] D) :
    extendSupportedPolicy J names policy V.val Y = policy V Y := by
  unfold extendSupportedPolicy
  rw [dite_eq_left V.property]
  congr 1

end
end DFVSGames.Clean.AnswerBridge

namespace DFVSGames.Soundness.ConditionalIncidences
open scoped BigOperators

def coordinateReindex {A B X : Type} (e : B ≃ A) : (A → X) ≃ (B → X) where
  toFun f := fun b => f (e b)
  invFun g := fun a => g (e.symm a)
  left_inv f := by
    funext a
    exact congrArg f (e.apply_symm_apply a)
  right_inv g := by
    funext b
    exact congrArg g (e.symm_apply_apply b)

theorem raw_conditional_incidence_reindex
    {P D O N : Type} [Fintype P] [DecidableEq P]
    [Fintype D] [Zero D] [DecidableEq D]
    [Fintype O] [DecidableEq O] [DecidableEq N]
    (J : Finset P) (name : O → Fin 3 → N) (gamma : RawCoefficients J D)
    (observed : PositionOutside (zeroSet J gamma) → O × N)
    (hpos : 0 < Fintype.card (RawObservationFibre J name gamma observed))
    (r : ℕ) (e : Fin r ≃ PositionInside (zeroSet J gamma))
    (f : (Fin r → O × N) → ℚ) :
    average (fun sample : RawObservationFibre J name gamma observed =>
      f (fun i => incidence name (sample.val.2 (e i).val))) =
    average (fun fresh : Fin r → O × Fin 3 => f (fun i => incidence name (fresh i))) := by
  calc
    _ = average (fun fresh : InsideDraw (zeroSet J gamma) O =>
        f (fun i => incidence name (fresh (e i)))) :=
      raw_conditional_inside_average J name gamma observed hpos
        (fun fresh => f (fun i => incidence name (fresh (e i))))
    _ = _ := average_equiv (coordinateReindex e)
      (fun fresh : Fin r → O × Fin 3 => f (fun i => incidence name (fresh i)))

theorem raw_conditional_event_reindex_real
    {P D O N : Type} [Fintype P] [DecidableEq P]
    [Fintype D] [Zero D] [DecidableEq D]
    [Fintype O] [DecidableEq O] [DecidableEq N]
    (J : Finset P) (name : O → Fin 3 → N) (gamma : RawCoefficients J D)
    (observed : PositionOutside (zeroSet J gamma) → O × N)
    (hpos : 0 < Fintype.card (RawObservationFibre J name gamma observed))
    (r : ℕ) (e : Fin r ≃ PositionInside (zeroSet J gamma))
    (event : (Fin r → O × N) → Prop) [DecidablePred event] :
    ((∑ sample : RawObservationFibre J name gamma observed,
      if event (fun i => incidence name (sample.val.2 (e i).val)) then (1:ℝ) else 0) /
        Fintype.card (RawObservationFibre J name gamma observed)) =
    ((∑ fresh : Fin r → O × Fin 3,
      if event (fun i => incidence name (fresh i)) then (1:ℝ) else 0) /
        Fintype.card (Fin r → O × Fin 3)) := by
  have hQ := raw_conditional_incidence_reindex J name gamma observed hpos r e
    (fun q => if event q then (1:ℚ) else 0)
  have hR := congrArg (fun q : ℚ => (q : ℝ)) hQ
  simpa only [average, Rat.cast_div, Rat.cast_sum, Rat.cast_natCast,
    apply_ite, Rat.cast_one, Rat.cast_zero] using hR

end DFVSGames.Soundness.ConditionalIncidences

end OAI
