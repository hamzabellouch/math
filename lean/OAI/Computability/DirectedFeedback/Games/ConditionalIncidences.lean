import Mathlib
import OAI.Computability.DirectedFeedback.Games.KernelCardinality

namespace OAI

section

open scoped BigOperators

namespace DFVSGames.Soundness.ConditionalIncidences

noncomputable section

abbrev PositionInside {P : Type} (K : Finset P) := {j : P // j ∈ K}
abbrev PositionOutside {P : Type} (K : Finset P) := {j : P // j ∉ K}
abbrev Draw (P O : Type) := P → O × Fin 3
abbrev InsideDraw {P : Type} (K : Finset P) (O : Type) := PositionInside K → O × Fin 3

def incidence {O N : Type} (name : O → Fin 3 → N) (draw : O × Fin 3) : O × N :=
  (draw.1, name draw.1 draw.2)

def insideDraw {P O : Type} (K : Finset P) (sample : Draw P O) : InsideDraw K O :=
  fun j => sample j.val

def outsideRecord {P O N : Type} (K : Finset P) (name : O → Fin 3 → N)
    (sample : Draw P O) : PositionOutside K → O × N :=
  fun j => incidence name (sample j.val)

abbrev ObservationFibre {P O N : Type} (K : Finset P) (name : O → Fin 3 → N)
    (observed : PositionOutside K → O × N) :=
  {sample : Draw P O // outsideRecord K name sample = observed}

abbrev OutsideFibre {P O N : Type} (K : Finset P) (name : O → Fin 3 → N)
    (observed : PositionOutside K → O × N) :=
  {sample : PositionOutside K → O × Fin 3 //
    (fun j => incidence name (sample j)) = observed}

instance observationFibreFintype {P O N : Type} [Fintype P] [Fintype O]
    (K : Finset P) (name : O → Fin 3 → N) (observed : PositionOutside K → O × N) :
    Fintype (ObservationFibre K name observed) := Fintype.ofFinite _

instance outsideFibreFintype {P O N : Type} [Fintype P] [Fintype O]
    (K : Finset P) (name : O → Fin 3 → N) (observed : PositionOutside K → O × N) :
    Fintype (OutsideFibre K name observed) := Fintype.ofFinite _

def observationFibreEquiv {P O N : Type} [DecidableEq P]
    (K : Finset P) (name : O → Fin 3 → N)
    (observed : PositionOutside K → O × N) :
    ObservationFibre K name observed ≃ InsideDraw K O × OutsideFibre K name observed where
  toFun sample :=
    (insideDraw K sample.val, ⟨fun j => sample.val j.val, sample.property⟩)
  invFun pieces :=
    ⟨fun j => if hj : j ∈ K then pieces.1 ⟨j, hj⟩ else pieces.2.val ⟨j, hj⟩, by
      funext j
      simp only [outsideRecord, j.property, ↓reduceDIte]
      exact congrFun pieces.2.property j⟩
  left_inv sample := by
    apply Subtype.ext
    funext j
    simp only [insideDraw]
    split <;> rfl
  right_inv pieces := by
    apply Prod.ext
    · funext j
      simp [insideDraw, j.property]
    · apply Subtype.ext
      funext j
      simp [j.property]

def average {A : Type} [Fintype A] (f : A → ℚ) : ℚ :=
  (∑ a, f a) / Fintype.card A

theorem average_equiv {A B : Type} [Fintype A] [Fintype B] (e : A ≃ B) (f : B → ℚ) :
    average (fun a => f (e a)) = average f := by
  unfold average
  rw [e.sum_comp, Fintype.card_congr e]

theorem average_product_left {A B : Type} [Fintype A] [Fintype B]
    (hB : Fintype.card B ≠ 0) (f : A → ℚ) :
    average (fun ab : A × B => f ab.1) = average f := by
  unfold average
  rw [Fintype.sum_prod_type]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Fintype.card_prod, Nat.cast_mul]
  rw [← Finset.mul_sum]
  have hBq : (Fintype.card B : ℚ) ≠ 0 := by exact_mod_cast hB
  rw [mul_comm (Fintype.card A : ℚ)]
  exact mul_div_mul_left _ _ hBq

theorem average_product_mul {A B : Type} [Fintype A] [Fintype B]
    (f : A → ℚ) (g : B → ℚ) :
    average (fun ab : A × B => f ab.1 * g ab.2) = average f * average g := by
  unfold average
  rw [Fintype.sum_prod_type]
  simp_rw [← Finset.mul_sum]
  rw [← Finset.sum_mul]
  simp only [Fintype.card_prod, Nat.cast_mul]
  exact (div_mul_div_comm _ _ _ _).symm

theorem average_coordinate_product {A X : Type} [Fintype A] [DecidableEq A] [Fintype X]
    (f : A → X → ℚ) :
    average (fun sample : A → X => ∏ a, f a (sample a)) = ∏ a, average (f a) := by
  unfold average
  rw [← Fintype.prod_sum]
  simp only [Fintype.card_pi, Nat.cast_prod]
  exact (Finset.prod_div_distrib _ _).symm

theorem uniform_conditional_ratio {A : Type} [Fintype A]
    (p : A → Prop) [Fintype {a // p a}]
    (hpos : 0 < Fintype.card {a // p a}) (f : {a // p a} → ℚ) :
    ((∑ a, f a) / (Fintype.card A : ℚ)) /
        ((Fintype.card {a // p a} : ℚ) / Fintype.card A) = average f := by
  have hA : Fintype.card A ≠ 0 :=
    Nat.ne_of_gt (Nat.lt_of_lt_of_le hpos (Fintype.card_subtype_le p))
  have hAq : (Fintype.card A : ℚ) ≠ 0 := by exact_mod_cast hA
  exact div_div_div_cancel_right₀ hAq _ _

section ConditionalLaw

variable {P O N : Type} [Fintype P] [DecidableEq P] [Fintype O]

theorem conditional_inside_average (K : Finset P) (name : O → Fin 3 → N)
    (observed : PositionOutside K → O × N)
    (hpos : 0 < Fintype.card (ObservationFibre K name observed))
    (f : InsideDraw K O → ℚ) :
    average (fun sample : ObservationFibre K name observed => f (insideDraw K sample.val)) =
      average f := by
  let e := observationFibreEquiv K name observed
  have hcard : Fintype.card (ObservationFibre K name observed) =
      Fintype.card (InsideDraw K O) * Fintype.card (OutsideFibre K name observed) := by
    rw [Fintype.card_congr e, Fintype.card_prod]
  have hout : Fintype.card (OutsideFibre K name observed) ≠ 0 := by
    intro hz
    rw [hcard, hz, Nat.mul_zero] at hpos
    exact (Nat.lt_irrefl 0) hpos
  calc
    average (fun sample : ObservationFibre K name observed => f (insideDraw K sample.val)) =
        average (fun pieces : InsideDraw K O × OutsideFibre K name observed => f pieces.1) :=
      average_equiv e (fun pieces => f pieces.1)
    _ = average f := average_product_left hout f

theorem conditional_incidence_average (K : Finset P) (name : O → Fin 3 → N)
    (observed : PositionOutside K → O × N)
    (hpos : 0 < Fintype.card (ObservationFibre K name observed))
    (f : (PositionInside K → O × N) → ℚ) :
    average (fun sample : ObservationFibre K name observed =>
      f (fun j => incidence name (sample.val j.val))) =
    average (fun fresh : InsideDraw K O => f (fun j => incidence name (fresh j))) := by
  exact conditional_inside_average K name observed hpos
    (fun fresh => f (fun j => incidence name (fresh j)))

end ConditionalLaw

abbrev RawSlot {P : Type} (J : Finset P) :=
  Option ((PositionOutside J × Fin 2) ⊕ PositionInside J)

abbrev RawCoefficients {P : Type} (J : Finset P) (D : Type) := RawSlot J → D

def zeroSet {P D : Type} [DecidableEq P] [Zero D] [DecidableEq D]
    (J : Finset P) (gamma : RawCoefficients J D) : Finset P :=
  J.attach.filter (fun j => gamma (some (.inr j)) = 0) |>.map ⟨Subtype.val, Subtype.val_injective⟩

theorem mem_zeroSet {P D : Type} [DecidableEq P] [Zero D] [DecidableEq D]
    (J : Finset P) (gamma : RawCoefficients J D) (j : P) :
    j ∈ zeroSet J gamma ↔ ∃ hj : j ∈ J, gamma (some (.inr ⟨j, hj⟩)) = 0 := by
  simp [zeroSet]

abbrev RawSample {P : Type} (J : Finset P) (D O : Type) :=
  RawCoefficients J D × Draw P O

abbrev RawObservationFibre {P D O N : Type} [DecidableEq P] [Zero D] [DecidableEq D]
    (J : Finset P) (name : O → Fin 3 → N) (gamma : RawCoefficients J D)
    (observed : PositionOutside (zeroSet J gamma) → O × N) :=
  {sample : RawSample J D O // sample.1 = gamma ∧
    outsideRecord (zeroSet J gamma) name sample.2 = observed}

instance rawObservationFibreFintype {P D O N : Type} [Fintype P] [DecidableEq P]
    [Fintype D] [Zero D] [DecidableEq D] [Fintype O]
    (J : Finset P) (name : O → Fin 3 → N) (gamma : RawCoefficients J D)
    (observed : PositionOutside (zeroSet J gamma) → O × N) :
    Fintype (RawObservationFibre J name gamma observed) := Fintype.ofFinite _

def rawObservationFibreEquiv {P D O N : Type} [DecidableEq P] [Zero D] [DecidableEq D]
    (J : Finset P) (name : O → Fin 3 → N) (gamma : RawCoefficients J D)
    (observed : PositionOutside (zeroSet J gamma) → O × N) :
    RawObservationFibre J name gamma observed ≃
      ObservationFibre (zeroSet J gamma) name observed where
  toFun sample := ⟨sample.val.2, sample.property.2⟩
  invFun sample := ⟨(gamma, sample.val), rfl, sample.property⟩
  left_inv sample := by
    apply Subtype.ext
    exact Prod.ext sample.property.1.symm rfl
  right_inv sample := rfl

theorem raw_conditional_inside_average {P D O N : Type} [Fintype P] [DecidableEq P]
    [Fintype D] [Zero D] [DecidableEq D] [Fintype O] [DecidableEq O] [DecidableEq N]
    (J : Finset P) (name : O → Fin 3 → N) (gamma : RawCoefficients J D)
    (observed : PositionOutside (zeroSet J gamma) → O × N)
    (hpos : 0 < Fintype.card (RawObservationFibre J name gamma observed))
    (f : InsideDraw (zeroSet J gamma) O → ℚ) :
    average (fun sample : RawObservationFibre J name gamma observed =>
      f (insideDraw (zeroSet J gamma) sample.val.2)) = average f := by
  let e := rawObservationFibreEquiv J name gamma observed
  have hpos' : 0 < Fintype.card (ObservationFibre (zeroSet J gamma) name observed) := by
    rwa [Fintype.card_congr e] at hpos
  calc
    average (fun sample : RawObservationFibre J name gamma observed =>
        f (insideDraw (zeroSet J gamma) sample.val.2)) =
      average (fun sample : ObservationFibre (zeroSet J gamma) name observed =>
        f (insideDraw (zeroSet J gamma) sample.val)) := by
      exact average_equiv e (fun sample : ObservationFibre (zeroSet J gamma) name observed =>
        f (insideDraw (zeroSet J gamma) sample.val))
    _ = average f := conditional_inside_average _ name observed hpos' f

theorem raw_conditional_ratio {P D O N : Type} [Fintype P] [DecidableEq P]
    [Fintype D] [Zero D] [DecidableEq D] [Fintype O] [DecidableEq O] [DecidableEq N]
    (J : Finset P) (name : O → Fin 3 → N) (gamma : RawCoefficients J D)
    (observed : PositionOutside (zeroSet J gamma) → O × N)
    (hpos : 0 < Fintype.card (RawObservationFibre J name gamma observed))
    (f : InsideDraw (zeroSet J gamma) O → ℚ) :
    ((∑ sample : RawObservationFibre J name gamma observed,
        f (insideDraw (zeroSet J gamma) sample.val.2)) / Fintype.card (RawSample J D O)) /
      ((Fintype.card (RawObservationFibre J name gamma observed) : ℚ) /
        Fintype.card (RawSample J D O)) = average f := by
  rw [uniform_conditional_ratio _ hpos]
  exact raw_conditional_inside_average J name gamma observed hpos f

theorem raw_conditional_incidence_average {P D O N : Type} [Fintype P] [DecidableEq P]
    [Fintype D] [Zero D] [DecidableEq D] [Fintype O] [DecidableEq O] [DecidableEq N]
    (J : Finset P) (name : O → Fin 3 → N) (gamma : RawCoefficients J D)
    (observed : PositionOutside (zeroSet J gamma) → O × N)
    (hpos : 0 < Fintype.card (RawObservationFibre J name gamma observed))
    (f : (PositionInside (zeroSet J gamma) → O × N) → ℚ) :
    average (fun sample : RawObservationFibre J name gamma observed =>
      f (fun j => incidence name (sample.val.2 j.val))) =
    average (fun fresh : InsideDraw (zeroSet J gamma) O => f (fun j => incidence name (fresh j))) := by
  exact raw_conditional_inside_average J name gamma observed hpos
    (fun fresh => f (fun j => incidence name (fresh j)))

theorem raw_conditional_product_incidence {P D O N : Type} [Fintype P] [DecidableEq P]
    [Fintype D] [Zero D] [DecidableEq D] [Fintype O] [DecidableEq O] [DecidableEq N]
    (J : Finset P) (name : O → Fin 3 → N) (gamma : RawCoefficients J D)
    (observed : PositionOutside (zeroSet J gamma) → O × N)
    (hpos : 0 < Fintype.card (RawObservationFibre J name gamma observed))
    (f : PositionInside (zeroSet J gamma) → O × N → ℚ) :
    average (fun sample : RawObservationFibre J name gamma observed =>
      ∏ j, f j (incidence name (sample.val.2 j.val))) =
    ∏ j, average (fun fresh : O × Fin 3 => f j (incidence name fresh)) := by
  calc
    _ = average (fun fresh : InsideDraw (zeroSet J gamma) O =>
        ∏ j, f j (incidence name (fresh j))) :=
      raw_conditional_inside_average J name gamma observed hpos
        (fun fresh => ∏ j, f j (incidence name (fresh j)))
    _ = _ := average_coordinate_product (fun j fresh => f j (incidence name fresh))

end

end DFVSGames.Soundness.ConditionalIncidences
end

section

open scoped BigOperators

namespace DFVSGames.Soundness.PartnerMapCoordinates

open PartnerProjection
open ConditionalIncidences (PositionInside PositionOutside RawSlot RawCoefficients average)
open DFVSGames.Integration.BinaryLinear (F2 ofBit toBit)

noncomputable section

variable {P : Type} [DecidableEq P] (rhs : P → Bool) (J : Finset P)

def activeOf (J : Finset P) (j : P) : Bool := decide (j ∈ J)

def inactiveOfOutside (j : PositionOutside J) : PartnerLinear.Inactive (activeOf J) :=
  ⟨j.val, by simp [activeOf, j.property]⟩

def activeOfInside (j : PositionInside J) : PartnerLinear.Active (activeOf J) :=
  ⟨j.val, by simp [activeOf, j.property]⟩

def outsideOfInactive (j : PartnerLinear.Inactive (activeOf J)) : PositionOutside J :=
  ⟨j.val, by simpa [activeOf] using j.property⟩

def insideOfActive (j : PartnerLinear.Active (activeOf J)) : PositionInside J :=
  ⟨j.val, by simpa [activeOf] using j.property⟩

def tupleToRaw (v : PartnerLinear.PartnerCoordinates (activeOf J)) : RawSlot J → F2
  | none => v.1
  | some (.inl (j, i)) =>
      if i = 0 then (v.2.1 (inactiveOfOutside J j)).1
      else (v.2.1 (inactiveOfOutside J j)).2
  | some (.inr j) => v.2.2 (activeOfInside J j)

def tupleFromRaw (f : RawSlot J → F2) : PartnerLinear.PartnerCoordinates (activeOf J) :=
  (f none,
    (fun j => (f (some (.inl (outsideOfInactive J j, 0))),
      f (some (.inl (outsideOfInactive J j, 1)))),
      fun j => f (some (.inr (insideOfActive J j)))))

def tupleRawEquiv : PartnerLinear.PartnerCoordinates (activeOf J) ≃ₗ[F2] (RawSlot J → F2) where
  toFun := tupleToRaw J
  invFun := tupleFromRaw J
  left_inv v := by
    apply Prod.ext
    · rfl
    · apply Prod.ext
      · funext j
        apply Prod.ext <;> rfl
      · funext j
        rfl
  right_inv f := by
    funext s
    rcases s with _ | (⟨j, i⟩ | j)
    · rfl
    · fin_cases i <;> rfl
    · rfl
  map_add' x y := by
    funext s
    rcases s with _ | (⟨j, i⟩ | j)
    · rfl
    · fin_cases i <;> rfl
    · rfl
  map_smul' c x := by
    funext s
    rcases s with _ | (⟨j, i⟩ | j)
    · rfl
    · fin_cases i <;> rfl
    · rfl

def pointEquiv : PartnerPoint rhs (activeOf J) ≃ₗ[F2] (RawSlot J → F2) :=
  (PartnerLinear.partnerLinearEquiv rhs (activeOf J)).trans (tupleRawEquiv J)

@[simp] theorem pointEquiv_none (y : PartnerPoint rhs (activeOf J)) :
    pointEquiv rhs J y none = ofBit y.homogeneous := rfl

@[simp] theorem pointEquiv_full_first (y : PartnerPoint rhs (activeOf J))
    (j : PositionOutside J) :
    pointEquiv rhs J y (some (.inl (j, 0))) = ofBit (y.full j.val).first := rfl

@[simp] theorem pointEquiv_full_second (y : PartnerPoint rhs (activeOf J))
    (j : PositionOutside J) :
    pointEquiv rhs J y (some (.inl (j, 1))) = ofBit (y.full j.val).second := rfl

@[simp] theorem pointEquiv_single (y : PartnerPoint rhs (activeOf J))
    (j : PositionInside J) :
    pointEquiv rhs J y (some (.inr j)) = ofBit (y.single j.val) := rfl

variable [Fintype P]

def partnerBasis : Module.Basis (RawSlot J) F2 (PartnerPoint rhs (activeOf J)) :=
  Module.Basis.ofEquivFun (pointEquiv rhs J)

variable (R : Type) [AddCommGroup R] [Module F2 R]

def mapEquiv : RawCoefficients J R ≃ₗ[F2] (PartnerPoint rhs (activeOf J) →ₗ[F2] R) :=
  (partnerBasis rhs J).constr F2

def coefficients (Y : PartnerPoint rhs (activeOf J) →ₗ[F2] R) : RawCoefficients J R :=
  (mapEquiv rhs J R).symm Y

theorem map_coefficients (Y : PartnerPoint rhs (activeOf J) →ₗ[F2] R) :
    mapEquiv rhs J R (coefficients rhs J R Y) = Y :=
  (mapEquiv rhs J R).apply_symm_apply Y

theorem coefficients_map (gamma : RawCoefficients J R) :
    coefficients rhs J R (mapEquiv rhs J R gamma) = gamma :=
  (mapEquiv rhs J R).symm_apply_apply gamma

theorem mapEquiv_apply (gamma : RawCoefficients J R) (y : PartnerPoint rhs (activeOf J)) :
    mapEquiv rhs J R gamma y = ∑ s, pointEquiv rhs J y s • gamma s := by
  rw [mapEquiv, Module.Basis.constr_apply_fintype]
  simp only [partnerBasis, Module.Basis.equivFun_ofEquivFun]

theorem mapEquiv_expansion (gamma : RawCoefficients J R) (y : PartnerPoint rhs (activeOf J)) :
    mapEquiv rhs J R gamma y =
      ofBit y.homogeneous • gamma none +
        (∑ j : PositionOutside J,
          (ofBit (y.full j.val).first • gamma (some (.inl (j, 0))) +
            ofBit (y.full j.val).second • gamma (some (.inl (j, 1))))) +
        ∑ j : PositionInside J, ofBit (y.single j.val) • gamma (some (.inr j)) := by
  rw [mapEquiv_apply, Fintype.sum_option, Fintype.sum_sum_type, Fintype.sum_prod_type]
  simp only [Fin.sum_univ_two, pointEquiv_none, pointEquiv_full_first,
    pointEquiv_full_second, pointEquiv_single]
  simp only [add_assoc]

theorem every_map_expansion (Y : PartnerPoint rhs (activeOf J) →ₗ[F2] R)
    (y : PartnerPoint rhs (activeOf J)) :
    Y y = ∑ s, pointEquiv rhs J y s • coefficients rhs J R Y s := by
  rw [← mapEquiv_apply, map_coefficients]

theorem pullback_expansion (gamma : RawCoefficients J R) (slot : P → Slot)
    (x : SourcePoint rhs) :
    mapEquiv rhs J R gamma (PartnerLinear.projection rhs (activeOf J) slot x) =
      ofBit x.homogeneous • gamma none +
        (∑ j : PositionOutside J,
          (ofBit (x.coordinates j.val).first • gamma (some (.inl (j, 0))) +
            ofBit (x.coordinates j.val).second • gamma (some (.inl (j, 1))))) +
        ∑ j : PositionInside J,
          ofBit (retained (slot j.val) (x.coordinates j.val)) • gamma (some (.inr j)) := by
  rw [mapEquiv_expansion]
  congr 1
  · congr 1
    apply Finset.sum_congr rfl
    intro j _
    simp [PartnerLinear.projection_apply, project, activeOf, j.property]
  · apply Finset.sum_congr rfl
    intro j _
    simp [PartnerLinear.projection_apply, project, activeOf, j.property]

instance partnerMapsFintype [Fintype R] :
    Fintype (PartnerPoint rhs (activeOf J) →ₗ[F2] R) := by
  classical
  exact Fintype.ofEquiv (RawCoefficients J R) (mapEquiv rhs J R).toEquiv

theorem uniform_coefficients_maps [Fintype R]
    (H : (PartnerPoint rhs (activeOf J) →ₗ[F2] R) → ℚ) :
    average (fun gamma : RawCoefficients J R => H (mapEquiv rhs J R gamma)) = average H :=
  ConditionalIncidences.average_equiv (mapEquiv rhs J R).toEquiv H

theorem uniform_map_coefficients_product [Fintype R]
    (H : RawSlot J → R → ℚ) :
    average (fun Y : PartnerPoint rhs (activeOf J) →ₗ[F2] R =>
      ∏ s, H s (coefficients rhs J R Y s)) = ∏ s, average (H s) := by
  calc
    _ = average (fun gamma : RawCoefficients J R => ∏ s, H s (gamma s)) :=
      ConditionalIncidences.average_equiv (mapEquiv rhs J R).symm.toEquiv
        (fun gamma => ∏ s, H s (gamma s))
    _ = _ := ConditionalIncidences.average_coordinate_product H

end

end DFVSGames.Soundness.PartnerMapCoordinates
end

namespace DFVSGames.Soundness.IncidenceExtraction

abbrev Triple := Fin 3 → Bool

def xorTriple (x : Triple) : Bool := (x 0 ^^ x 1) ^^ x 2

structure Incidence (Occurrence Name : Type) where
  name : Occurrence → Fin 3 → Name
  rhs : Occurrence → Bool

def Incidence.accepts {Occurrence Name : Type}
    (g : Incidence Occurrence Name) (o : Occurrence) (i : Fin 3)
    (a : Triple) (b : Bool) : Prop :=
  xorTriple a = g.rhs o ∧ a i = b

def Incidence.namedAccepts {Occurrence Name : Type}
    (g : Incidence Occurrence Name) (o : Occurrence) (n : Name)
    (a : Triple) (b : Bool) : Prop :=
  ∃ i, g.name o i = n ∧ g.accepts o i a b

theorem Incidence.accepts_implies_namedAccepts {Occurrence Name : Type}
    (g : Incidence Occurrence Name) (o : Occurrence) (i : Fin 3)
    (a : Triple) (b : Bool) (h : g.accepts o i a b) :
    g.namedAccepts o (g.name o i) a b :=
  ⟨i, rfl, h⟩

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

end DFVSGames.Soundness.IncidenceExtraction

namespace DFVSGames.Soundness.ConcreteExtraction

open PartnerProjection IncidenceExtraction

def slotIndex : PartnerProjection.Slot → Fin 3
  | .first => 0
  | .second => 1
  | .third => 2

def tripleCoordinates (x : PartnerProjection.Triple) : IncidenceExtraction.Triple :=
  fun i => if i = 0 then x.first else if i = 1 then x.second else x.third

theorem parity_coordinates (x : PartnerProjection.Triple) :
    IncidenceExtraction.xorTriple (tripleCoordinates x) = PartnerProjection.parity x := rfl

theorem retained_coordinates (x : PartnerProjection.Triple) (i : PartnerProjection.Slot) :
    tripleCoordinates x (slotIndex i) = PartnerProjection.retained i x := by
  cases i <;> rfl

def fullPoint {P : Type} {rhs : P → Bool}
    (x : PartnerProjection.SourcePoint rhs) : IncidenceExtraction.FullPoint P :=
  ⟨x.homogeneous, fun j => tripleCoordinates (x.coordinates j)⟩

def partnerPoint {P : Type} {rhs active : P → Bool}
    (x : PartnerProjection.PartnerPoint rhs active) : IncidenceExtraction.PartnerPoint P :=
  ⟨x.homogeneous, x.single⟩

theorem actual_projection_accepts
    {P O N : Type} (g : IncidenceExtraction.Incidence O N) (u : P → O)
    (active : P → Bool) (slot : P → PartnerProjection.Slot)
    (x : PartnerProjection.SourcePoint (fun j => g.rhs (u j)))
    (y : PartnerProjection.PartnerPoint (fun j => g.rhs (u j)) active)
    (hone : x.homogeneous = true)
    (hproject : PartnerProjection.project (fun j => g.rhs (u j)) active slot x = y) :
    IncidenceExtraction.AugmentedAccepts g u (fun j => active j = true)
      (fun j => slotIndex (slot j)) (fullPoint x) (partnerPoint y) := by
  subst y
  constructor
  · intro j
    exact x.valid j
  constructor
  · exact hone
  constructor
  · exact hone
  intro j hj
  change tripleCoordinates (x.coordinates j) (slotIndex (slot j)) =
    (if active j then PartnerProjection.retained (slot j) (x.coordinates j) else false)
  rw [hj]
  exact retained_coordinates _ _

theorem actual_projection_implies_named_repetition
    {P R O N : Type} (g : IncidenceExtraction.Incidence O N) (u : P → O)
    (active : P → Bool) (slot : P → PartnerProjection.Slot) (embed : R → P)
    (x : PartnerProjection.SourcePoint (fun j => g.rhs (u j)))
    (y : PartnerProjection.PartnerPoint (fun j => g.rhs (u j)) active)
    (hinside : ∀ r, active (embed r) = true)
    (hone : x.homogeneous = true)
    (hproject : PartnerProjection.project (fun j => g.rhs (u j)) active slot x = y) :
    ∀ r, g.namedAccepts (u (embed r))
      (g.name (u (embed r)) (slotIndex (slot (embed r))))
      (tripleCoordinates (x.coordinates (embed r))) (y.single (embed r)) := by
  exact IncidenceExtraction.augmented_accepts_implies_named_repeated_accepts g u
    (fun j => active j = true) (fun j => slotIndex (slot j)) embed
    (fullPoint x) (partnerPoint y) hinside
    (actual_projection_accepts g u active slot x y hone hproject)

end DFVSGames.Soundness.ConcreteExtraction

namespace DFVSGames.Reduction.ActualHomogeneous

open Integration.BinaryLinear
open scoped BigOperators

abbrev E (k : Nat) := F2 × (Fin k → F2 × F2)
abbrev Ambient (k : Nat) := F2 × (Fin k → Fin 3 → F2)

variable {k : Nat}

def tau : E k →ₗ[F2] F2 := LinearMap.fst F2 _ _
def hBasis (k : Nat) : E k := (1, 0)
def firstBasis (j : Fin k) : E k := (0, Pi.single j (1, 0))
def secondBasis (j : Fin k) : E k := (0, Pi.single j (0, 1))
def coordinateBasis (j : Fin k) (i : Fin 2) : E k :=
  if i = 0 then firstBasis j else secondBasis j

@[simp] theorem tau_hBasis : tau (hBasis k) = 1 := rfl
@[simp] theorem tau_firstBasis (j : Fin k) : tau (firstBasis j) = 0 := rfl
@[simp] theorem tau_secondBasis (j : Fin k) : tau (secondBasis j) = 0 := rfl

theorem pair_fst_ite (p : Prop) [Decidable p] (a b : F2 × F2) :
    (if p then a else b).1 = if p then a.1 else b.1 := by split_ifs <;> rfl
theorem pair_snd_ite (p : Prop) [Decidable p] (a b : F2 × F2) :
    (if p then a else b).2 = if p then a.2 else b.2 := by split_ifs <;> rfl

theorem coordinate_decomposition (x : E k) :
    x = x.1 • hBasis k + ∑ j : Fin k,
      ((x.2 j).1 • firstBasis j + (x.2 j).2 • secondBasis j) := by
  apply Prod.ext
  · simp [hBasis, firstBasis, secondBasis, Prod.fst_sum]
  · funext j
    apply Prod.ext <;>
      simp [hBasis, firstBasis, secondBasis, Pi.single_apply,
        Prod.snd_sum, Prod.fst_sum, Finset.sum_apply, pair_fst_ite, pair_snd_ite]

theorem linearMap_expansion {R : Type*} [AddCommGroup R] [Module F2 R]
    (X : E k →ₗ[F2] R) (x : E k) :
    X x = x.1 • X (hBasis k) + ∑ j : Fin k,
      ((x.2 j).1 • X (firstBasis j) + (x.2 j).2 • X (secondBasis j)) := by
  conv_lhs => rw [coordinate_decomposition x]
  simp

def homogeneous (b : Fin k → F2) : Submodule F2 (Ambient k) where
  carrier := {x | ∀ j, x.2 j 0 + x.2 j 1 + x.2 j 2 = b j * x.1}
  zero_mem' := by simp
  add_mem' := by
    intro x y hx hy j
    change (x.2 j 0 + y.2 j 0) + (x.2 j 1 + y.2 j 1) +
      (x.2 j 2 + y.2 j 2) = b j * (x.1 + y.1)
    calc
      _ = (x.2 j 0 + x.2 j 1 + x.2 j 2) +
          (y.2 j 0 + y.2 j 1 + y.2 j 2) := by ring
      _ = b j * x.1 + b j * y.1 := by rw [hx j, hy j]
      _ = _ := by ring
  smul_mem' := by
    intro c x hx j
    change c * x.2 j 0 + c * x.2 j 1 + c * x.2 j 2 = b j * (c * x.1)
    calc
      _ = c * (x.2 j 0 + x.2 j 1 + x.2 j 2) := by ring
      _ = c * (b j * x.1) := by rw [hx j]
      _ = _ := by ring

def embed (b : Fin k → F2) : E k →ₗ[F2] Ambient k where
  toFun x := (x.1, fun j => ![(x.2 j).1, (x.2 j).2,
    b j * x.1 + (x.2 j).1 + (x.2 j).2])
  map_add' x y := by
    apply Prod.ext
    · rfl
    · funext j i
      fin_cases i <;> simp ; ring
  map_smul' c x := by
    apply Prod.ext
    · rfl
    · funext j i
      fin_cases i <;> simp [smul_eq_mul] ; ring

theorem embed_mem (b : Fin k → F2) (x : E k) : embed b x ∈ homogeneous b := by
  intro j
  change (x.2 j).1 + (x.2 j).2 + (b j * x.1 + (x.2 j).1 + (x.2 j).2) = b j * x.1
  have h1 := CharTwo.add_self_eq_zero ((x.2 j).1)
  have h2 := CharTwo.add_self_eq_zero ((x.2 j).2)
  calc
    _ = b j * x.1 + (((x.2 j).1 + (x.2 j).1) + ((x.2 j).2 + (x.2 j).2)) := by ring
    _ = _ := by rw [h1, h2]; simp

def equivalence (b : Fin k → F2) : E k ≃ₗ[F2] homogeneous b where
  toFun x := ⟨embed b x, embed_mem b x⟩
  invFun x := (x.1.1, fun j => (x.1.2 j 0, x.1.2 j 1))
  left_inv x := by rfl
  right_inv x := by
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · funext j i
      fin_cases i
      · rfl
      · rfl
      · change b j * x.1.1 + x.1.2 j 0 + x.1.2 j 1 = x.1.2 j 2
        rw [← x.property j]
        have h1 := CharTwo.add_self_eq_zero (x.1.2 j 0)
        have h2 := CharTwo.add_self_eq_zero (x.1.2 j 1)
        calc
          _ = x.1.2 j 2 + ((x.1.2 j 0 + x.1.2 j 0) + (x.1.2 j 1 + x.1.2 j 1)) := by ring
          _ = _ := by rw [h1, h2]; simp
  map_add' x y := Subtype.ext ((embed b).map_add x y)
  map_smul' c x := Subtype.ext ((embed b).map_smul c x)

theorem finrank_E (k : Nat) : Module.finrank F2 (E k) = 1 + 2 * k := by
  simp [E, Module.finrank_prod, Module.finrank_pi_fintype, Nat.mul_comm]

theorem finrank_homogeneous (b : Fin k → F2) :
    Module.finrank F2 (homogeneous b) = 1 + 2 * k := by
  rw [← (equivalence b).finrank_eq, finrank_E]

end DFVSGames.Reduction.ActualHomogeneous

end OAI
