import Mathlib
import OAI.Computability.DirectedFeedback.Games.ConditionalIncidences

namespace OAI

namespace DFVSGames.Reduction.ActualCanonical

open Integration.BinaryLinear ActualHomogeneous
open scoped BigOperators

universe u v w
variable {k : Nat}
variable {Name : Type u} {Id : Type v} {R : Type w}
variable [AddCommGroup R] [Module F2 R] [DecidableEq R]

inductive Record (Name : Type u) (Id : Type v) (R : Type w)
  | blank
  | single (name : Name) (coefficient : R)
  | full (occurrence : Id) (coefficients : Fin 3 → R)
  deriving DecidableEq

def recordEquiv : Record Name Id R ≃ Unit ⊕ ((Name × R) ⊕ (Id × (Fin 3 → R))) where
  toFun r := match r with
    | .blank => .inl ()
    | .single n c => .inr (.inl (n,c))
    | .full e a => .inr (.inr (e,a))
  invFun r := match r with
    | .inl _ => .blank
    | .inr (.inl (n,c)) => .single n c
    | .inr (.inr (e,a)) => .full e a
  left_inv r := by cases r <;> rfl
  right_inv r := by rcases r with u | (p | p) <;> cases ‹_› <;> rfl

noncomputable instance [Fintype Name] [Fintype Id] [Fintype R] :
    Fintype (Record Name Id R) := Fintype.ofEquiv _ recordEquiv.symm

abbrev Data (k : Nat) (Name : Type u) (Id : Type v) (R : Type w) :=
  R × (Fin k → Record Name Id R)

def pivot (a : Fin 3 → R) : R :=
  if a 0 = a 1 then a 0 else if a 0 = a 2 then a 0 else a 2

def translate (a : Fin 3 → R) (t : R) : Fin 3 → R := fun i => a i + t
def normalize (a : Fin 3 → R) : Fin 3 → R := translate a (pivot a)

def record (names : Id → Fin 3 → Name) (e : Id) (a : Fin 3 → R) :
    Record Name Id R :=
  if a 0 = a 1 then
      if a 0 = a 2 then .blank else .single (names e 2) (a 2 + a 0)
    else if a 0 = a 2 then .single (names e 1) (a 1 + a 0)
    else if a 1 = a 2 then .single (names e 0) (a 0 + a 2)
    else .full e (normalize a)

def data (occ : Fin k → Id) (names : Id → Fin 3 → Name)
    (rhs : Id → F2) (z : R) (a : Fin k → Fin 3 → R) : Data k Name Id R :=
  (z + ∑ j, rhs (occ j) • pivot (a j), fun j => record names (occ j) (a j))

def standardTriple (X : E k →ₗ[F2] R) (j : Fin k) : Fin 3 → R :=
  ![X (firstBasis j), X (secondBasis j), 0]

def canonical (occ : Fin k → Id) (names : Id → Fin 3 → Name)
    (rhs : Id → F2) (X : E k →ₗ[F2] R) : Data k Name Id R :=
  data occ names rhs (X (hBasis k)) (standardTriple X)

def ambientEval (b : Fin k → F2) (z : R) (a : Fin k → Fin 3 → R) (x : E k) : R :=
  x.1 • z + ∑ j, ((x.2 j).1 • a j 0 + (x.2 j).2 • a j 1 +
    (b j * x.1 + (x.2 j).1 + (x.2 j).2) • a j 2)

def Represents (b : Fin k → F2) (z : R) (a : Fin k → Fin 3 → R)
    (X : E k →ₗ[F2] R) : Prop := ∀ x, ambientEval b z a x = X x

omit [DecidableEq R] in
theorem add_self (x : R) : x + x = 0 := by
  calc
    x + x = (1 + 1 : F2) • x := by simp [add_smul]
    _ = 0 := by rw [show (1 + 1 : F2) = 0 by decide, zero_smul]

omit [DecidableEq R] in
theorem add_both (x y t : R) : (x + t) + (y + t) = x + y := by
  calc
    _ = (x + y) + (t + t) := by abel
    _ = _ := by rw [add_self, add_zero]

omit [Module F2 R] in
theorem pivot_translate (a : Fin 3 → R) (t : R) :
    pivot (translate a t) = pivot a + t := by
  classical
  by_cases h1 : a 0 = a 1 <;> by_cases h2 : a 0 = a 2 <;>
    simp [pivot, translate, h1, h2]

theorem normalize_translate (a : Fin 3 → R) (t : R) :
    normalize (translate a t) = normalize a := by
  unfold normalize
  rw [pivot_translate]
  funext i
  exact add_both _ _ _

theorem record_translate (names : Id → Fin 3 → Name) (e : Id) (a : Fin 3 → R) (t : R) :
    record names e (translate a t) = record names e a := by
  classical
  have hs (i : Fin 3) : translate a t i = a i + t := rfl
  simp only [record, hs, add_right_cancel_iff, add_both, normalize_translate]

theorem data_gauge (occ : Fin k → Id) (names : Id → Fin 3 → Name) (rhs : Id → F2)
    (z : R) (a : Fin k → Fin 3 → R) (t : Fin k → R) :
    data occ names rhs (z + ∑ j, rhs (occ j) • t j) (fun j => translate (a j) (t j)) =
      data occ names rhs z a := by
  apply Prod.ext
  · simp only [data, pivot_translate, smul_add, Finset.sum_add_distrib]
    exact add_both _ _ _
  · funext j
    exact record_translate names (occ j) (a j) (t j)

theorem data_global_shift (occ : Fin k → Id) (names : Id → Fin 3 → Name) (rhs : Id → F2)
    (z c : R) (a : Fin k → Fin 3 → R) :
    data occ names rhs (z + c) a =
      ((data occ names rhs z a).1 + c, (data occ names rhs z a).2) := by
  apply Prod.ext
  · dsimp [data]; abel
  · rfl

theorem canonical_shift (occ : Fin k → Id) (names : Id → Fin 3 → Name) (rhs : Id → F2)
    (X : E k →ₗ[F2] R) (c : R) :
    canonical occ names rhs (X + tau.smulRight c) =
      ((canonical occ names rhs X).1 + c, (canonical occ names rhs X).2) := by
  have ht : standardTriple (X + tau.smulRight c) = standardTriple X := by
    funext j i
    fin_cases i <;> simp [standardTriple, tau, firstBasis, secondBasis]
  simp only [canonical, ht]
  have hg : (X + tau.smulRight c : E k →ₗ[F2] R) (hBasis k) = X (hBasis k) + c := by
    simp [hBasis, tau]
  rw [hg]
  exact data_global_shift occ names rhs _ c _

omit [DecidableEq R] in
@[simp] theorem ambientEval_hBasis (b : Fin k → F2) (z : R) (a : Fin k → Fin 3 → R) :
    ambientEval b z a (hBasis k) = z + ∑ j, b j • a j 2 := by
  simp [ambientEval, hBasis]

omit [DecidableEq R] in
@[simp] theorem ambientEval_firstBasis (b : Fin k → F2) (z : R)
    (a : Fin k → Fin 3 → R) (j : Fin k) :
    ambientEval b z a (firstBasis j) = a j 0 + a j 2 := by
  classical
  simp only [ambientEval, firstBasis, zero_smul, zero_add, mul_zero]
  rw [Finset.sum_eq_single j]
  · simp
  · intro i hi hij
    simp [hij]
  · simp

omit [DecidableEq R] in
@[simp] theorem ambientEval_secondBasis (b : Fin k → F2) (z : R)
    (a : Fin k → Fin 3 → R) (j : Fin k) :
    ambientEval b z a (secondBasis j) = a j 1 + a j 2 := by
  classical
  simp only [ambientEval, secondBasis, zero_smul, zero_add, mul_zero]
  rw [Finset.sum_eq_single j]
  · simp
  · intro i hi hij
    simp [hij]
  · simp

omit [DecidableEq R] in

theorem standard_represents (b : Fin k → F2) (X : E k →ₗ[F2] R) :
    Represents b (X (hBasis k)) (standardTriple X) X := by
  intro x
  simpa [ambientEval, standardTriple] using (linearMap_expansion X x).symm

omit [DecidableEq R] in

theorem extension_coefficients (b : Fin k → F2) (z : R) (a : Fin k → Fin 3 → R)
    (X : E k →ₗ[F2] R) (h : Represents b z a X) :
    X (hBasis k) = z + ∑ j, b j • a j 2 ∧
      ∀ j, X (firstBasis j) = a j 0 + a j 2 ∧
        X (secondBasis j) = a j 1 + a j 2 := by
  constructor
  · simpa only [ambientEval_hBasis] using (h (hBasis k)).symm
  · intro j
    exact ⟨by simpa only [ambientEval_firstBasis] using (h (firstBasis j)).symm,
      by simpa only [ambientEval_secondBasis] using (h (secondBasis j)).symm⟩

theorem canonical_eq_of_extension (occ : Fin k → Id) (names : Id → Fin 3 → Name)
    (rhs : Id → F2) (z : R) (a : Fin k → Fin 3 → R) (X : E k →ₗ[F2] R)
    (h : Represents (fun j => rhs (occ j)) z a X) :
    canonical occ names rhs X = data occ names rhs z a := by
  obtain ⟨hz, ha⟩ := extension_coefficients _ z a X h
  have ht : standardTriple X = fun j => translate (a j) (a j 2) := by
    funext j i
    fin_cases i
    · exact (ha j).1
    · exact (ha j).2
    · exact (add_self (a j 2)).symm
  unfold canonical
  rw [hz, ht]
  exact data_gauge occ names rhs z a (fun j => a j 2)

theorem extension_independent (occ : Fin k → Id) (names : Id → Fin 3 → Name)
    (rhs : Id → F2) (z z' : R) (a a' : Fin k → Fin 3 → R) (X : E k →ₗ[F2] R)
    (h : Represents (fun j => rhs (occ j)) z a X)
    (h' : Represents (fun j => rhs (occ j)) z' a' X) :
    data occ names rhs z a = data occ names rhs z' a' :=
  (canonical_eq_of_extension occ names rhs z a X h).symm.trans
    (canonical_eq_of_extension occ names rhs z' a' X h')

def singletonTriple (i : Fin 3) (c : R) : Fin 3 → R := Pi.single i c

omit [Module F2 R] in
theorem pivot_singleton (i : Fin 3) (c : R) : pivot (singletonTriple i c) = 0 := by
  classical
  by_cases hc : c = 0 <;> fin_cases i <;> simp [singletonTriple, pivot, hc]

omit [Module F2 R] in
theorem record_singleton (names : Id → Fin 3 → Name) (e : Id) (i : Fin 3) (c : R) :
    record names e (singletonTriple i c) =
      (if c = 0 then Record.blank else Record.single (names e i) c) := by
  classical
  by_cases hc : c = 0 <;> fin_cases i <;>
    simp [record, singletonTriple, hc, eq_comm]

theorem singleton_global_adjustment (rhs : Id → F2) (e : Id) (i : Fin 3) (c : R) :
    rhs e • pivot (singletonTriple i c) = 0 := by rw [pivot_singleton, smul_zero]

omit [Module F2 R] in

theorem singleton_locality (names : Id → Fin 3 → Name) (e e' : Id)
    (i i' : Fin 3) (c : R) (hname : names e i = names e' i') :
    record names e (singletonTriple i c) = record names e' (singletonTriple i' c) := by
  simp only [record_singleton, hname]

end DFVSGames.Reduction.ActualCanonical

namespace DFVSGames.Soundness.ActualCanonicalPullback

open scoped BigOperators
open PartnerProjection PartnerMapCoordinates
open ConditionalIncidences
open DFVSGames.Integration.BinaryLinear
open DFVSGames.Reduction

noncomputable section

variable {k : Nat} (rhsB : Fin k → Bool) (J : Finset (Fin k))
variable (R : Type) [AddCommGroup R] [Module F2 R]

def selectedFree (b : Fin k → F2) (slot : Fin k → Slot)
    (v : ActualHomogeneous.E k) (j : Fin k) : F2 :=
  match slot j with
  | .first => (v.2 j).1
  | .second => (v.2 j).2
  | .third => b j * v.1 + (v.2 j).1 + (v.2 j).2

def ambientCoefficients (gamma : RawCoefficients J R) (slot : Fin k → Slot)
    (j : Fin k) (i : Fin 3) : R :=
  if hj : j ∈ J then
    if i = ConcreteExtraction.slotIndex (slot j) then gamma (some (.inr ⟨j,hj⟩)) else 0
  else if i = 0 then gamma (some (.inl (⟨j,hj⟩,0)))
    else if i = 1 then gamma (some (.inl (⟨j,hj⟩,1))) else 0

def freePullback (gamma : RawCoefficients J R) (slot : Fin k → Slot) :
    ActualHomogeneous.E k →ₗ[F2] R :=
  (mapEquiv rhsB J R gamma).comp
    ((PartnerLinear.projection rhsB (activeOf J) slot).comp
      (PartnerLinear.sourceLinearEquiv rhsB).symm.toLinearMap)

theorem ofBit_and (a b : Bool) : ofBit (a && b) = ofBit a * ofBit b := by
  cases a <;> cases b <;> decide

theorem inverse_homogeneous (v : ActualHomogeneous.E k) :
    ofBit (((PartnerLinear.sourceLinearEquiv rhsB).symm v).homogeneous) = v.1 :=
  ofBit_toBit _

theorem inverse_first (v : ActualHomogeneous.E k) (j : Fin k) :
    ofBit ((((PartnerLinear.sourceLinearEquiv rhsB).symm v).coordinates j).first) =
      (v.2 j).1 := ofBit_toBit _

theorem inverse_second (v : ActualHomogeneous.E k) (j : Fin k) :
    ofBit ((((PartnerLinear.sourceLinearEquiv rhsB).symm v).coordinates j).second) =
      (v.2 j).2 := ofBit_toBit _

theorem inverse_retained_free (v : ActualHomogeneous.E k) (j : Fin k)
    (slot : Fin k → Slot) :
    ofBit (retained (slot j)
      (((PartnerLinear.sourceLinearEquiv rhsB).symm v).coordinates j)) =
        selectedFree (fun j => ofBit (rhsB j)) slot v j := by
  unfold selectedFree
  cases hslot : slot j with
  | first => exact ofBit_toBit _
  | second => exact ofBit_toBit _
  | third =>
    change ofBit (((rhsB j && toBit v.1).xor (toBit (v.2 j).1)).xor
      (toBit (v.2 j).2)) = ofBit (rhsB j) * v.1 + (v.2 j).1 + (v.2 j).2
    rw [ofBit_xor, ofBit_xor, ofBit_and, ofBit_toBit, ofBit_toBit, ofBit_toBit]

theorem freePullback_expansion (gamma : RawCoefficients J R)
    (slot : Fin k → Slot) (v : ActualHomogeneous.E k) :
    freePullback rhsB J R gamma slot v =
      v.1 • gamma none +
        (∑ j : PositionOutside J, ((v.2 j.val).1 • gamma (some (.inl (j,0))) +
          (v.2 j.val).2 • gamma (some (.inl (j,1))))) +
        ∑ j : PositionInside J, selectedFree (fun j => ofBit (rhsB j)) slot v j.val •
          gamma (some (.inr j)) := by
  change mapEquiv rhsB J R gamma
    (PartnerLinear.projection rhsB (activeOf J) slot
      ((PartnerLinear.sourceLinearEquiv rhsB).symm v)) = _
  rw [pullback_expansion]
  simp only [inverse_homogeneous, inverse_first, inverse_second, inverse_retained_free]

def outsideInsideEquiv : (PositionOutside J ⊕ PositionInside J) ≃ Fin k where
  toFun j := Sum.elim Subtype.val Subtype.val j
  invFun j := if hj : j ∈ J then Sum.inr ⟨j,hj⟩ else Sum.inl ⟨j,hj⟩
  left_inv j := by
    cases j with
    | inl j => simp [j.property]
    | inr j => simp [j.property]
  right_inv j := by
    by_cases hj : j ∈ J <;> simp [hj]

omit [Module F2 R] in
theorem sum_outside_inside (f : PositionOutside J → R) (g : PositionInside J → R) :
    (∑ j, f j) + (∑ j, g j) =
      ∑ j : Fin k, if hj : j ∈ J then g ⟨j,hj⟩ else f ⟨j,hj⟩ := by
  rw [← (outsideInsideEquiv J).sum_comp]
  rw [Fintype.sum_sum_type]
  congr 1 <;> apply Finset.sum_congr rfl
  · intro j _
    simp [outsideInsideEquiv, j.property]
  · intro j _
    simp [outsideInsideEquiv, j.property]

theorem raw_represents (gamma : RawCoefficients J R) (slot : Fin k → Slot) :
    ActualCanonical.Represents (fun j => ofBit (rhsB j)) (gamma none)
      (ambientCoefficients J R gamma slot) (freePullback rhsB J R gamma slot) := by
  intro v
  let f : PositionOutside J → R := fun j =>
    (v.2 j.val).1 • gamma (some (.inl (j,0))) +
      (v.2 j.val).2 • gamma (some (.inl (j,1)))
  let g : PositionInside J → R := fun j =>
    selectedFree (fun j => ofBit (rhsB j)) slot v j.val • gamma (some (.inr j))
  have hs : (∑ j, f j) + (∑ j, g j) =
      ∑ j : Fin k, ((v.2 j).1 • ambientCoefficients J R gamma slot j 0 +
        (v.2 j).2 • ambientCoefficients J R gamma slot j 1 +
        (ofBit (rhsB j) * v.1 + (v.2 j).1 + (v.2 j).2) •
          ambientCoefficients J R gamma slot j 2) := by
    rw [sum_outside_inside]
    apply Finset.sum_congr rfl
    intro j _
    by_cases hj : j ∈ J
    · cases hslot : slot j <;>
        simp [g, ambientCoefficients, selectedFree, hj, hslot, ConcreteExtraction.slotIndex]
    · simp [f, ambientCoefficients, hj]
  calc
    ActualCanonical.ambientEval _ _ _ v = v.1 • gamma none + ((∑ j, f j) + (∑ j, g j)) :=
      congrArg (fun z : R => v.1 • gamma none + z) hs.symm
    _ = (v.1 • gamma none + (∑ j, f j)) + (∑ j, g j) := (add_assoc _ _ _).symm
    _ = freePullback rhsB J R gamma slot v :=
      (freePullback_expansion rhsB J R gamma slot v).symm

theorem canonical_raw_pullback [DecidableEq R] {Id Name : Type} [DecidableEq Id] [DecidableEq Name]
    (occ : Fin k → Id) (names : Id → Fin 3 → Name) (rhs : Id → F2)
    (gamma : RawCoefficients J R) (slot : Fin k → Slot) :
    ActualCanonical.canonical occ names rhs
      (freePullback (fun j => toBit (rhs (occ j))) J R gamma slot) =
    ActualCanonical.data occ names rhs (gamma none) (ambientCoefficients J R gamma slot) := by
  apply ActualCanonical.canonical_eq_of_extension
  simpa only [ofBit_toBit] using raw_represents (fun j => toBit (rhs (occ j))) J R gamma slot

omit [Module F2 R] in
theorem ambientCoefficients_single (gamma : RawCoefficients J R) (slot : Fin k → Slot)
    (j : Fin k) (hj : j ∈ J) :
    ambientCoefficients J R gamma slot j =
      ActualCanonical.singletonTriple (ConcreteExtraction.slotIndex (slot j))
        (gamma (some (.inr ⟨j,hj⟩))) := by
  funext i
  simp [ambientCoefficients, hj, ActualCanonical.singletonTriple, Pi.single_apply]

omit [Module F2 R] in
theorem ambientCoefficients_full_eq (gamma : RawCoefficients J R)
    (slot slot' : Fin k → Slot) (j : Fin k) (hj : j ∉ J) :
    ambientCoefficients J R gamma slot j = ambientCoefficients J R gamma slot' j := by
  funext i
  simp [ambientCoefficients, hj]

theorem raw_data_locality [DecidableEq R] {Id Name : Type}
    (names : Id → Fin 3 → Name) (rhs : Id → F2)
    (occ occ' : Fin k → Id) (slot slot' : Fin k → Slot)
    (gamma : RawCoefficients J R)
    (hfull : ∀ j, j ∉ J → occ j = occ' j)
    (hsingle : ∀ j, j ∈ J → names (occ j) (ConcreteExtraction.slotIndex (slot j)) =
      names (occ' j) (ConcreteExtraction.slotIndex (slot' j))) :
    ActualCanonical.data occ names rhs (gamma none) (ambientCoefficients J R gamma slot) =
      ActualCanonical.data occ' names rhs (gamma none) (ambientCoefficients J R gamma slot') := by
  apply Prod.ext
  · change gamma none + _ = gamma none + _
    congr 1
    apply Finset.sum_congr rfl
    intro j _
    by_cases hj : j ∈ J
    · rw [ambientCoefficients_single J R gamma slot j hj,
        ambientCoefficients_single J R gamma slot' j hj]
      simp only [ActualCanonical.singleton_global_adjustment]
    · rw [hfull j hj, ambientCoefficients_full_eq J R gamma slot slot' j hj]
  · funext j
    change ActualCanonical.record names (occ j) (ambientCoefficients J R gamma slot j) =
      ActualCanonical.record names (occ' j) (ambientCoefficients J R gamma slot' j)
    by_cases hj : j ∈ J
    · rw [ambientCoefficients_single J R gamma slot j hj,
        ambientCoefficients_single J R gamma slot' j hj]
      exact ActualCanonical.singleton_locality names _ _ _ _ _ (hsingle j hj)
    · rw [hfull j hj, ambientCoefficients_full_eq J R gamma slot slot' j hj]

theorem canonical_private_input_locality [DecidableEq R]
    {Id Name : Type} [DecidableEq Id] [DecidableEq Name]
    (names : Id → Fin 3 → Name) (rhs : Id → F2)
    (occ occ' : Fin k → Id) (slot slot' : Fin k → Slot)
    (gamma : RawCoefficients J R)
    (hfull : ∀ j, j ∉ J → occ j = occ' j)
    (hsingle : ∀ j, j ∈ J → names (occ j) (ConcreteExtraction.slotIndex (slot j)) =
      names (occ' j) (ConcreteExtraction.slotIndex (slot' j))) :
    ActualCanonical.canonical occ names rhs
      (freePullback (fun j => toBit (rhs (occ j))) J R gamma slot) =
    ActualCanonical.canonical occ' names rhs
      (freePullback (fun j => toBit (rhs (occ' j))) J R gamma slot') := by
  rw [canonical_raw_pullback, canonical_raw_pullback]
  exact raw_data_locality J R names rhs occ occ' slot slot' gamma hfull hsingle

end
end DFVSGames.Soundness.ActualCanonicalPullback

namespace DFVSGames.Soundness.RawPartnerTarget
open scoped BigOperators
open DFVSGames.Integration.BinaryLinear
open DFVSGames.Reduction
open PartnerProjection PartnerMapCoordinates ConditionalIncidences

noncomputable section
attribute [local instance] Classical.propDecidable

abbrev RawPoint {k : Nat} (J : Finset (Fin k)) := RawSlot J → F2

variable {k : Nat} {R : Type} [AddCommGroup R] [Module F2 R]

def rawProjection (rhsB : Fin k → Bool) (J : Finset (Fin k))
    (slot : Fin k → Slot) : ActualHomogeneous.E k →ₗ[F2] RawPoint J :=
  (pointEquiv rhsB J).toLinearMap.comp
    ((PartnerLinear.projection rhsB (activeOf J) slot).comp
      (PartnerLinear.sourceLinearEquiv rhsB).symm.toLinearMap)

def gammaOfRawMap (J : Finset (Fin k)) (Y : RawPoint J →ₗ[F2] R) :
    RawCoefficients J R := fun s => Y (Pi.single s 1)

theorem rawPoint_decomposition (J : Finset (Fin k)) (v : RawPoint J) :
    (∑ s, v s • Pi.single s (1 : F2)) = v := by
  funext t
  simp [Finset.sum_apply, Pi.single_apply, smul_eq_mul, mul_ite]

theorem rawMap_expansion (J : Finset (Fin k)) (Y : RawPoint J →ₗ[F2] R)
    (v : RawPoint J) : Y v = ∑ s, v s • gammaOfRawMap J Y s := by
  calc
    Y v = Y (∑ s, v s • Pi.single s (1 : F2)) :=
      congrArg Y (rawPoint_decomposition J v).symm
    _ = _ := by simp [gammaOfRawMap]

theorem rawMap_on_partner (rhsB : Fin k → Bool) (J : Finset (Fin k))
    (Y : RawPoint J →ₗ[F2] R) (y : PartnerPoint rhsB (activeOf J)) :
    Y (pointEquiv rhsB J y) = mapEquiv rhsB J R (gammaOfRawMap J Y) y := by
  rw [mapEquiv_apply]
  exact rawMap_expansion J Y (pointEquiv rhsB J y)

theorem rawMap_pullback (rhsB : Fin k → Bool) (J : Finset (Fin k))
    (slot : Fin k → Slot) (Y : RawPoint J →ₗ[F2] R) :
    Y.comp (rawProjection rhsB J slot) =
      ActualCanonicalPullback.freePullback rhsB J R (gammaOfRawMap J Y) slot := by
  apply LinearMap.ext
  intro x
  change Y (pointEquiv rhsB J
      (PartnerLinear.projection rhsB (activeOf J) slot
        ((PartnerLinear.sourceLinearEquiv rhsB).symm x))) =
    mapEquiv rhsB J R (gammaOfRawMap J Y)
      (PartnerLinear.projection rhsB (activeOf J) slot
        ((PartnerLinear.sourceLinearEquiv rhsB).symm x))
  exact rawMap_on_partner rhsB J Y _

end
end DFVSGames.Soundness.RawPartnerTarget

namespace DFVSGames.Soundness.ConditionalIncidences

noncomputable section

instance zeroBits (R : Type) : Zero (ZeroInformation.Bits R) :=
  ⟨ZeroInformation.zero⟩

def membershipBool {P : Type} [DecidableEq P] (J : Finset P) : P → Bool :=
  fun j => decide (j ∈ J)

def fullCoefficient {P R : Type} [DecidableEq P] (J : Finset P)
    (gamma : RawCoefficients J (ZeroInformation.Bits R)) (i : Fin 2) :
    P → ZeroInformation.Bits R :=
  fun j => if hj : j ∉ J then gamma (some (.inl (⟨j, hj⟩, i))) else ZeroInformation.zero

def singleCoefficient {P R : Type} [DecidableEq P] (J : Finset P)
    (gamma : RawCoefficients J (ZeroInformation.Bits R)) : P → ZeroInformation.Bits R :=
  fun j => if hj : j ∈ J then gamma (some (.inr ⟨j, hj⟩)) else ZeroInformation.zero

def fillHidden {P X : Type} [DecidableEq P] (K : Finset P)
    (fallback : P → X) (inside : PositionInside K → X) : P → X :=
  fun j => if hj : j ∈ K then inside ⟨j, hj⟩ else fallback j

theorem singleCoefficient_zero {P R : Type} [DecidableEq P]
    [Fintype R] [DecidableEq R] (J : Finset P)
    (gamma : RawCoefficients J (ZeroInformation.Bits R)) (j : P)
    (hj : j ∈ zeroSet J gamma) : singleCoefficient J gamma j = ZeroInformation.zero := by
  obtain ⟨hjJ, hz⟩ := (mem_zeroSet J gamma j).mp hj
  change gamma (some (.inr ⟨j, hjJ⟩)) = ZeroInformation.zero at hz
  simpa only [singleCoefficient, hjJ, ↓reduceDIte] using hz

theorem zeroSet_subset {P D : Type} [DecidableEq P] [Zero D] [DecidableEq D]
    (J : Finset P) (gamma : RawCoefficients J D) : zeroSet J gamma ⊆ J := by
  intro j hj
  exact ((mem_zeroSet J gamma j).mp hj).choose

variable {P R O N : Type} [Fintype P] [DecidableEq P] [Fintype R] [DecidableEq R]
  (J : Finset P) (name : O → Fin 3 → N)
  (gamma : RawCoefficients J (ZeroInformation.Bits R))
  (observed : PositionOutside (zeroSet J gamma) → O × N)

def actualFirst (sample : Draw P O) : ZeroInformation.FirstInput P R O :=
  ZeroInformation.firstInput Finset.univ.toList (membershipBool J) (gamma none)
    (fullCoefficient J gamma 0) (fullCoefficient J gamma 1) (singleCoefficient J gamma)
    (fun j => (sample j).1) (fun j => (sample j).2)

def actualSecond (sample : Draw P O) : ZeroInformation.SecondInput P R O N :=
  ZeroInformation.secondInput Finset.univ.toList (membershipBool J) (gamma none)
    (fullCoefficient J gamma 0) (fullCoefficient J gamma 1) (singleCoefficient J gamma)
    (fun j => (sample j).1) (fun j => name (sample j).1 (sample j).2)

def localFirstFromH (reference : RawObservationFibre J name gamma observed)
    (insideOccurrences : PositionInside (zeroSet J gamma) → O) :
    ZeroInformation.FirstInput P R O :=
  ZeroInformation.reconstructFirst Finset.univ.toList
    (membershipBool J) (membershipBool (zeroSet J gamma)) (gamma none)
    (fullCoefficient J gamma 0) (fullCoefficient J gamma 1) (singleCoefficient J gamma)
    name
    (fillHidden (zeroSet J gamma) (fun j => (reference.val.2 j).1) insideOccurrences)
    (fun j => (reference.val.2 j).1)
    (fun j => name (reference.val.2 j).1 (reference.val.2 j).2)

def localSecondFromH (reference : RawObservationFibre J name gamma observed)
    (insideNames : PositionInside (zeroSet J gamma) → N) :
    ZeroInformation.SecondInput P R O N :=
  ZeroInformation.reconstructSecond Finset.univ.toList
    (membershipBool J) (membershipBool (zeroSet J gamma)) (gamma none)
    (fullCoefficient J gamma 0) (fullCoefficient J gamma 1) (singleCoefficient J gamma)
    (fun j => (reference.val.2 j).1)
    (fillHidden (zeroSet J gamma)
      (fun j => name (reference.val.2 j).1 (reference.val.2 j).2) insideNames)
    (fun j => name (reference.val.2 j).1 (reference.val.2 j).2)

omit [DecidableEq R] in
theorem localFirstFromH_question_inside
    (reference : RawObservationFibre J name gamma observed)
    (insideOccurrences : PositionInside (zeroSet J gamma) → O)
    (j : PositionInside (zeroSet J gamma)) :
    (localFirstFromH J name gamma observed reference insideOccurrences).question j.val =
      insideOccurrences j := by
  simp [localFirstFromH, ZeroInformation.reconstructFirst, ZeroInformation.firstInput,
    ZeroInformation.reconstructQuestion, fillHidden, membershipBool, j.property]

omit [DecidableEq R] in
theorem localSecondFromH_question_inside
    (reference : RawObservationFibre J name gamma observed)
    (insideNames : PositionInside (zeroSet J gamma) → N)
    (j : PositionInside (zeroSet J gamma)) :
    (localSecondFromH J name gamma observed reference insideNames).question j.val =
      Sum.inr (insideNames j) := by
  have hjJ : j.val ∈ J := zeroSet_subset J gamma j.property
  simp [localSecondFromH, ZeroInformation.reconstructSecond, ZeroInformation.secondInput,
    ZeroInformation.partnerQuestion, ZeroInformation.reconstructQuestion,
    fillHidden, membershipBool, j.property, hjJ]

omit [Fintype P] [DecidableEq R] in
theorem outside_pair_agree (reference sample : RawObservationFibre J name gamma observed)
    (j : P) (hj : j ∉ zeroSet J gamma) :
    incidence name (reference.val.2 j) = incidence name (sample.val.2 j) := by
  exact congrFun (reference.property.2.trans sample.property.2.symm) ⟨j, hj⟩

omit [Fintype P] [DecidableEq R] in
theorem fillHidden_occurrences (reference sample : RawObservationFibre J name gamma observed) :
    fillHidden (zeroSet J gamma) (fun j => (reference.val.2 j).1)
        (fun j => (sample.val.2 j.val).1) =
      (fun j => (sample.val.2 j).1) := by
  funext j
  by_cases hj : j ∈ zeroSet J gamma
  · simp [fillHidden, hj]
  · simp only [fillHidden, hj, ↓reduceDIte]
    exact congrArg (fun p : O × N => p.1)
      (outside_pair_agree J name gamma observed reference sample j hj)

omit [Fintype P] [DecidableEq R] in
theorem fillHidden_names (reference sample : RawObservationFibre J name gamma observed) :
    fillHidden (zeroSet J gamma)
        (fun j => name (reference.val.2 j).1 (reference.val.2 j).2)
        (fun j => name (sample.val.2 j.val).1 (sample.val.2 j.val).2) =
      (fun j => name (sample.val.2 j).1 (sample.val.2 j).2) := by
  funext j
  by_cases hj : j ∈ zeroSet J gamma
  · simp [fillHidden, hj]
  · simp only [fillHidden, hj, ↓reduceDIte]
    exact congrArg Prod.snd (outside_pair_agree J name gamma observed reference sample j hj)

theorem localFirstFromH_correct
    (distinct : ∀ o i i', name o i = name o i' → i = i')
    (reference sample : RawObservationFibre J name gamma observed) :
    localFirstFromH J name gamma observed reference (fun j => (sample.val.2 j.val).1) =
      actualFirst J gamma sample.val.2 := by
  unfold localFirstFromH actualFirst
  rw [fillHidden_occurrences J name gamma observed reference sample]
  apply ZeroInformation.first_input_reconstruction
  · intro j hj
    exact singleCoefficient_zero J gamma j (of_decide_eq_true hj)
  · exact distinct
  · intro j hj
    have hj' : j ∉ zeroSet J gamma := of_decide_eq_false hj
    exact congrArg (fun p : O × N => p.1)
      (outside_pair_agree J name gamma observed reference sample j hj')
  · intro j hj
    have hj' : j ∉ zeroSet J gamma := of_decide_eq_false hj
    exact congrArg Prod.snd (outside_pair_agree J name gamma observed reference sample j hj')

omit [DecidableEq R] in

theorem localSecondFromH_correct (reference sample : RawObservationFibre J name gamma observed) :
    localSecondFromH J name gamma observed reference
        (fun j => name (sample.val.2 j.val).1 (sample.val.2 j.val).2) =
      actualSecond J name gamma sample.val.2 := by
  unfold localSecondFromH actualSecond
  rw [fillHidden_names J name gamma observed reference sample]
  apply ZeroInformation.second_input_reconstruction
  · intro j hj
    exact decide_eq_true (zeroSet_subset J gamma (of_decide_eq_true hj))
  · intro j hj
    have hj' : j ∉ zeroSet J gamma := of_decide_eq_false hj
    exact congrArg (fun p : O × N => p.1)
      (outside_pair_agree J name gamma observed reference sample j hj')
  · intro j hj
    have hj' : j ∉ zeroSet J gamma := of_decide_eq_false hj
    exact congrArg Prod.snd (outside_pair_agree J name gamma observed reference sample j hj')

end

end DFVSGames.Soundness.ConditionalIncidences

namespace DFVSGames.Soundness.BinaryRowTransport
open scoped BigOperators
open DFVSGames.Integration.BinaryLinear
open ConditionalIncidences PartnerMapCoordinates

noncomputable section
attribute [local instance] Classical.propDecidable
variable {Q : Type}

def rowBits (v : Q → F2) : ZeroInformation.Bits Q := fun q => toBit (v q)

theorem rowBits_zero : rowBits (0 : Q → F2) = ZeroInformation.zero := by
  funext q
  change toBit (0 : F2) = false
  decide

theorem rowBits_add (v w : Q → F2) : rowBits (v+w) = ZeroInformation.add (rowBits v) (rowBits w) := by
  funext q
  exact toBit_add _ _

theorem rowBits_smul (b : Bool) (v : Q → F2) :
    rowBits (ofBit b • v) = ZeroInformation.scale (rowBits v) b := by
  cases b <;> funext q <;> simp [rowBits, ZeroInformation.scale, ofBit, toBit]

theorem rowBits_list_sum {P : Type} (xs : List P) (f : P → Q → F2) :
    rowBits (xs.map f |>.sum) = ZeroInformation.rowSum xs (fun j => rowBits (f j)) := by
  induction xs with
  | nil => exact rowBits_zero
  | cons j xs ih =>
    simp only [List.map_cons, List.sum_cons, rowBits_add, ih, ZeroInformation.rowSum, List.foldr_cons]

theorem rowBits_sum {P : Type} [Fintype P] (f : P → Q → F2) :
    rowBits (∑ j, f j) = ZeroInformation.rowSum Finset.univ.toList (fun j => rowBits (f j)) := by
  rw [← Finset.sum_map_toList]
  exact rowBits_list_sum _ _

def rowBitsEquiv : (Q → F2) ≃ ZeroInformation.Bits Q where
  toFun := rowBits
  invFun v := fun q => ofBit (v q)
  left_inv v := by funext q; exact ofBit_toBit _
  right_inv v := by funext q; exact toBit_ofBit _

theorem rowBits_eq_zero (v : Q → F2) : rowBits v = ZeroInformation.zero ↔ v = 0 := by
  rw [← rowBits_zero]
  constructor
  · intro h
    apply (rowBitsEquiv (Q := Q)).injective
    exact h
  · intro h
    rw [h]

def rowCoefficients {P : Type} (J : Finset P) (gamma : RawCoefficients J (Q → F2)) :
    RawCoefficients J (ZeroInformation.Bits Q) := fun slot => rowBits (gamma slot)

theorem zeroSet_rowCoefficients {P : Type} [DecidableEq P] [Fintype Q] [DecidableEq Q]
    (J : Finset P) (gamma : RawCoefficients J (Q → F2)) :
    zeroSet J (rowCoefficients J gamma) = zeroSet J gamma := by
  ext j
  simp only [mem_zeroSet, rowCoefficients]
  apply exists_congr
  intro hj
  change (rowBits (gamma (some (.inr ⟨j,hj⟩))) = ZeroInformation.zero) ↔
    (gamma (some (.inr ⟨j,hj⟩)) = 0)
  exact rowBits_eq_zero _

theorem actual_pullbackRow {k : Nat} [Fintype Q] [DecidableEq Q]
    (rhs : Fin k → Bool) (J : Finset (Fin k))
    (gamma : RawCoefficients J (Q → F2)) (slot : Fin k → PartnerProjection.Slot)
    (x : PartnerProjection.SourcePoint rhs) :
    rowBits (mapEquiv rhs J (Q → F2) gamma
      (PartnerLinear.projection rhs (activeOf J) slot x)) =
    ZeroInformation.pullbackRow Finset.univ.toList (membershipBool J)
      ((rowCoefficients J gamma) none)
      (fullCoefficient J (rowCoefficients J gamma) 0)
      (fullCoefficient J (rowCoefficients J gamma) 1)
      (singleCoefficient J (rowCoefficients J gamma))
      (fun j => ConcreteExtraction.slotIndex (slot j)) x.homogeneous
      (fun j => ConcreteExtraction.tripleCoordinates (x.coordinates j)) := by
  let f : PositionOutside J → Q → F2 := fun j =>
    ofBit (x.coordinates j.val).first • gamma (some (.inl (j,0))) +
      ofBit (x.coordinates j.val).second • gamma (some (.inl (j,1)))
  let g : PositionInside J → Q → F2 := fun j =>
    ofBit (PartnerProjection.retained (slot j.val) (x.coordinates j.val)) • gamma (some (.inr j))
  rw [pullback_expansion]
  change rowBits ((ofBit x.homogeneous • gamma none + ∑ j, f j) + ∑ j, g j) = _
  rw [add_assoc, ActualCanonicalPullback.sum_outside_inside J (Q → F2) f g,
    rowBits_add, rowBits_smul, rowBits_sum]
  unfold ZeroInformation.pullbackRow
  congr 1
  apply ZeroInformation.rowSum_congr
  intro j
  by_cases hj : j ∈ J
  · simp [g, hj, membershipBool, singleCoefficient, rowCoefficients,
      rowBits_smul, ConcreteExtraction.retained_coordinates]
  · simp [f, hj, membershipBool, fullCoefficient, rowCoefficients,
      rowBits_add, rowBits_smul, ConcreteExtraction.tripleCoordinates]

theorem actual_partnerRow {k : Nat} [Fintype Q] [DecidableEq Q]
    (rhs : Fin k → Bool) (J : Finset (Fin k))
    (gamma : RawCoefficients J (Q → F2))
    (y : PartnerProjection.PartnerPoint rhs (activeOf J)) :
    rowBits (mapEquiv rhs J (Q → F2) gamma y) =
    ZeroInformation.partnerRow Finset.univ.toList (membershipBool J)
      ((rowCoefficients J gamma) none)
      (fullCoefficient J (rowCoefficients J gamma) 0)
      (fullCoefficient J (rowCoefficients J gamma) 1)
      (singleCoefficient J (rowCoefficients J gamma)) y.homogeneous
      (fun j => ConcreteExtraction.tripleCoordinates (y.full j)) y.single := by
  let f : PositionOutside J → Q → F2 := fun j =>
    ofBit (y.full j.val).first • gamma (some (.inl (j,0))) +
      ofBit (y.full j.val).second • gamma (some (.inl (j,1)))
  let g : PositionInside J → Q → F2 := fun j =>
    ofBit (y.single j.val) • gamma (some (.inr j))
  rw [mapEquiv_expansion]
  change rowBits ((ofBit y.homogeneous • gamma none + ∑ j, f j) + ∑ j, g j) = _
  rw [add_assoc, ActualCanonicalPullback.sum_outside_inside J (Q → F2) f g,
    rowBits_add, rowBits_smul, rowBits_sum]
  unfold ZeroInformation.partnerRow
  congr 1
  apply ZeroInformation.rowSum_congr
  intro j
  by_cases hj : j ∈ J
  · simp [g, hj, membershipBool, singleCoefficient, rowCoefficients, rowBits_smul]
  · simp [f, hj, membershipBool, fullCoefficient, rowCoefficients,
      rowBits_add, rowBits_smul, ConcreteExtraction.tripleCoordinates]

def rawBitsEquiv {P : Type} (J : Finset P) :
    RawCoefficients J (Q → F2) ≃ RawCoefficients J (ZeroInformation.Bits Q) :=
  Equiv.piCongrRight (fun _ => rowBitsEquiv)

def bitsMapEquiv {P : Type} [Fintype P] [DecidableEq P]
    (rhs : P → Bool) (J : Finset P) :
    RawCoefficients J (ZeroInformation.Bits Q) ≃
      (PartnerProjection.PartnerPoint rhs (activeOf J) →ₗ[F2] (Q → F2)) :=
  (rawBitsEquiv J).symm.trans (mapEquiv rhs J (Q → F2)).toEquiv

theorem uniform_bit_coefficients_maps {P : Type} [Fintype P] [DecidableEq P]
    [Fintype Q] [DecidableEq Q] (rhs : P → Bool) (J : Finset P)
    (H : (PartnerProjection.PartnerPoint rhs (activeOf J) →ₗ[F2] (Q → F2)) → ℝ) :
    (𝔼 gamma : RawCoefficients J (ZeroInformation.Bits Q), H (bitsMapEquiv rhs J gamma)) =
      𝔼 Y, H Y :=
  Fintype.expect_equiv (bitsMapEquiv rhs J) _ H (fun _ => rfl)

end
end DFVSGames.Soundness.BinaryRowTransport

namespace DFVSGames.Soundness.RawMapLaw
open scoped BigOperators
open DFVSGames.Integration.BinaryLinear
open ConditionalIncidences PartnerMapCoordinates RawPartnerTarget BinaryRowTransport

noncomputable section
attribute [local instance] Classical.propDecidable

variable {k : Nat} (J : Finset (Fin k)) (R : Type) [AddCommGroup R] [Module F2 R]

def rawMap (gamma : RawCoefficients J R) : RawPoint J →ₗ[F2] R :=
  (mapEquiv (fun _ : Fin k => false) J R gamma).comp
    (pointEquiv (fun _ : Fin k => false) J).symm.toLinearMap

theorem coefficients_rawMap (gamma : RawCoefficients J R) :
    gammaOfRawMap J (rawMap J R gamma) = gamma := by
  apply (mapEquiv (fun _ : Fin k => false) J R).injective
  apply LinearMap.ext
  intro y
  rw [← rawMap_on_partner]
  change mapEquiv (fun _ : Fin k => false) J R gamma
    ((pointEquiv (fun _ : Fin k => false) J).symm
      (pointEquiv (fun _ : Fin k => false) J y)) = _
  rw [LinearEquiv.symm_apply_apply]

theorem rawMap_coefficients (Y : RawPoint J →ₗ[F2] R) :
    rawMap J R (gammaOfRawMap J Y) = Y := by
  apply LinearMap.ext
  intro v
  have h := rawMap_on_partner (fun _ : Fin k => false) J Y
    ((pointEquiv (fun _ : Fin k => false) J).symm v)
  rw [LinearEquiv.apply_symm_apply] at h
  exact h.symm

def rawMapEquiv : RawCoefficients J R ≃ (RawPoint J →ₗ[F2] R) where
  toFun := rawMap J R
  invFun := gammaOfRawMap J
  left_inv := coefficients_rawMap J R
  right_inv := rawMap_coefficients J R

instance rawMapsFintype [Fintype R] : Fintype (RawPoint J →ₗ[F2] R) := by
  classical
  exact Fintype.ofEquiv (RawCoefficients J R) (rawMapEquiv J R)

def bitsRawMapEquiv {Q : Type} : RawCoefficients J (ZeroInformation.Bits Q) ≃
    (RawPoint J →ₗ[F2] (Q → F2)) :=
  (rawBitsEquiv J).symm.trans (rawMapEquiv J (Q → F2))

theorem bits_coefficients {Q : Type} (gamma : RawCoefficients J (ZeroInformation.Bits Q)) :
    rowCoefficients J (gammaOfRawMap J (bitsRawMapEquiv J gamma)) = gamma := by
  change (rawBitsEquiv J) (gammaOfRawMap J (rawMap J (Q → F2) ((rawBitsEquiv J).symm gamma))) = gamma
  rw [coefficients_rawMap, Equiv.apply_symm_apply]

theorem uniform_bits_rawMaps {Q : Type} [Fintype Q] [DecidableEq Q]
    (H : (RawPoint J →ₗ[F2] (Q → F2)) → ℝ) :
    (𝔼 gamma : RawCoefficients J (ZeroInformation.Bits Q), H (bitsRawMapEquiv J gamma)) =
      𝔼 Y, H Y :=
  Fintype.expect_equiv (bitsRawMapEquiv J) _ H (fun _ => rfl)

end
end DFVSGames.Soundness.RawMapLaw

end OAI
