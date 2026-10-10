import OAI.Probability.SignedSweeps.BinaryNetworks

namespace OAI

noncomputable section
namespace SignedSweeps
open scoped BigOperators TensorProduct
open Module
open scoped BigOperators
attribute [local instance] Classical.propDecidable

def sweepPrefix (d : ℕ) (a : SweepSettings d) (t : ℕ) : SymmetricGroup (2 ^ d) :=
  (((List.ofFn fun i => (a i).1).take t).reverse).prod

@[simp] lemma sweepPrefix_zero (d : ℕ) (a : SweepSettings d) : sweepPrefix d a 0 = 1 := by
  simp [sweepPrefix]

@[simp] lemma sweepPrefix_full (d : ℕ) (a : SweepSettings d) :
    sweepPrefix d a d = sampleSweep d a := by
  unfold sweepPrefix sampleSweep
  rw [List.take_of_length_le (by simp)]

lemma sweepPrefix_succ (d : ℕ) (a : SweepSettings d) (t : ℕ) (ht : t < d) :
    sweepPrefix d a (t+1) = (a ⟨t,ht⟩).1 * sweepPrefix d a t := by
  unfold sweepPrefix
  rw [List.take_succ_eq_append_getElem (by simpa using ht), List.reverse_append, List.prod_append]
  simp

lemma coordinateSubgroup_bit {d : ℕ} {i : Fin d} (g : coordinateSubgroup d i)
    (x : Fin (2 ^ d)) (j : Fin d) (hji : j ≠ i) :
    (positionsEquiv d).symm (g.1 x) j = (positionsEquiv d).symm x j :=
  congrFun (g.property x) ⟨j,hji⟩

lemma sweepPrefix_before (d : ℕ) (a : SweepSettings d) (x : Fin (2 ^ d)) (t : ℕ)
    (ht : t ≤ d) (j : Fin d) (hjt : t ≤ j.1) :
    (positionsEquiv d).symm (sweepPrefix d a t x) j = (positionsEquiv d).symm x j := by
  induction t with
  | zero => simp
  | succ t ih =>
    rw [sweepPrefix_succ d a t (by omega), Equiv.Perm.mul_apply,
      coordinateSubgroup_bit _ _ j (by intro h; have hv := congrArg Fin.val h; simp at hv; omega)]
    exact ih (by omega) (by omega)

lemma sweepPrefix_after (d : ℕ) (a : SweepSettings d) (x : Fin (2 ^ d))
    (s t : ℕ) (hts : t ≤ s) (hs : s ≤ d) (j : Fin d) (hjt : j.1 < t) :
    (positionsEquiv d).symm (sweepPrefix d a s x) j =
      (positionsEquiv d).symm (sweepPrefix d a t x) j := by
  induction s with
  | zero => omega
  | succ s ih =>
    by_cases he : t = s+1
    · simp only [he]
    rw [sweepPrefix_succ d a s (by omega), Equiv.Perm.mul_apply,
      coordinateSubgroup_bit _ _ j (by intro h; have hv := congrArg Fin.val h; simp at hv; omega)]
    exact ih (by omega) (by omega)

def endpointPath (d t : ℕ) (x y : Fin (2 ^ d)) : Fin (2 ^ d) :=
  positionsEquiv d (fun j => if j.1 < t then (positionsEquiv d).symm y j else (positionsEquiv d).symm x j)

@[simp] lemma endpointPath_zero (d : ℕ) (x y : Fin (2 ^ d)) : endpointPath d 0 x y = x := by
  simp [endpointPath]

@[simp] lemma endpointPath_full (d : ℕ) (x y : Fin (2 ^ d)) : endpointPath d d x y = y := by
  simp [endpointPath, Fin.is_lt]

@[simp] lemma endpointPath_bit (d t : ℕ) (x y : Fin (2 ^ d)) (j : Fin d) :
    (positionsEquiv d).symm (endpointPath d t x y) j =
      if j.1 < t then (positionsEquiv d).symm y j else (positionsEquiv d).symm x j := by
  simp [endpointPath]

lemma sweepPrefix_eq_endpointPath (d : ℕ) (a : SweepSettings d) (x : Fin (2 ^ d))
    (t : ℕ) (ht : t ≤ d) :
    sweepPrefix d a t x = endpointPath d t x (sampleSweep d a x) := by
  apply (positionsEquiv d).symm.injective
  funext j
  rw [endpointPath_bit]
  split_ifs with hj
  · rw [← sweepPrefix_full]
    exact (sweepPrefix_after d a x d t ht le_rfl j hj).symm
  · exact sweepPrefix_before d a x t ht j (by omega)

def pathAddress (d : ℕ) (i : Fin d) (x y : Fin (2 ^ d)) : SwitchAddress d i :=
  fun j => (positionsEquiv d).symm (endpointPath d i.1 x y) j.1

lemma layerSettings_endpointPath (d : ℕ) (i : Fin d) (p : LayerSettings d i)
    (x y : Fin (2 ^ d))
    (h : p (pathAddress d i x y) ((positionsEquiv d).symm x i) = (positionsEquiv d).symm y i) :
    (layerSettingsEquiv d i p).1 (endpointPath d i.1 x y) = endpointPath d (i.1+1) x y := by
  apply (positionsEquiv d).symm.injective
  funext j
  by_cases hji : j = i
  · subst j
    rw [layerSettings_bit, endpointPath_bit, endpointPath_bit]
    simp only [lt_self_iff_false, ↓reduceIte, Nat.lt_add_one]
    change p (pathAddress d i x y) ((positionsEquiv d).symm x i) =
      (positionsEquiv d).symm y i
    exact h
  · rw [layerSettings_key d i p _ j hji, endpointPath_bit, endpointPath_bit]
    have hv : j.1 ≠ i.1 := fun he => hji (Fin.ext he)
    by_cases hj : j.1 < i.1 <;> simp only [ite_eq_left, hj, show (j.1 < i.1+1) ↔ (j.1 < i.1) by omega]

lemma sampleSweep_endpoints_iff (d : ℕ) (p : PhysicalSettings d) (x y : Fin (2 ^ d)) :
    sampleSweep d (physicalSettingsEquiv d p) x = y ↔
      ∀ i : Fin d, p i (pathAddress d i x y) ((positionsEquiv d).symm x i) =
        (positionsEquiv d).symm y i := by
  constructor
  · intro h i
    have hpath := sweepPrefix_eq_endpointPath d (physicalSettingsEquiv d p) x i.1 (Nat.le_of_lt i.2)
    rw [h] at hpath
    have hnext := sweepPrefix_eq_endpointPath d (physicalSettingsEquiv d p) x (i.1+1) i.2
    rw [h, sweepPrefix_succ d (physicalSettingsEquiv d p) i.1 i.2, Equiv.Perm.mul_apply, hpath] at hnext
    have hi := congrArg (fun z => (positionsEquiv d).symm z i) hnext
    change (positionsEquiv d).symm ((layerSettingsEquiv d i (p i)).1 (endpointPath d i.1 x y)) i = _ at hi
    rw [layerSettings_bit, endpointPath_bit, endpointPath_bit] at hi
    simp only [lt_self_iff_false, ↓reduceIte, Nat.lt_add_one] at hi
    change p i (pathAddress d i x y) ((positionsEquiv d).symm x i) =
      (positionsEquiv d).symm y i at hi
    exact hi
  · intro h
    have hp : ∀ t, t ≤ d → sweepPrefix d (physicalSettingsEquiv d p) t x = endpointPath d t x y := by
      intro t
      induction t with
      | zero => simp
      | succ t ih =>
        intro ht
        rw [sweepPrefix_succ d (physicalSettingsEquiv d p) t (by omega), Equiv.Perm.mul_apply,
          ih (by omega)]
        exact layerSettings_endpointPath d ⟨t,by omega⟩ (p _) x y (h _)
    simpa using hp d le_rfl

def endpointEncounter {I : Type*} (d : ℕ) (x y : I → Fin (2 ^ d)) : SimpleGraph I where
  Adj a b := a ≠ b ∧ ∃ i : Fin d, pathAddress d i (x a) (y a) = pathAddress d i (x b) (y b)
  symm := ⟨by rintro a b ⟨hab,i,hi⟩; exact ⟨hab.symm,i,hi.symm⟩⟩
  loopless := ⟨by rintro a ⟨ha,_⟩; exact ha rfl⟩

end SignedSweeps
end

end OAI
