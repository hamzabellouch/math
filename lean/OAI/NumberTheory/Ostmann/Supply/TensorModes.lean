import OAI.NumberTheory.Ostmann.Supply.CenteredPrimitiveEnergy
import OAI.NumberTheory.Ostmann.Supply.TensorOperators

namespace OAI

noncomputable section
namespace Ostmann.Supply.TensorModes
open TensorOperators
open Finset
open scoped TensorProduct BigOperators

def augmentedSpace (E : FiniteHilbertSpace) : FiniteHilbertSpace :=
  FiniteHilbertSpace.of (WithLp 2 (ℂ × E))

def scalarPart (E : FiniteHilbertSpace) : augmentedSpace E →L[ℂ] augmentedSpace E :=
  (WithLp.prodContinuousLinearEquiv 2 ℂ ℂ E).symm.toContinuousLinearMap.comp
    ((WithLp.fstL 2 ℂ ℂ E).prod 0)

def centeredPart (E : FiniteHilbertSpace) : augmentedSpace E →L[ℂ] augmentedSpace E :=
  1 - scalarPart E

@[simp] theorem scalarPart_apply (E : FiniteHilbertSpace) (x : augmentedSpace E) :
    scalarPart E x = WithLp.toLp 2 (x.fst, (0 : E)) := rfl

@[simp] theorem centeredPart_apply (E : FiniteHilbertSpace) (x : augmentedSpace E) :
    centeredPart E x = WithLp.toLp 2 ((0 : ℂ), x.snd) := by
  apply WithLp.ofLp_injective 2
  change (x.fst - x.fst, x.snd - (0 : E)) = ((0 : ℂ), x.snd)
  simp

@[simp] theorem scalarPart_star (E : FiniteHilbertSpace) : IsStarProjection (scalarPart E) := by
  constructor
  · change scalarPart E * scalarPart E = scalarPart E
    ext x
    rfl
  · apply ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr
    intro x y
    change inner ℂ x.fst y.fst + inner ℂ (0 : E) y.snd =
      inner ℂ x.fst y.fst + inner ℂ x.snd (0 : E)
    simp

@[simp] theorem centeredPart_star (E : FiniteHilbertSpace) : IsStarProjection (centeredPart E) :=
  (scalarPart_star E).one_sub

@[simp] theorem scalar_centered_mul (E : FiniteHilbertSpace) :
    scalarPart E * centeredPart E = 0 := (scalarPart_star E).mul_one_sub_self

@[simp] theorem centered_scalar_mul (E : FiniteHilbertSpace) :
    centeredPart E * scalarPart E = 0 := (scalarPart_star E).one_sub_mul_self

@[simp] theorem scalar_add_centered (E : FiniteHilbertSpace) :
    scalarPart E + centeredPart E = 1 := by simp [centeredPart]

theorem tensorOp_congr {E F : ℕ → FiniteHilbertSpace} (n : ℕ)
    (f g : ∀ i, E i →L[ℂ] F i) (h : ∀ i < n, f i = g i) :
    tensorOp f n = tensorOp g n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change TensorProduct.mapL (tensorOp f n) (f n) = TensorProduct.mapL (tensorOp g n) (g n)
    rw [ih (fun i hi => h i (by omega)), h n (by omega)]

theorem tensorOp_mul {E : ℕ → FiniteHilbertSpace}
    (f g : ∀ i, E i →L[ℂ] E i) (n : ℕ) :
    tensorOp (fun i => f i * g i) n = tensorOp f n * tensorOp g n := by
  induction n with
  | zero => change (1 : ℂ →L[ℂ] ℂ) = 1 * 1; simp
  | succ n ih =>
    change TensorProduct.mapL (tensorOp (fun i => f i * g i) n) (f n * g n) = _
    rw [ih, TensorProduct.mapL_mul]
    rfl

@[simp] theorem tensorOp_one (E : ℕ → FiniteHilbertSpace) (n : ℕ) :
    tensorOp (fun i => (1 : E i →L[ℂ] E i)) n = 1 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change TensorProduct.mapL (tensorOp (fun i => (1 : E i →L[ℂ] E i)) n) 1 = 1
    rw [ih]
    exact TensorProduct.mapL_id_id

theorem tensorOp_adjoint {E : ℕ → FiniteHilbertSpace}
    (f : ∀ i, E i →L[ℂ] E i) (n : ℕ) :
    (tensorOp f n).adjoint = tensorOp (fun i => (f i).adjoint) n := by
  induction n with
  | zero => exact ContinuousLinearMap.adjoint_id
  | succ n ih =>
    change (TensorProduct.mapL (tensorOp f n) (f n)).adjoint = _
    rw [TensorProduct.adjoint_mapL, ih]
    rfl

theorem tensorOp_zero_of_factor {E F : ℕ → FiniteHilbertSpace}
    (f : ∀ i, E i →L[ℂ] F i) (n : ℕ) (h : ∃ i < n, f i = 0) : tensorOp f n = 0 := by
  induction n with
  | zero => obtain ⟨i, hi, hzero⟩ := h; omega
  | succ n ih =>
    obtain ⟨i, hi, hz⟩ := h
    change TensorProduct.mapL (tensorOp f n) (f n) = 0
    by_cases hin : i = n
    · subst i
      rw [hz, TensorProduct.mapL_zero_right]
    · rw [ih ⟨i, by omega, hz⟩, TensorProduct.mapL_zero_left]

def exactMode (E : ℕ → FiniteHilbertSpace) (n : ℕ) (s : Finset ℕ) :
    tensorSpace (fun i => augmentedSpace (E i)) n →L[ℂ]
      tensorSpace (fun i => augmentedSpace (E i)) n :=
  tensorOp (fun i => if i ∈ s then centeredPart (E i) else scalarPart (E i)) n

theorem exactMode_star (E : ℕ → FiniteHilbertSpace) (n : ℕ) (s : Finset ℕ) :
    IsStarProjection (exactMode E n s) := by
  have hloc (i : ℕ) : IsStarProjection (if i ∈ s then centeredPart (E i) else scalarPart (E i)) := by
    split_ifs <;> simp
  constructor
  · change exactMode E n s * exactMode E n s = exactMode E n s
    rw [exactMode, ← tensorOp_mul]
    apply tensorOp_congr
    intro i hi
    exact (hloc i).isIdempotentElem
  · change (exactMode E n s).adjoint = exactMode E n s
    rw [exactMode, tensorOp_adjoint]
    apply tensorOp_congr
    intro i hi
    exact (hloc i).isSelfAdjoint.adjoint_eq

theorem exactMode_mul_eq_zero (E : ℕ → FiniteHilbertSpace) (n : ℕ)
    {s t : Finset ℕ} (hs : s ⊆ range n) (ht : t ⊆ range n) (hst : s ≠ t) :
    exactMode E n s * exactMode E n t = 0 := by
  rw [exactMode, exactMode, ← tensorOp_mul]
  apply tensorOp_zero_of_factor
  have hdiff : ∃ i, ¬(i ∈ s ↔ i ∈ t) := by
    exact not_forall.mp (fun h => hst (Finset.ext h))
  obtain ⟨i, hi⟩ := hdiff
  by_cases his : i ∈ s
  · have hit : i ∉ t := fun hit => hi ⟨fun _ => hit, fun _ => his⟩
    exact ⟨i, mem_range.mp (hs his), by simp [his, hit]⟩
  · have hit : i ∈ t := by tauto
    exact ⟨i, mem_range.mp (ht hit), by simp [his, hit]⟩

def retainedModes (n K : ℕ) : Finset (Finset ℕ) :=
  (range n).powerset.filter (fun s => s.card ≤ K)

def lowModes (E : ℕ → FiniteHilbertSpace) (n K : ℕ) :
    tensorSpace (fun i => augmentedSpace (E i)) n →L[ℂ]
      tensorSpace (fun i => augmentedSpace (E i)) n :=
  ∑ s ∈ retainedModes n K, exactMode E n s

theorem sum_exactMode_star (E : ℕ → FiniteHilbertSpace) (n : ℕ) (M : Finset (Finset ℕ))
    (hM : ∀ s ∈ M, s ⊆ range n) : IsStarProjection (∑ s ∈ M, exactMode E n s) := by
  induction M using Finset.induction_on with
  | empty => simp
  | @insert s M hs ih =>
    rw [sum_insert hs]
    apply (exactMode_star E n s).add (ih (fun t ht => hM t (mem_insert_of_mem ht)))
    rw [mul_sum]
    apply sum_eq_zero
    intro t ht
    exact exactMode_mul_eq_zero E n (hM s (mem_insert_self _ _))
      (hM t (mem_insert_of_mem ht)) (by intro h; subst t; exact hs ht)

theorem lowModes_star (E : ℕ → FiniteHilbertSpace) (n K : ℕ) :
    IsStarProjection (lowModes E n K) :=
  sum_exactMode_star E n _ (fun _ hs => mem_powerset.mp (mem_filter.mp hs).1)

end Ostmann.Supply.TensorModes

end

end OAI
