import OAI.NumberTheory.TwoPoint.Bounds.FiniteProbability
import OAI.NumberTheory.TwoPoint.Bounds.LinearPivots
import Mathlib.Logic.Equiv.Prod

namespace OAI

/-! Product sampling and the atom bound for independent linear equations. -/

namespace TwoPointCorrelations

open Finset

variable {ι A : Type*} [Fintype ι] [DecidableEq ι]

def joinCoordinates (S : Finset ι) (x : S → A) (y : {i // i ∉ S} → A) : ι → A :=
  fun i => if h : i ∈ S then x ⟨i, h⟩ else y ⟨i, h⟩

omit [Fintype ι] in
@[simp] lemma joinCoordinates_mem (S : Finset ι) (x : S → A) (y : {i // i ∉ S} → A)
    (i : S) : joinCoordinates S x y i = x i := by simp [joinCoordinates, i.property]

omit [Fintype ι] in
@[simp] lemma joinCoordinates_notMem (S : Finset ι) (x : S → A) (y : {i // i ∉ S} → A)
    (i : {i // i ∉ S}) : joinCoordinates S x y i = y i := by simp [joinCoordinates, i.property]

namespace FiniteLaw

variable [Fintype A]

lemma independent_probability_all (μ : ι → FiniteLaw A) (E : ι → A → Prop) :
    (independent μ).probability (fun x => ∀ i, E i (x i)) =
      ∏ i, (μ i).probability (E i) := by
  classical
  unfold probability
  calc
    _ = (independent μ).average (fun x => ∏ i, if E i (x i) then (1 : ℝ) else 0) := by
      apply congrArg (independent μ).average
      funext x
      by_cases hx : ∀ i, E i (x i) <;> simp [Fintype.prod_boole, hx]
    _ = _ := independent_average_product μ (fun i x => if E i x then 1 else 0)

lemma independent_weight_join (μ : ι → FiniteLaw A) (S : Finset ι)
    (x : S → A) (y : {i // i ∉ S} → A) :
    (independent μ).weight (joinCoordinates S x y) =
      (independent (fun i : S => μ i)).weight x *
      (independent (fun i : {i // i ∉ S} => μ i)).weight y := by
  change (∏ i, (μ i).weight (joinCoordinates S x y i)) = _
  rw [← Fintype.prod_subtype_mul_prod_subtype (fun i => i ∈ S)]
  simp only [joinCoordinates_mem, joinCoordinates_notMem, independent]
  have hinst : Subtype.fintype (fun i : ι => i ∈ S) = (inferInstance : Fintype S) :=
    Subsingleton.elim _ _
  rw [hinst]

/-- Conditioning on coordinates outside `S` leaves the original product
law on `S`. -/
lemma independent_average_split (μ : ι → FiniteLaw A) (S : Finset ι) (f : (ι → A) → ℝ) :
    (independent μ).average f =
      (independent (fun i : {i // i ∉ S} => μ i)).average (fun y =>
        (independent (fun i : S => μ i)).average (fun x => f (joinCoordinates S x y))) := by
  let e := Equiv.piEquivPiSubtypeProd (fun i => i ∈ S) (fun _ => A)
  calc
    _ = ∑ z : (S → A) × ({i // i ∉ S} → A),
        (independent μ).weight (joinCoordinates S z.1 z.2) *
          f (joinCoordinates S z.1 z.2) := by
      exact (e.symm.sum_comp (fun z => (independent μ).weight z * f z)).symm
    _ = _ := by
      rw [Fintype.sum_prod_type]
      simp only [independent_weight_join, average, mul_sum]
      rw [sum_comm]
      apply sum_congr rfl
      intro y _
      apply sum_congr rfl
      intro x _
      ring

/-- An event that determines the coordinates in `S`, after all other
coordinates are fixed, has probability at most `α ^ #S`. -/
theorem probability_le_of_determined_coordinates (μ : ι → FiniteLaw A)
    (S : Finset ι) (α : ℝ) (hα : 0 ≤ α) (hatom : ∀ i x, (μ i).weight x ≤ α)
    (E : (ι → A) → Prop)
    (hunique : ∀ x y, E x → E y → (∀ i ∉ S, x i = y i) → x = y) :
    (independent μ).probability E ≤ α ^ S.card := by
  classical
  rw [probability, independent_average_split μ S]
  apply (average_mono _ (g := fun _ => α ^ S.card) ?_).trans_eq (average_const _ _)
  intro y
  apply probability_le_atom_bound
  · exact pow_nonneg hα _
  · intro x
    change (∏ i : S, (μ i).weight (x i)) ≤ _
    simpa only [prod_const, card_univ, Fintype.card_coe] using
      prod_le_prod₀ (s := univ) (fun (i : S) _ => (μ i.val).nonneg (x i))
        (fun (i : S) _ => hatom i.val (x i))
  · intro x x' hx hx'
    have hj := hunique (joinCoordinates S x y) (joinCoordinates S x' y) hx hx'
      (fun i hi => by simp [joinCoordinates, hi])
    funext i
    simpa only [joinCoordinates_mem] using congrFun hj i

/-- Independent bounded atoms satisfy the expected codimension bound for
every surjective real linear system. -/
theorem probability_linear_equations {K κ : Type*} [Field K] [Fintype κ]
    (μ : ι → FiniteLaw A) (val : A → K) (hval : Function.Injective val)
    (T : (ι → K) →ₗ[K] (κ → K)) (hT : Function.Surjective T)
    (b : κ → K) (α : ℝ) (hα : 0 ≤ α) (hatom : ∀ i x, (μ i).weight x ≤ α) :
    (independent μ).probability (fun x => T (fun i => val (x i)) = b) ≤
      α ^ Fintype.card κ := by
  obtain ⟨S, hcard, hpivot⟩ := exists_pivot_coordinates T hT
  rw [← hcard]
  apply probability_le_of_determined_coordinates μ S α hα hatom
  intro x y hx hy hxy
  have heq := hpivot (fun i => val (x i)) (fun i => val (y i))
    (fun i hi => congrArg val (hxy i hi)) (hx.trans hy.symm)
  funext i
  exact hval (congrFun heq i)

end FiniteLaw

end TwoPointCorrelations

end OAI
