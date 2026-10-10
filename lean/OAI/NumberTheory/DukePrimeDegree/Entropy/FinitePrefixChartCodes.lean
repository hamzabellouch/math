import OAI.NumberTheory.DukePrimeDegree.Geometry.FiniteTransverseCode

namespace OAI

/-! # Finite codes for a growing prefix of coordinate charts

The label records chart membership as well as the coordinate grid. A
single sufficiently advanced label therefore resolves any fixed chart.
-/

noncomputable section
open Set MeasureTheory
namespace DukePrimeDegree

theorem exists_finite_prefix_chart_codes
    {Y : Type*} [MeasurableSpace Y] {d : ℕ}
    (A : ℕ → Set Y) (hA : ∀ i, MeasurableSet (A i))
    (f : ℕ → Y → Fin d → ℝ) (hf : ∀ i, Measurable (f i))
    (R : ℕ → ℝ) (hR : ∀ i, 0 ≤ R i)
    (hbound : ∀ i x, x ∈ A i → ∀ j, |f i x j| ≤ R i) :
    ∃ (K : ℕ → ℕ) (B : ∀ n, Y → Fin (K n)),
      (∀ n, Measurable (B n)) ∧
      ∀ n i, i ≤ n → ∀ x ∈ A i, ∀ y, B n y=B n x →
        y ∈ A i ∧ ∀ j, |f i y j-f i x j| < 2*(1/(n+1:ℝ)) := by
  classical
  have hscale (n : ℕ) : (0:ℝ) < 1/(n+1) := by positivity
  have hscale1 (n : ℕ) : 1/(n+1:ℝ) ≤ 1 := by
    apply div_le_self zero_le_one
    linarith [Nat.cast_nonneg (α := ℝ) n]
  choose L C hC _hcard hclose using fun n (i : Fin (n+1)) =>
    exists_bounded_vector_code (f i.val) (hf i.val) (hR i.val) (hscale n) (hscale1 n)
  let Alphabet (n : ℕ) := ∀ i : Fin (n+1), Option (Fin (L n i))
  let F (n : ℕ) (x : Y) : Alphabet n := fun i =>
    if x ∈ A i.val then some (C n i x) else none
  let K (n : ℕ) := Fintype.card (Alphabet n)
  let B (n : ℕ) (x : Y) : Fin (K n) := Fintype.equivFin (Alphabet n) (F n x)
  have hBm (n : ℕ) : Measurable (B n) := by
    let : MeasurableSpace (Alphabet n) := ⊤
    apply (measurable_of_finite (Fintype.equivFin (Alphabet n))).comp
    apply measurable_to_countable'
    intro a
    change MeasurableSet {x | F n x=a}
    have he : {x | F n x=a} = ⋂ i : Fin (n+1), {x | F n x i=a i} := by
      ext x
      simp only [mem_ofPred_eq,mem_iInter]
      exact ⟨fun h i => congrFun h i,fun h => funext h⟩
    rw [he]
    apply MeasurableSet.iInter
    intro i
    let : MeasurableSpace (Option (Fin (L n i))) := ⊤
    have hFi : Measurable (fun x => F n x i) :=
      ((measurable_of_finite Option.some).comp (hC n i)).piecewise (hA i.val) measurable_const
    exact hFi (measurableSet_singleton (a i))
  refine ⟨K,B,hBm,?_⟩
  intro n i hin x hx y hxy
  let ii : Fin (n+1) := ⟨i,by omega⟩
  have hF : F n y=F n x := (Fintype.equivFin (Alphabet n)).injective hxy
  have hletter := congrFun hF ii
  have hy : y ∈ A i := by
    by_contra hy
    simp only [F,ii,ite_eq_left hx,ite_eq_right hy,reduceCtorEq] at hletter
  have hcode : C n ii y=C n ii x := by
    simpa only [F,ii,ite_eq_left hx,ite_eq_left hy,Option.some.injEq] using hletter
  exact ⟨hy,hclose n ii x y (hbound i x hx) hcode⟩

end DukePrimeDegree

end

end OAI
