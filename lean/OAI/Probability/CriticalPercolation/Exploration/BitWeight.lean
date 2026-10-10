import Mathlib
import OAI.Probability.CriticalPercolation.ProductMeasure.Delta
import OAI.Probability.CriticalPercolation.Exploration.QueryTree
import OAI.Probability.CriticalPercolation.Modular.PushMass

namespace OAI

section
section
open Set MeasureTheory ProbabilityTheory
open scoped Classical
open Real
open Set Real
open scoped Topology
open scoped BigOperators
open Set

namespace CriticalPercolation.QueryTree
open FiniteProduct FiniteEntropy

variable {E : Type*} [Fintype E]

noncomputable def bitWeight (p : ℝ) (_ : E) (b : Bool) : ℝ := if b then p else 1-p

omit [Fintype E] in
lemma bitWeight_sum (p : ℝ) (e : E) : ∑ b, bitWeight p e b = 1 := by
  simp [bitWeight]

omit [Fintype E] in
lemma bitWeight_nonneg {p : ℝ} (hp : p ∈ Set.Icc 0 1) (e : E) (b : Bool) :
    0 ≤ bitWeight p e b := by cases b <;> simp [bitWeight, hp.1, hp.2]

lemma expect_indicator (p : ℝ) {Y : Type*} (f : (E → Bool) → Y) (y : Y) :
    expect (bitWeight p) (fun ω => if f ω = y then 1 else 0) =
      pushMass f (density (bitWeight p)) y := by
  classical
  simp only [expect, pushMass, mul_ite, mul_one, mul_zero]

lemma reference_eq_product_push (p : ℝ) (t : QueryTree E)
    (used : Finset E) (hv : t.Valid used) :
    pushMass t.run (density (bitWeight p)) = t.reference p := by
  classical
  induction t generalizing used with
  | stop =>
    funext x
    have : x = PUnit.unit := Subsingleton.elim _ _
    subst x
    simp only [pushMass, run, reference]
    exact sum_density _ (bitWeight_sum p)
  | ask e left right hl hr =>
    have hi (b : Bool) : DependsOn (fun ω : E → Bool => if ω e = b then (1:ℝ) else 0)
        ({e} : Set E) := by
      intro ω ω' hω
      dsimp only
      rw [hω e (Set.mem_singleton e)]
    have hc (u : QueryTree E) (hu : u.Valid (insert e used)) (x : u.Leaf) :
        DependsOn (fun ω => if u.run ω = x then (1:ℝ) else 0) ({e} : Set E)ᶜ := by
      intro ω ω' hω
      have heq : u.run ω = u.run ω' := run_dependsOn u _ hu (fun j hj =>
        hω j (by intro hje; have hje : j = e := hje; subst j
                 exact hj (Finset.mem_insert_self _ _)))
      dsimp only
      rw [heq]
    funext x
    cases x with
    | inl x =>
      have heq : (fun ω => if (ask e left right).run ω = Sum.inl x then (1:ℝ) else 0) =
          (fun ω => (if ω e = false then (1:ℝ) else 0) *
            (if left.run ω = x then 1 else 0)) := by
        funext ω
        cases he : ω e <;> simp [run, he]
      have hm : pushMass (ask e left right).run (density (bitWeight p)) (Sum.inl x) =
          expect (bitWeight p) (fun ω => if (ask e left right).run ω = Sum.inl x then 1 else 0) := by
        simp only [pushMass, expect, mul_ite, mul_one, mul_zero]
        apply Finset.sum_congr rfl
        intro ω _
        split_ifs <;> simp_all
      rw [hm, heq, expect_indep _ (bitWeight_sum p) _ (hi false)
        (hc left hv.2.1 x)]
      have hev : expect (bitWeight p) (fun ω => if ω e = false then 1 else 0) =
          bitWeight p e false := by
        convert expect_eval_indicator (bitWeight p) (bitWeight_sum p) e false using 1
        congr 1
        funext ω
        split_ifs <;> simp_all
      rw [hev]
      have hm' : expect (bitWeight p) (fun ω => if left.run ω = x then 1 else 0) =
          pushMass left.run (density (bitWeight p)) x := by
        simp only [pushMass, expect, mul_ite, mul_one, mul_zero]
      rw [hm', hl _ hv.2.1]
      rfl
    | inr x =>
      have heq : (fun ω => if (ask e left right).run ω = Sum.inr x then (1:ℝ) else 0) =
          (fun ω => (if ω e = true then (1:ℝ) else 0) *
            (if right.run ω = x then 1 else 0)) := by
        funext ω
        cases he : ω e <;> simp [run, he]
      have hm : pushMass (ask e left right).run (density (bitWeight p)) (Sum.inr x) =
          expect (bitWeight p) (fun ω => if (ask e left right).run ω = Sum.inr x then 1 else 0) := by
        simp only [pushMass, expect, mul_ite, mul_one, mul_zero]
        apply Finset.sum_congr rfl
        intro ω _
        split_ifs <;> simp_all
      rw [hm, heq, expect_indep _ (bitWeight_sum p) _ (hi true)
        (hc right hv.2.2 x)]
      have hev : expect (bitWeight p) (fun ω => if ω e = true then 1 else 0) =
          bitWeight p e true := by
        convert expect_eval_indicator (bitWeight p) (bitWeight_sum p) e true using 1
        congr 1
        funext ω
        split_ifs <;> simp_all
      rw [hev]
      have hm' : expect (bitWeight p) (fun ω => if right.run ω = x then 1 else 0) =
          pushMass right.run (density (bitWeight p)) x := by
        simp only [pushMass, expect, mul_ite, mul_one, mul_zero]
      rw [hm', hr _ hv.2.2]
      rfl

end CriticalPercolation.QueryTree

end
end

end OAI
