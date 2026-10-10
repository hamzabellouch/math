import Mathlib
import OAI.Probability.SKBarriers.Scalar.ScalarHierarchy

namespace OAI

section

section
noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic

theorem scalarHierarchy_compress (n : ℕ) {r : ℕ} (e : Fin r → Fin n)
    (he : StrictMono e) (m v : Fin n → ℝ)
    (hv : ∀ t, (∀ j, e j ≠ t) → v t = 0) (f : ℝ → ℝ) :
    scalarHierarchy n m v f = scalarHierarchy r (m ∘ e) (v ∘ e) f := by
  induction n generalizing r f with
  | zero =>
    cases r with
    | zero => rfl
    | succ r => exact Fin.elim0 (e 0)
  | succ n ih =>
    cases r with
    | zero =>
      have hlast : v (Fin.last n) = 0 := hv _ (fun j => Fin.elim0 j)
      simp only [scalarHierarchy,hlast,scalarStep_zero]
      exact ih (fun j => Fin.elim0 j) (fun a => Fin.elim0 a)
        (fun i => m i.castSucc) (fun i => v i.castSucc)
        (fun t _ => hv t.castSucc (fun j => Fin.elim0 j)) f
    | succ r =>
      by_cases hlast : e (Fin.last r) = Fin.last n
      · have hlt (i : Fin r) : (e i.castSucc).val < n := by
          have H := he (Fin.castSucc_lt_last i)
          rw [hlast] at H
          exact H
        let e' : Fin r → Fin n := fun i => ⟨(e i.castSucc).val,hlt i⟩
        have hcast (i : Fin r) : (e' i).castSucc = e i.castSucc := Fin.ext rfl
        have he' : StrictMono e' := by
          intro a b hab
          exact he (show a.castSucc < b.castSucc from hab)
        have hv' (t : Fin n) (ht : ∀ j, e' j ≠ t) : v t.castSucc = 0 := by
          apply hv
          intro j
          refine Fin.lastCases ?_ (fun i => ?_) j
          · rw [hlast]
            exact (Fin.castSucc_ne_last t).symm
          · intro h
            exact ht i (Fin.ext (congrArg (fun z : Fin (n+1) => z.val) h))
        rw [scalarHierarchy,scalarHierarchy,← hlast]
        have H := ih e' he' (fun i => m i.castSucc) (fun i => v i.castSucc) hv'
          (scalarStep (m (e (Fin.last r))) (v (e (Fin.last r))) f)
        simpa only [Function.comp_def,hcast] using H
      · have hlt (i : Fin (r+1)) : (e i).val < n := by
          have H := he.monotone (Fin.le_last i)
          have H' : (e (Fin.last r)).val < n := by
            have H'' := (e (Fin.last r)).isLt
            have Hne : (e (Fin.last r)).val ≠ n := by
              intro h
              exact hlast (Fin.ext h)
            omega
          exact lt_of_le_of_lt H H'
        let e' : Fin (r+1) → Fin n := fun i => ⟨(e i).val,hlt i⟩
        have hcast (i : Fin (r+1)) : (e' i).castSucc = e i := Fin.ext rfl
        have he' : StrictMono e' := by
          intro a b hab
          exact he hab
        have hzero : v (Fin.last n) = 0 := by
          apply hv
          intro j h
          have H := hlt j
          rw [h] at H
          exact (lt_irrefl n) H
        have hv' (t : Fin n) (ht : ∀ j, e' j ≠ t) : v t.castSucc = 0 := by
          apply hv
          intro j h
          exact ht j (Fin.ext (congrArg (fun z : Fin (n+1) => z.val) h))
        rw [scalarHierarchy,hzero,scalarStep_zero]
        have H := ih e' he' (fun i => m i.castSucc) (fun i => v i.castSucc) hv' f
        simpa only [Function.comp_def,hcast] using H
end SK.Analytic

end
end

end

end OAI
