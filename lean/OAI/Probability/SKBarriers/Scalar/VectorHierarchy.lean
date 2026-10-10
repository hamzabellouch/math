import Mathlib
import OAI.Probability.SKBarriers.Gaussian.GaussianStepAlgebra

namespace OAI

section

noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic
attribute [local instance 2000] parameterNormedGroup parameterNormedSpace
section Vector
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

def vectorStep (m : ℝ) (v : E) (f : E → ℝ) : E → ℝ :=
  gaussianStep m (fun z : E × ℝ => f (z.1+z.2 • v))

def vectorHierarchy : (n : ℕ) → (Fin n → ℝ) → (Fin n → E) → (E → ℝ) → E → ℝ
  | 0,_,_,f => f
  | n+1,m,v,f => vectorHierarchy n (fun i => m i.castSucc) (fun i => v i.castSucc)
      (vectorStep (m (Fin.last n)) (v (Fin.last n)) f)

@[simp] theorem vectorStep_zero (m : ℝ) (f : E → ℝ) : vectorStep m 0 f=f := by
  simp only [vectorStep,smul_zero,add_zero]
  exact gaussianStep_prefix f m

theorem hierarchyPressure_vector_linear (n : ℕ) (m : Fin n → ℝ) (v : Fin n → E)
    (f : E → ℝ) (c : ℝ → E) :
    hierarchyPressure n m (fun z => f (c (parameter n z)+∑ j, coordinateProjection n j z • v j))=
      fun x => vectorHierarchy n m v f (c x) := by
  induction n generalizing f with
  | zero => simp [hierarchyPressure,vectorHierarchy,parameter]
  | succ n ih =>
    have he : (fun z : ParameterSpace (n+1) =>
        f (c (parameter (n+1) z)+∑ j, coordinateProjection (n+1) j z • v j))=
        fun z => f ((c (parameter n z.1)+∑ j : Fin n, coordinateProjection n j z.1 • v j.castSucc)+
          z.2 • v (Fin.last n)) := by
      funext z
      rw [Fin.sum_univ_castSucc]
      simp [coordinateProjection,parameter,add_assoc]
    rw [he,hierarchyPressure]
    change hierarchyPressure n (fun j => m j.castSucc)
      (fun z => vectorStep (m (Fin.last n)) (v (Fin.last n)) f
        (c (parameter n z)+∑ j, coordinateProjection n j z • v j.castSucc))=_
    rw [ih]
    rfl

theorem vectorHierarchy_compress (n : ℕ) {r : ℕ} (e : Fin r → Fin n)
    (he : StrictMono e) (m : Fin n → ℝ) (v : Fin n → E)
    (hv : ∀ t, (∀ j, e j ≠ t) → v t = 0) (f : E → ℝ) :
    vectorHierarchy n m v f = vectorHierarchy r (m ∘ e) (v ∘ e) f := by
  induction n generalizing r f with
  | zero =>
    cases r with
    | zero => rfl
    | succ r => exact Fin.elim0 (e 0)
  | succ n ih =>
    cases r with
    | zero =>
      have hlast : v (Fin.last n) = 0 := hv _ (fun j => Fin.elim0 j)
      simp only [vectorHierarchy,hlast,vectorStep_zero]
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
        rw [vectorHierarchy,vectorHierarchy,← hlast]
        have H := ih e' he' (fun i => m i.castSucc) (fun i => v i.castSucc) hv'
          (vectorStep (m (e (Fin.last r))) (v (e (Fin.last r))) f)
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
        rw [vectorHierarchy,hzero,vectorStep_zero]
        have H := ih e' he' (fun i => m i.castSucc) (fun i => v i.castSucc) hv' f
        simpa only [Function.comp_def,hcast] using H
end Vector

end SK.Analytic

end
end

end OAI
