import Mathlib
import OAI.Geometry.PrescribedRicci.ComplexJet

namespace OAI

/-! Jet Polynomial. -/

section

 

noncomputable section
open Set Finset
open scoped ContDiff Classical BigOperators
namespace TameInterpolation
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {ι κ : Type*} [Fintype κ] [DecidableEq κ]

def cword (e : ι → E) (f : E → ℂ) : List ι → E → ℂ
  | [] => f
  | a::as => cdir (e a) (cword e f as)

lemma cword_smooth (e : ι → E) {f : E → ℂ} (hf : ContDiff ℝ ∞ f) (as : List ι) :
    ContDiff ℝ ∞ (cword e f as) := by
  induction as with
  | nil => exact hf
  | cons a as ih => exact cdir_smooth _ ih

lemma cword_compact (e : ι → E) {f : E → ℂ} (hf : HasCompactSupport f) (as : List ι) :
    HasCompactSupport (cword e f as) := by
  induction as with
  | nil => exact hf
  | cons a as ih => exact cdir_compact _ ih

def monoEval (e : ι → E) (f : κ → E → ℂ) (s : κ → List ι) (x : E) : ℂ :=
  ∏ i, cword e (f i) (s i) x

def stepState (a : ι) (s : κ → List ι) (i : κ) : κ → List ι :=
  Function.update s i (a::s i)

def stateOrder (s : κ → List ι) : ℕ := ∑ i, (s i).length

def activeSet (s : κ → List ι) : Finset κ := Finset.univ.filter fun i => s i ≠ []

lemma stateOrder_step (a : ι) (s : κ → List ι) (i : κ) :
    stateOrder (stepState a s i) = stateOrder s+1 := by
  unfold stateOrder
  rw [← Finset.add_sum_erase Finset.univ (fun j => (stepState a s i j).length) (Finset.mem_univ i),
    ← Finset.add_sum_erase Finset.univ (fun j => (s j).length) (Finset.mem_univ i)]
  simp only [stepState,Function.update_self,List.length_cons]
  have he : ∑ j ∈ Finset.univ.erase i, (Function.update s i (a::s i) j).length =
      ∑ j ∈ Finset.univ.erase i, (s j).length := by
    apply Finset.sum_congr rfl
    intro j hj
    rw [Function.update_of_ne (by simpa using (Finset.mem_erase.mp hj).1)]
  rw [he]; omega

lemma activeSet_step (a : ι) (s : κ → List ι) (i : κ) :
    activeSet (stepState a s i) = insert i (activeSet s) := by
  apply Finset.ext
  intro j
  change j ∈ Finset.univ.filter (fun j => stepState a s i j ≠ []) ↔
    j ∈ insert i (Finset.univ.filter (fun j => s j ≠ []))
  rw [Finset.mem_filter,Finset.mem_insert,Finset.mem_filter]
  simp only [Finset.mem_univ,true_and]
  by_cases hj : j = i
  · subst j; simp [stepState]
  · simp [stepState,hj]

omit [DecidableEq κ] in
lemma monoEval_smooth (e : ι → E) (f : κ → E → ℂ) (hf : ∀ i, ContDiff ℝ ∞ (f i))
    (s : κ → List ι) : ContDiff ℝ ∞ (monoEval e f s) := by
  apply contDiff_prod
  intro i _
  exact cword_smooth e (hf i) _

lemma cdir_monoEval (e : ι → E) (f : κ → E → ℂ) (hf : ∀ i, ContDiff ℝ ∞ (f i))
    (a : ι) (s : κ → List ι) :
    cdir (e a) (monoEval e f s) = fun x => ∑ i, monoEval e f (stepState a s i) x := by
  funext x
  unfold cdir monoEval
  rw [fderiv_finsetProd (fun i _ => (cword_smooth e (hf i) _).differentiable (by simp) x)]
  simp only [_root_.sum_apply,smul_apply,smul_eq_mul]
  apply Finset.sum_congr rfl
  intro i _
  rw [← Finset.mul_prod_erase Finset.univ
    (fun j => cword e (f j) (stepState a s i j) x) (Finset.mem_univ i)]
  simp only [stepState,Function.update_self,cword,cdir]
  have he : ∏ j ∈ Finset.univ.erase i, cword e (f j) (Function.update s i (a::s i) j) x =
      ∏ j ∈ Finset.univ.erase i, cword e (f j) (s j) x := by
    apply Finset.prod_congr rfl
    intro j hj
    rw [Function.update_of_ne (by simpa using (Finset.mem_erase.mp hj).1)]
  rw [he]
  ring

lemma cdir_finite_sum (e : ι → E) (a : ι) {ν : Type*} (s : Finset ν)
    (f : ν → E → ℂ) (hf : ∀ i ∈ s, ContDiff ℝ ∞ (f i)) :
    cdir (e a) (fun x => ∑ i ∈ s, f i x) = fun x => ∑ i ∈ s, cdir (e a) (f i) x := by
  funext x
  unfold cdir
  rw [fderiv_fun_sum (fun i hi => (hf i hi).differentiable (by simp) x)]
  simp only [_root_.sum_apply]

lemma cdir_list_sum (e : ι → E) (a : ι) {ν : Type*} (s : List ν)
    (f : ν → E → ℂ) (hf : ∀ i ∈ s, ContDiff ℝ ∞ (f i)) :
    cdir (e a) (fun x => (s.map (fun i => f i x)).sum) =
      fun x => (s.map (fun i => cdir (e a) (f i) x)).sum := by
  induction s with
  | nil => funext x; simp [cdir]
  | cons i s ih =>
    have hsum : ContDiff ℝ ∞ (fun x => (s.map (fun j => f j x)).sum) := by
      have hh : ∀ j ∈ s, ContDiff ℝ ∞ (f j) := fun j hj => hf j (List.mem_cons_of_mem i hj)
      clear ih hf
      induction s with
      | nil => exact contDiff_const
      | cons j s ih =>
        exact (hh j (List.mem_cons_self ..)).add (ih (fun k hk => hh k (List.mem_cons_of_mem j hk)))
    simp only [List.map_cons,List.sum_cons]
    funext x
    unfold cdir
    rw [fderiv_fun_add ((hf i (List.mem_cons_self ..)).differentiable (by simp) x)
      (hsum.differentiable (by simp) x),add_apply]
    exact congrArg (fun z : ℂ => fderiv ℝ (f i) x (e a)+z)
      (congrFun (ih (fun j hj => hf j (List.mem_cons_of_mem i hj))) x)
end TameInterpolation

end
end

end OAI
