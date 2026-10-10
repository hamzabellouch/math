import Mathlib
import OAI.Geometry.PrescribedRicci.JetPolynomial

namespace OAI

/-! Jet Remainder. -/

section

 

noncomputable section
open Set Finset
open scoped ContDiff Classical BigOperators
namespace TameInterpolation
variable {ι κ : Type*} [Fintype κ] [DecidableEq κ]

def singleState (ws : List ι) (i : κ) : κ → List ι := Function.update (fun _ => []) i ws

def mixedStep (a : ι) (ws : List ι) : List (κ → List ι) :=
  Finset.univ.toList.flatMap fun i => (Finset.univ.erase i).toList.map fun j =>
    stepState a (singleState ws i) j

def monoRemainder : List ι → List (κ → List ι)
  | [] => []
  | [_] => []
  | a::b::ws => (monoRemainder (b::ws)).flatMap
      (fun s => Finset.univ.toList.map (stepState a s)) ++ mixedStep a (b::ws)

lemma singleState_order (ws : List ι) (i : κ) : stateOrder (singleState ws i) = ws.length := by
  unfold stateOrder
  rw [← Finset.add_sum_erase Finset.univ (fun j => (singleState ws i j).length) (Finset.mem_univ i)]
  simp only [singleState,Function.update_self]
  have he : (∑ j ∈ Finset.univ.erase i, (Function.update (fun _ : κ => ([]:List ι)) i ws j).length) = 0 := by
    apply Finset.sum_eq_zero
    intro j hj
    rw [Function.update_of_ne (Finset.mem_erase.mp hj).1]
    rfl
  rw [he,Nat.add_zero]

lemma singleState_active {ws : List ι} (hw : ws ≠ []) (i : κ) :
    activeSet (singleState ws i) = {i} := by
  apply Finset.ext
  intro j
  change j ∈ Finset.univ.filter (fun j => singleState ws i j ≠ []) ↔ j ∈ ({i}:Finset κ)
  rw [Finset.mem_filter,Finset.mem_singleton]
  simp only [Finset.mem_univ,true_and]
  by_cases hj : j = i
  · subst j; simp [singleState,hw]
  · simp [singleState,hj]

omit [Fintype κ] in
lemma singleState_step_same (a : ι) (ws : List ι) (i : κ) :
    stepState a (singleState ws i) i = singleState (a::ws) i := by
  simp only [stepState,singleState,Function.update_self,Function.update_idem]

lemma monoRemainder_order (ws : List ι) (s : κ → List ι) (hs : s ∈ monoRemainder ws) :
    stateOrder s = ws.length ∧ 2 ≤ (activeSet s).card := by
  induction ws generalizing s with
  | nil => simp [monoRemainder] at hs
  | cons a ws ih =>
    cases ws with
    | nil => simp [monoRemainder] at hs
    | cons b ws =>
      simp only [monoRemainder,List.mem_append] at hs
      rcases hs with hs | hs
      · obtain ⟨s',hs',hs⟩ := List.mem_flatMap.mp hs
        obtain ⟨i,_,rfl⟩ := List.mem_map.mp hs
        have hh := ih s' hs'
        constructor
        · simp only [stateOrder_step,hh.1,List.length_cons]
        · rw [activeSet_step]
          exact hh.2.trans (Finset.card_mono (Finset.subset_insert _ _))
      · obtain ⟨i,_,hs⟩ := List.mem_flatMap.mp hs
        obtain ⟨j,hj,rfl⟩ := List.mem_map.mp hs
        have hji : j ≠ i := (Finset.mem_erase.mp (Finset.mem_toList.mp hj)).1
        constructor
        · simp only [stateOrder_step,singleState_order,List.length_cons]
        · rw [activeSet_step,singleState_active (by simp),
            Finset.card_insert_of_notMem (by simpa using hji),Finset.card_singleton]

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma sum_flatMap_map {α β γ : Type*} [AddCommMonoid γ]
    (s : List α) (g : α → List β) (f : β → γ) :
    ((s.flatMap g).map f).sum = (s.map (fun a => ((g a).map f).sum)).sum := by
  induction s with
  | nil => rfl
  | cons a s ih => simp only [List.flatMap_cons,List.map_append,List.sum_append,List.map_cons,List.sum_cons,ih]

lemma mixedStep_sum (e : ι → E) (f : κ → E → ℂ) (a : ι) (ws : List ι) (x : E) :
    ((mixedStep a ws).map (fun s => monoEval e f s x)).sum =
      ∑ i, ∑ j ∈ Finset.univ.erase i, monoEval e f (stepState a (singleState ws i) j) x := by
  unfold mixedStep
  rw [sum_flatMap_map]
  simp

lemma cdir_principal (e : ι → E) (f : κ → E → ℂ) (hf : ∀ i, ContDiff ℝ ∞ (f i))
    (a : ι) (ws : List ι) :
    cdir (e a) (fun x => ∑ i, monoEval e f (singleState ws i) x) = fun x =>
      (∑ i, monoEval e f (singleState (a::ws) i) x)+
        ((mixedStep a ws).map (fun s => monoEval e f s x)).sum := by
  rw [cdir_finite_sum e a _ _ (fun i _ => monoEval_smooth e f hf _)]
  simp_rw [cdir_monoEval e f hf]
  funext x
  rw [mixedStep_sum,← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  rw [← Finset.add_sum_erase Finset.univ
    (fun j => monoEval e f (stepState a (singleState ws i) j) x) (Finset.mem_univ i),
    singleState_step_same]

lemma monoRemainder_step_sum (e : ι → E) (f : κ → E → ℂ)
    (hf : ∀ i, ContDiff ℝ ∞ (f i)) (a b : ι) (ws : List ι) :
    cdir (e a) (fun x => ((monoRemainder (b::ws)).map (fun s => monoEval e f s x)).sum) =
      fun x => (((monoRemainder (b::ws)).flatMap
        (fun s => Finset.univ.toList.map (stepState a s))).map (fun s => monoEval e f s x)).sum := by
  rw [cdir_list_sum e a _ _ (fun s _ => monoEval_smooth e f hf s)]
  simp_rw [cdir_monoEval e f hf]
  funext x
  rw [sum_flatMap_map]
  simp

omit [DecidableEq κ] in
lemma smooth_mono_list_sum (e : ι → E) (f : κ → E → ℂ)
    (hf : ∀ i, ContDiff ℝ ∞ (f i)) (ss : List (κ → List ι)) :
    ContDiff ℝ ∞ (fun x => (ss.map (fun s => monoEval e f s x)).sum) := by
  induction ss with
  | nil => exact contDiff_const
  | cons s ss ih => exact (monoEval_smooth e f hf s).add ih

theorem cword_product_remainder (e : ι → E) (f : κ → E → ℂ)
    (hf : ∀ i, ContDiff ℝ ∞ (f i)) (ws : List ι) (hw : ws ≠ []) :
    cword e (fun x => ∏ i, f i x) ws = fun x =>
      (∑ i, monoEval e f (singleState ws i) x)+
        ((monoRemainder ws).map (fun s => monoEval e f s x)).sum := by
  induction ws with
  | nil => exact (hw rfl).elim
  | cons a ws ih =>
    cases ws with
    | nil =>
      change cdir (e a) (monoEval e f (fun _ => [])) = _
      rw [cdir_monoEval e f hf]
      funext x
      simp only [monoRemainder,List.map_nil,List.sum_nil,add_zero]
      apply Finset.sum_congr rfl
      intro i _
      rfl
    | cons b ws =>
      have hi := ih (by simp)
      change cdir (e a) (cword e (fun x => ∏ i, f i x) (b::ws)) = _
      rw [hi]
      have h1 : ContDiff ℝ ∞ (fun x => ∑ i, monoEval e f (singleState (b::ws) i) x) := by
        apply ContDiff.sum; intro i _; exact monoEval_smooth e f hf _
      have h2 := smooth_mono_list_sum e f hf (monoRemainder (b::ws))
      have hadd : cdir (e a) (fun x => (∑ i, monoEval e f (singleState (b::ws) i) x)+
          ((monoRemainder (b::ws)).map (fun s => monoEval e f s x)).sum) =
          fun x => cdir (e a) (fun x => ∑ i, monoEval e f (singleState (b::ws) i) x) x+
            cdir (e a) (fun x => ((monoRemainder (b::ws)).map (fun s => monoEval e f s x)).sum) x := by
        funext x
        unfold cdir
        rw [fderiv_fun_add (h1.differentiable (by simp) x) (h2.differentiable (by simp) x)]
        rfl
      rw [hadd,cdir_principal e f hf,monoRemainder_step_sum e f hf]
      funext x
      simp only [monoRemainder,List.map_append,List.sum_append]
      abel
end TameInterpolation

end
end

end OAI
