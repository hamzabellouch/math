import Mathlib
import OAI.Combinatorics.MatchingCount.Machines.OnlineTraverse
import OAI.Combinatorics.MatchingCount.Tapes.OnlineWord

namespace OAI

namespace MatchingFPRAS.PhysicalStream
open Finset

variable {A B C : Type} [Fintype A] [Fintype B]
noncomputable def qaverage (f : A → ℚ) : ℚ := (∑ a,f a)/Fintype.card A
omit [Fintype A] [Fintype B] in
lemma qaverage_bits {n : ℕ} (f : Bits n → ℚ) : qaverage f=average f := by
  simp [qaverage,average,Bits]
lemma qaverage_equiv (e : A ≃ B) (f : B → ℚ) : qaverage (f ∘ e)=qaverage f := by
  unfold qaverage
  simp only [Function.comp_apply]
  rw [Fintype.card_congr e,e.sum_comp]
lemma qaverage_prod (f : A×B → ℚ) :
    qaverage f=qaverage (fun a=>qaverage (fun b=>f (a,b))) := by
  simp only [qaverage,Fintype.card_prod,Nat.cast_mul,Fintype.sum_prod_type,←sum_div,div_div]
  congr 1
  ring
omit [Fintype B] in
lemma qaverage_congr (f g : A → ℚ) (h : ∀ a,f a=g a) : qaverage f=qaverage g := by
  rw [show f=g from funext h]
omit [Fintype B] in
lemma qaverage_unit (f : (Fin 0 → A) → ℚ) : qaverage f=f Fin.elim0 := by
  simp only [qaverage,Fintype.sum_unique,Fintype.card_fun,Fintype.card_fin,pow_zero,Nat.cast_one,div_one]
  congr 1
def splitFunction (n : ℕ) (A : Type) : (Fin (n+1) → A) ≃ A×(Fin n → A) where
  toFun f := (f 0,fun i=>f i.succ)
  invFun f := Fin.cons f.1 f.2
  left_inv f := by funext i; refine Fin.cases ?_ ?_ i <;> simp
  right_inv f := by rcases f with ⟨a,f⟩; rfl
omit [Fintype B] in
lemma qaverage_succ (n : ℕ) (f : (Fin (n+1) → A) → ℚ) :
    qaverage f=qaverage (fun a : A=>qaverage (fun as : Fin n → A=>f (Fin.cons a as))) := by
  rw [←qaverage_equiv (splitFunction n A).symm f,qaverage_prod]
  rfl

omit [Fintype A] [Fintype B] in
lemma mean_word_qaverage (n : ℕ) (f : List Bool → ℚ) :
    (OnlineWord.prepend n []).mean f=qaverage (fun w : Bits n=>f (List.ofFn w)) := by
  rw [OnlineWord.mean_prepend_nil,qaverage_bits]

omit [Fintype A] [Fintype B] in
lemma mean_traverse_ofFn {X Y Ω : Type} [Fintype Ω]
    (f : X → Experiment Y) (n : ℕ) (xs : Fin n → X) (draw : Fin n → Ω → Y)
    (hf : ∀ i h,(f (xs i)).mean h=qaverage (fun u=>h (draw i u)))
    (h : List Y → ℚ) :
    (OnlineTree.traverseM f (List.ofFn xs)).mean h=
      qaverage (fun us : Fin n → Ω=>h (List.ofFn (fun i=>draw i (us i)))) := by
  induction n generalizing h with
  | zero => simp only [List.ofFn_zero,OnlineTree.traverseM,Experiment.mean,qaverage_unit]
  | succ n ih =>
    rw [List.ofFn_succ,OnlineTree.traverseM,Experiment.mean_bind,hf 0,qaverage_succ]
    apply qaverage_congr
    intro u
    simp only [Experiment.mean_map]
    rw [ih (fun i=>xs i.succ) (fun i=>draw i.succ) (fun i=>hf i.succ)]
    apply qaverage_congr
    intro us
    congr 1
    rw [List.ofFn_succ]
    rfl
end MatchingFPRAS.PhysicalStream

end OAI
