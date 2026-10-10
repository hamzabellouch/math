import OAI.Combinatorics.ContingencyTables.Counting.CompanionRestartSemantics

namespace OAI

/-! # Unused tail bits do not alter the executed restart stages -/
namespace ContingencyTables.DensePrograms
open scoped BigOperators

lemma prefix_sum_add_width_le {q : ℕ} (width : Fin q → ℕ) (i : Fin q) :
    ((List.ofFn width).take i.val).sum+width i ≤ ∑ j,width j := by
  by_cases hi : width i=0
  · rw [hi,Nat.add_zero,←List.sum_ofFn]
    exact (List.take_sublist i.val (List.ofFn width)).sum_le_sum (fun _ _ => Nat.zero_le _)
  · have h := (finSigmaFinEquiv (⟨i,⟨width i-1,by omega⟩⟩ : Sigma (fun i => Fin (width i)))).isLt
    rw [finSigmaFinEquiv_apply,←take_ofFn_sum] at h
    dsimp only at h
    omega

theorem dependentChunk_take_sum {q : ℕ} (width : Fin q → ℕ)
    (bits : List Bool) (i : Fin q) :
    dependentChunk ((List.ofFn width,bits.take (∑ j,width j)),i.val)=
      dependentChunk ((List.ofFn width,bits),i.val) := by
  have hw : (List.ofFn width).getD i.val 0=width i := by
    simp only [List.getD_eq_getElem?_getD,List.getElem?_ofFn,i.isLt,dite_true,Option.getD_some,Fin.eta]
  have hb := prefix_sum_add_width_le width i
  dsimp only [dependentChunk,chunkStart]
  rw [hw,List.drop_take,List.take_take,min_eq_left (by omega)]

end ContingencyTables.DensePrograms

namespace ContingencyTables.CompanionRestartProgram
open CommonBasesFPRAS FirstSuccess DensePrograms FiniteObservableTransport
open scoped BigOperators Classical

lemma stageWord_take_sum (base : List Stage×List ℕ) (bits : List Bool)
    (i : Fin base.1.length) :
    stageWord ((base,bits.take (∑ j : Fin base.1.length,widthAt base j.val)),i.val)=
      stageWord ((base,bits),i.val) := by
  unfold stageWord
  rw [widths_ofFn,widths_ofFn]
  exact dependentChunk_take_sum (fun i : Fin base.1.length => widthAt base i.val) bits i

private lemma foldl_eq_on {A B : Type*} (f g : B → A → B) (xs : List A)
    (h : ∀ a,a ∈ xs → ∀ b,f b a=g b a) (b : B) : xs.foldl f b=xs.foldl g b := by
  induction xs generalizing b with
  | nil => rfl
  | cons a xs ih =>
    simp only [List.foldl_cons]
    rw [h a (by simp) b]
    exact ih (fun a ha b => h a (by simp [ha]) b) _

theorem output_take_sum (base : List Stage×List ℕ) (bits : List Bool) :
    output (base,bits.take (∑ i : Fin base.1.length,widthAt base i.val))=
      output (base,bits) := by
  unfold output
  rw [walk_eq,walk_eq]
  change (List.range base.1.length).foldl
      (fun code i => next (i,((base,bits.take (∑ j : Fin base.1.length,widthAt base j.val)),code))) base.2=
    (List.range base.1.length).foldl (fun code i => next (i,((base,bits),code))) base.2
  apply foldl_eq_on
  intro i hi code
  have hlt : i < base.1.length := List.mem_range.mp hi
  rw [next_detached,next_detached,stageWord_take_sum base bits ⟨i,hlt⟩]

end ContingencyTables.CompanionRestartProgram

namespace ContingencyTables.FiniteObservableTransport
open CommonBasesFPRAS FairBits
open scoped Classical
noncomputable section

theorem SameLaw.append_unused {Y Z : Type*} [Fintype Y] {n : ℕ}
    {f : (Fin n → Bool) → Z} {g : Y → Z} (h : SameLaw f g) (t : ℕ) :
    SameLaw (fun bits : Fin (n+t) → Bool => f (splitWordEquiv n t bits).1) g := by
  intro phi
  have he := uniformAverage_equiv (splitWordEquiv n t)
    (fun p : (Fin n → Bool)×(Fin t → Bool) => phi (f p.1))
  refine he.trans ?_
  rw [uniformAverage_prod]
  simp only [uniformAverage_const]
  exact h phi

theorem restart_append_sameLaw {Y : Type*} [Fintype Y]
    (base : List CompanionRestartProgram.Stage×List ℕ) (n : ℕ)
    (hn : (∑ i : Fin base.1.length,CompanionRestartProgram.widthAt base i.val)=n)
    (g : Y → List ℕ)
    (h : SameLaw (fun bits : Fin n → Bool =>
      CompanionRestartProgram.output (base,List.ofFn bits)) g) (t : ℕ) :
    SameLaw (fun bits : Fin (n+t) → Bool =>
      CompanionRestartProgram.output (base,List.ofFn bits)) g := by
  have hp := h.append_unused t
  have he (bits : Fin (n+t) → Bool) :
      CompanionRestartProgram.output (base,List.ofFn bits)=
        CompanionRestartProgram.output (base,List.ofFn (splitWordEquiv n t bits).1) := by
    have hs := (CompanionRestartProgram.output_take_sum base (List.ofFn bits)).symm
    rw [hn,DensePrograms.ofFn_split_take] at hs
    exact hs
  intro phi
  simp_rw [he]
  exact hp phi

end
end ContingencyTables.FiniteObservableTransport

end OAI
