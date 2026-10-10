import Mathlib
import OAI.Geometry.HyperbolicGroups.Presentation

namespace OAI

section
section


noncomputable section
namespace HyperbolicObstruction
namespace LetterPresentation
open IncidenceTemplate MasterGraph

abbrev ParityGroup := Multiplicative (ZMod 2)
def oddLetter : ParityGroup := Multiplicative.ofAdd 1

@[simp] lemma oddLetter_inv : oddLetter⁻¹ = oddLetter :=
  congrArg Multiplicative.ofAdd (by decide : -(1:ZMod 2) = 1)
@[simp] lemma oddLetter_mul : oddLetter * oddLetter = 1 :=
  congrArg Multiplicative.ofAdd (by decide : (1:ZMod 2)+1 = 0)
lemma oddLetter_ne_one : oddLetter ≠ 1 := by
  intro h
  exact (by decide : (1:ZMod 2) ≠ 0) (congrArg Multiplicative.toAdd h)

def coreParity : MasterGraph.Vertex → ParityGroup
  | .inl (.inl _) => 1
  | .inl (.inr _) => oddLetter
  | .inr _ => 1

lemma coreParity_step {L : Type*} (label : Field → L) {a b : MasterGraph.Vertex}
    (s : Step a b) (hs : ∃ e : Edge, s.field = .inl e) :
    coreParity b = coreParity a * s.value label (fun _ => oddLetter) := by
  obtain ⟨e,he⟩ := hs
  cases h : s.forward
  · obtain ⟨ha,hb⟩ := s.endpoints_neg h
    rw [he] at ha hb
    simp only [Step.value,h,Bool.false_eq_true,ite_false]
    rw [← ha,← hb]
    simp [source,target,coreParity]
  · obtain ⟨ha,hb⟩ := s.endpoints_pos h
    rw [he] at ha hb
    simp only [Step.value,h,ite_true]
    rw [← ha,← hb]
    simp [source,target,coreParity]

lemma coreParity_path {L : Type*} (label : Field → L) {a b : MasterGraph.Vertex}
    (p : MasterGraph.Path a b) (hp : p.IsCore) :
    coreParity b = coreParity a * p.eval label (fun _ => oddLetter) := by
  induction p with
  | nil => simp [Path.eval]
  | cons s p ih =>
    rw [ih (fun f hf => hp f (List.mem_cons_of_mem _ hf)),
      coreParity_step label s (hp _ List.mem_cons_self)]
    simp only [Path.eval,mul_assoc]

lemma coreParity_loop {L : Type*} (label : Field → L) {a : MasterGraph.Vertex}
    (p : MasterGraph.Path a a) (hp : p.IsCore) : p.eval label (fun _ => oddLetter) = 1 := by
  have h := coreParity_path label p hp
  exact mul_left_cancel (h.symm.trans (mul_one _).symm)

variable (n : ℕ)
def freeParity : FreeGroup (Fin (n+1)) →* ParityGroup := FreeGroup.lift (fun _ => oddLetter)
@[simp] lemma freeParity_letter (a : Alphabet n) : freeParity n (freeLetter n a) = oddLetter := by
  unfold freeLetter
  split_ifs <;> simp [freeParity]

variable (w : TableModel.Entry (A := Alphabet n) rowSupport → Bool)
  (d : (Fin 6 → Alphabet n) → Bool)

lemma relator_parity (r : FreeGroup (Fin (n+1))) (hr : Relator n w d r) : freeParity n r = 1 := by
  cases hr with
  | fan l i _ a p hf =>
    rw [Path.eval_map]
    simp only [freeParity_letter]
    apply coreParity_loop
    intro f hf'
    have hh := hf (List.mem_toFinset.mpr hf')
    simp only [rowSupport,Finset.mem_map,Function.Embedding.inl_apply] at hh
    obtain ⟨e,_,he⟩ := hh
    exact ⟨e,he.symm⟩
  | top l _ _ a p hp =>
    rw [Path.eval_map]
    simpa only [freeParity_letter] using coreParity_loop l p hp
  | square l τ _ =>
    rw [squareWord_map]
    simp [squareWord,Step.value]
  | six x _ =>
    rw [map_list_prod,List.map_ofFn]
    norm_num [Function.comp_def,List.ofFn_succ]

/-- The source quotient onto C₂, for every realization including all unmatched
rows. No infinitude or asphericity hypothesis is used here. -/
def parity : Group n w d →* ParityGroup :=
  PresentedGroup.toGroup (fun r hr => relator_parity n w d r hr)

@[simp] lemma parity_letter (a : Alphabet n) : parity n w d (letter n w d a) = oddLetter := by
  change PresentedGroup.toGroup _ (PresentedGroup.mk _ (freeLetter n a)) = _
  change freeParity n (freeLetter n a) = _
  exact freeParity_letter n a

lemma parity_surjective : Function.Surjective (parity n w d) := by
  intro a
  have h : a = 1 ∨ a = oddLetter := by
    have h' : ((Multiplicative.toAdd a):ZMod 2) = 0 ∨ ((Multiplicative.toAdd a):ZMod 2) = 1 := by
      exact (by decide : ∀ b : ZMod 2, b = 0 ∨ b = 1) _
    exact h'
  rcases h with rfl | rfl
  · exact ⟨1,map_one _⟩
  · exact ⟨letter n w d (0,true),parity_letter n w d _⟩

lemma letter_ne_one (a : Alphabet n) : letter n w d a ≠ 1 := by
  intro h
  have hh := congrArg (parity n w d) h
  rw [parity_letter,map_one] at hh
  exact oddLetter_ne_one hh

instance group_nontrivial : Nontrivial (Group n w d) :=
  ⟨⟨letter n w d (0,true),1,letter_ne_one n w d _⟩⟩

end LetterPresentation
end HyperbolicObstruction
end
end

/- Recursive standard-axiom reports for the checked endpoints. -/
end

section

end

end OAI
