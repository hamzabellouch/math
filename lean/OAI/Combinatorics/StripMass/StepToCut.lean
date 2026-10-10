import Mathlib
import OAI.Combinatorics.StripMass.CutStateSound

namespace OAI

/-! Critical honeycomb strip paths, polynomial identities and crossing mass. -/



namespace CriticalStrip.Diagram
noncomputable section
open Finset
open scoped Classical
namespace Pairing

theorem inlinePrivate74_cut_input_left {n : ℕ} (p : Pairing n) (a b : Fin n) (t : Tile)
    (ha : p.Occupied a) (hn : ¬p.Adj a b) : CutPatch.Adj (p.cutShape a b) t 0 4 := by
  by_cases hb : p.Occupied b <;> simp only [cutShape,ha,hb,hn,ite_true,ite_false]
  all_goals exact Or.inl (by simp [CutPatch.inputEdges])

theorem inlinePrivate74_cut_input_right {n : ℕ} (p : Pairing n) (a b : Fin n) (t : Tile)
    (hb : p.Occupied b) (hn : ¬p.Adj a b) : CutPatch.Adj (p.cutShape a b) t 1 5 := by
  by_cases ha : p.Occupied a <;> simp only [cutShape,ha,hb,hn,ite_true,ite_false]
  all_goals exact Or.inl (by simp [CutPatch.inputEdges])

theorem inlinePrivate74_cut_input_paired {n : ℕ} (p : Pairing n) (a b : Fin n) (t : Tile)
    (hn : p.Adj a b) : CutPatch.Adj (p.cutShape a b) t 0 1 := by
  have ha : p.Occupied a := ⟨b,hn⟩
  have hb : p.Occupied b := ⟨a,adj_symm hn⟩
  simp only [cutShape,ha,hb,hn,ite_true]
  exact Or.inl (by simp [CutPatch.inputEdges])

theorem cutReach_left {n : ℕ} (p : Pairing n) (a b : Fin n) (hab : a≠b) (t : Tile)
    (j : Fin n) (h : p.Adj a j) :
    Relation.ReflTransGen (p.cutGraph a b t) (.inl 0) (p.stepToCut a b (.old j)) := by
  have ha : p.Occupied a := ⟨j,h⟩
  have hja : j≠a := by rintro rfl; exact p.adj_irrefl _ h
  by_cases hjb : j=b
  · subst j
    simp only [stepToCut,Ne.symm hab,ite_false,ite_true]
    exact .single (inlinePrivate74_cut_input_paired p a b t h)
  · have hn : ¬p.Adj a b := fun hh => hjb (adj_unique h hh)
    have hj : p.partnerOrSelf a=j := ((p.adj_partnerOrSelf a j).mp h).2.symm
    simp only [stepToCut,hja,hjb,ite_false]
    refine (Relation.ReflTransGen.single (show p.cutGraph a b t (.inl 0) (.inl 4) from inlinePrivate74_cut_input_left p a b t ha hn)).tail ?_
    exact ⟨2,(p.cutShape_active_two a b t).mpr ⟨ha,hn⟩,rfl,by simp [cutLabels,hj]⟩

theorem cutReach_right {n : ℕ} (p : Pairing n) (a b : Fin n) (hab : a≠b) (t : Tile)
    (j : Fin n) (h : p.Adj b j) :
    Relation.ReflTransGen (p.cutGraph a b t) (.inl 1) (p.stepToCut a b (.old j)) := by
  have hb : p.Occupied b := ⟨j,h⟩
  have hjb : j≠b := by rintro rfl; exact p.adj_irrefl _ h
  by_cases hja : j=a
  · subst j
    simp only [stepToCut,ite_true]
    exact .single ((CutPatch.adj_symmetric _ _).symm _ _ (inlinePrivate74_cut_input_paired p a b t (adj_symm h)))
  · have hn : ¬p.Adj a b := fun hh => hja (adj_unique h (adj_symm hh))
    have hj : p.partnerOrSelf b=j := ((p.adj_partnerOrSelf b j).mp h).2.symm
    simp only [stepToCut,hja,hjb,ite_false]
    refine (Relation.ReflTransGen.single (show p.cutGraph a b t (.inl 1) (.inl 5) from inlinePrivate74_cut_input_right p a b t hb hn)).tail ?_
    exact ⟨3,(p.cutShape_active_three a b t).mpr ⟨hb,hn⟩,rfl,by simp [cutLabels,hj]⟩

theorem cutReach_old_edge {n : ℕ} (p : Pairing n) (a b : Fin n) (hab : a≠b) (t : Tile)
    (i j : Fin n) (h : p.Adj i j) :
    Relation.ReflTransGen (p.cutGraph a b t) (p.stepToCut a b (.old i)) (p.stepToCut a b (.old j)) := by
  by_cases hia : i=a
  · subst i
    simp only [stepToCut,ite_true]
    exact cutReach_left p a b hab t j h
  by_cases hib : i=b
  · subst i
    simpa only [stepToCut,Ne.symm hab,ite_false,ite_true] using cutReach_right p a b hab t j h
  by_cases hja : j=a
  · subst j
    have hh := symm (cutReach_left p a b hab t i (adj_symm h))
    simpa only [stepToCut,ite_true] using hh
  by_cases hjb : j=b
  · subst j
    have hh := symm (cutReach_right p a b hab t i (adj_symm h))
    simpa only [stepToCut,Ne.symm hab,ite_false,ite_true] using hh
  simp only [stepToCut,hia,hib,hja,hjb,ite_false]
  exact .single ((omitTwo_adj p a b i j).mpr ⟨h,hia,hib,hja,hjb⟩)

theorem cutReach_box_output {n : ℕ} (p : Pairing n) (a b : Fin n) (t : Tile)
    (k : Fin 4) (i : Fin n) (h : p.stepWiring a b t (.box k) (.out i)) :
    Relation.ReflTransGen (p.cutGraph a b t) (p.stepToCut a b (.box k)) (p.stepToCut a b (.out i)) := by
  rcases h with ⟨rfl,rfl,h⟩ | ⟨rfl,rfl,h⟩
  · exact .single ⟨0,(CutPatch.active_zero _ _).mpr h,rfl,by simp [cutLabels]⟩
  · exact .single ⟨1,(CutPatch.active_one _ _).mpr h,rfl,by simp [cutLabels]⟩

theorem cutReach_old_box {n : ℕ} (p : Pairing n) (a b : Fin n) (hab : a≠b) (t : Tile)
    (i : Fin n) (k : Fin 4) (h : p.stepWiring a b t (.old i) (.box k)) :
    Relation.ReflTransGen (p.cutGraph a b t) (p.stepToCut a b (.old i)) (p.stepToCut a b (.box k)) := by
  rcases h with ⟨rfl,rfl,h⟩ | ⟨rfl,rfl,h⟩
  · simp only [stepToCut,ite_true]; exact .refl
  · simp only [stepToCut,Ne.symm hab,ite_false,ite_true]; exact .refl

theorem cutReach_old_output {n : ℕ} (p : Pairing n) (a b : Fin n) (t : Tile)
    (i j : Fin n) (h : p.stepWiring a b t (.old i) (.out j)) :
    Relation.ReflTransGen (p.cutGraph a b t) (p.stepToCut a b (.old i)) (p.stepToCut a b (.out j)) := by
  obtain ⟨rfl,hia,hib,hi⟩ := h
  simp only [stepToCut,hia,hib,ite_false]
  exact .refl

theorem stepToCut_edge {n : ℕ} (p : Pairing n) (a b : Fin n) (hab : a≠b) (t : Tile)
    (v w : StepVertex n) (h : p.stepWiring a b t v w) :
    Relation.ReflTransGen (p.cutGraph a b t) (p.stepToCut a b v) (p.stepToCut a b w) := by
  cases v with
  | old i =>
    cases w with
    | old j => exact cutReach_old_edge p a b hab t i j h
    | box k => exact cutReach_old_box p a b hab t i k h
    | out j => exact cutReach_old_output p a b t i j h
  | box k =>
    cases w with
    | old i => exact symm (cutReach_old_box p a b hab t i k h)
    | box l => exact .single (Or.inr (Or.inr ⟨k,l,h,rfl,rfl⟩))
    | out i => exact cutReach_box_output p a b t k i h
  | out i =>
    cases w with
    | old j => exact symm (cutReach_old_output p a b t j i h)
    | box k => exact symm (cutReach_box_output p a b t k i h)
    | out j => exact h.elim


 

 


@[simp] theorem cutToStep_tilePort {n : ℕ} (p : Pairing n) (a b : Fin n) (k : Fin 4) :
    p.cutToStep a b (.inl (CutPatch.tilePort k)) = .box k := by
  fin_cases k <;> rfl

theorem partnerOrSelf_occupied {n : ℕ} (p : Pairing n) (a : Fin n) (ha : p.Occupied a) :
    p.Occupied (p.partnerOrSelf a) :=
  ⟨a,adj_symm ((adj_partnerOrSelf p a _).mpr ⟨ha,rfl⟩)⟩

theorem partnerOrSelf_away_left {n : ℕ} (p : Pairing n) (a b : Fin n)
    (ha : p.Occupied a) (hn : ¬p.Adj a b) : p.partnerOrSelf a ≠ b := by
  intro h
  exact hn ((adj_partnerOrSelf p a b).mpr ⟨ha,h.symm⟩)

theorem step_input_left {n : ℕ} (p : Pairing n) (a b : Fin n) (t : Tile)
    (ha : p.Occupied a) :
    Relation.ReflTransGen (p.stepWiring a b t) (.box 0) (.old (p.partnerOrSelf a)) := by
  refine (Relation.ReflTransGen.single (show p.stepWiring a b t (.box 0) (.old a) from Or.inl ⟨rfl,rfl,ha⟩)).tail ?_
  exact (adj_partnerOrSelf p a _).mpr ⟨ha,rfl⟩

theorem step_input_right {n : ℕ} (p : Pairing n) (a b : Fin n) (t : Tile)
    (hb : p.Occupied b) :
    Relation.ReflTransGen (p.stepWiring a b t) (.box 1) (.old (p.partnerOrSelf b)) := by
  refine (Relation.ReflTransGen.single (show p.stepWiring a b t (.box 1) (.old b) from Or.inr ⟨rfl,rfl,hb⟩)).tail ?_
  exact (adj_partnerOrSelf p b _).mpr ⟨hb,rfl⟩

theorem step_input_paired {n : ℕ} (p : Pairing n) (a b : Fin n) (t : Tile)
    (hn : p.Adj a b) : Relation.ReflTransGen (p.stepWiring a b t) (.box 0) (.box 1) := by
  have h₁ : p.stepWiring a b t (.box 0) (.old a) := Or.inl ⟨rfl,rfl,⟨b,hn⟩⟩
  have h₂ : p.stepWiring a b t (.old a) (.old b) := hn
  have h₃ : p.stepWiring a b t (.old b) (.box 1) := Or.inr ⟨rfl,rfl,⟨a,adj_symm hn⟩⟩
  exact ((Relation.ReflTransGen.single h₁).tail h₂).tail h₃

theorem cut_input_cases {n : ℕ} (p : Pairing n) (a b : Fin n) (v w : Fin 6)
    (h : (v,w) ∈ CutPatch.inputEdges (p.cutShape a b)) :
    (v=0 ∧ w=4 ∧ p.Occupied a) ∨ (v=1 ∧ w=5 ∧ p.Occupied b) ∨
      (v=0 ∧ w=1 ∧ p.Adj a b) := by
  by_cases ha : p.Occupied a <;> by_cases hb : p.Occupied b <;> by_cases hn : p.Adj a b <;>
    simp [cutShape,ha,hb,hn,CutPatch.inputEdges,Prod.mk.injEq] at h ⊢ <;> itauto

theorem stepReach_input_edge {n : ℕ} (p : Pairing n) (a b : Fin n) (t : Tile)
    (v w : Fin 6) (h : (v,w) ∈ CutPatch.inputEdges (p.cutShape a b)) :
    Relation.ReflTransGen (p.stepWiring a b t) (p.cutToStep a b (.inl v)) (p.cutToStep a b (.inl w)) := by
  rcases cut_input_cases p a b v w h with ⟨rfl,rfl,ha⟩ | ⟨rfl,rfl,hb⟩ | ⟨rfl,rfl,hn⟩
  · exact step_input_left p a b t ha
  · exact step_input_right p a b t hb
  · exact step_input_paired p a b t hn

theorem stepReach_interface {n : ℕ} (p : Pairing n) (a b : Fin n) (t : Tile)
    (i : Fin 4) (hi : CutPatch.active (p.cutShape a b) t i) :
    Relation.ReflTransGen (p.stepWiring a b t)
      (p.cutToStep a b (.inl (CutPatch.boundary i))) (p.cutToStep a b (.inr (p.cutLabels a b i))) := by
  fin_cases i
  · exact .single (Or.inl ⟨rfl,rfl,(CutPatch.active_zero _ _).mp hi⟩)
  · exact .single (Or.inr ⟨rfl,rfl,(CutPatch.active_one _ _).mp hi⟩)
  · obtain ⟨ha,hn⟩ := (p.cutShape_active_two a b t).mp hi
    exact .single ⟨rfl,p.partnerOrSelf_ne a ha,p.partnerOrSelf_away_left a b ha hn,
      p.partnerOrSelf_occupied a ha⟩
  · obtain ⟨hb,hn⟩ := (p.cutShape_active_three a b t).mp hi
    have hna : ¬p.Adj b a := fun hh => hn (adj_symm hh)
    exact .single ⟨rfl,p.partnerOrSelf_away_left b a hb hna,p.partnerOrSelf_ne b hb,
      p.partnerOrSelf_occupied b hb⟩

theorem stepReach_omitted {n : ℕ} (p : Pairing n) (a b : Fin n) (t : Tile)
    (i j : Fin n) (h : (p.omitTwo a b).Adj i j) :
    Relation.ReflTransGen (p.stepWiring a b t) (.out i) (.out j) := by
  obtain ⟨h,hia,hib,hja,hjb⟩ := (omitTwo_adj p a b i j).mp h
  have h₁ : p.stepWiring a b t (.out i) (.old i) := ⟨rfl,hia,hib,⟨j,h⟩⟩
  have h₂ : p.stepWiring a b t (.old i) (.old j) := h
  have h₃ : p.stepWiring a b t (.old j) (.out j) := ⟨rfl,hja,hjb,⟨i,adj_symm h⟩⟩
  exact ((Relation.ReflTransGen.single h₁).tail h₂).tail h₃

theorem cutToStep_edge {n : ℕ} (p : Pairing n) (a b : Fin n) (t : Tile)
    (v w : Sum (Fin 6) (Fin n)) (h : p.cutGraph a b t v w) :
    Relation.ReflTransGen (p.stepWiring a b t) (p.cutToStep a b v) (p.cutToStep a b w) := by
  cases v with
  | inl v =>
    cases w with
    | inl w =>
      rcases h with h | h | ⟨i,j,h,rfl,rfl⟩
      · exact stepReach_input_edge p a b t v w h
      · exact symm (stepReach_input_edge p a b t w v h)
      · simp only [cutToStep_tilePort]
        exact .single h
    | inr w =>
      obtain ⟨i,hi,rfl,rfl⟩ := h
      exact stepReach_interface p a b t i hi
  | inr v =>
    cases w with
    | inl w =>
      obtain ⟨i,hi,rfl,rfl⟩ := h
      exact symm (stepReach_interface p a b t i hi)
    | inr w => exact stepReach_omitted p a b t v w h

end Pairing
end

 

 

noncomputable section
open scoped Classical

namespace Graph

theorem used_of_reach_ne {V : Type*} {r : V → V → Prop} {v w : V}
    (h : Relation.ReflTransGen r v w) (hne : v ≠ w) : Used r v := by
  rcases h.cases_head with h | ⟨x,hx,_⟩
  · exact (hne h).elim
  · exact ⟨x,hx⟩

end Graph

@[simp] theorem Tile.adj_irrefl (t : Tile) (i : Fin 4) : ¬t.Adj i i := by
  cases t <;> fin_cases i <;> decide

namespace Pairing

theorem stepToCut_old_injective {n : ℕ} (p : Pairing n) (a b : Fin n) :
    Function.Injective (fun i => p.stepToCut a b (.old i)) := by
  intro i j h
  by_cases hia : i=a <;> by_cases hib : i=b <;>
    by_cases hja : j=a <;> by_cases hjb : j=b <;>
    simp_all [stepToCut]

theorem cutGraph_used_old {n : ℕ} (p : Pairing n) (a b : Fin n) (hab : a≠b) (t : Tile)
    (i : Fin n) (hi : p.Occupied i) : Graph.Used (p.cutGraph a b t) (p.stepToCut a b (.old i)) := by
  obtain ⟨j,hj⟩ := hi
  apply Graph.used_of_reach_ne (p.cutReach_old_edge a b hab t i j hj)
  intro hh
  have := p.stepToCut_old_injective a b hh
  subst j
  exact p.adj_irrefl i hj

theorem stepWiring_old_used {n : ℕ} (p : Pairing n) (a b : Fin n) (t : Tile)
    (i : Fin n) : Graph.Used (p.stepWiring a b t) (.old i) ↔ p.Occupied i := by
  constructor
  · rintro ⟨v,hv⟩
    cases v with
    | old j => exact ⟨j,hv⟩
    | box k => rcases hv with ⟨rfl,_,h⟩ | ⟨rfl,_,h⟩ <;> exact h
    | out j => exact hv.2.2.2
  · rintro ⟨j,hj⟩
    exact ⟨.old j,hj⟩

theorem stepToCut_used {n : ℕ} (p : Pairing n) (a b : Fin n) (hab : a≠b) (t : Tile)
    (v : StepVertex n) (hv : Graph.Used (p.stepWiring a b t) v) :
    Graph.Used (p.cutGraph a b t) (p.stepToCut a b v) := by
  cases v with
  | old i => exact p.cutGraph_used_old a b hab t i ((p.stepWiring_old_used a b t i).mp hv)
  | box k =>
    obtain ⟨w,hw⟩ := hv
    cases w with
    | old i =>
      rcases hw with ⟨hia,hk,ha⟩ | ⟨hib,hk,hb⟩
      · subst i k
        simpa [stepToCut,CutPatch.tilePort] using p.cutGraph_used_old a b hab t a ha
      · subst i k
        simpa [stepToCut,hab.symm,CutPatch.tilePort] using p.cutGraph_used_old a b hab t b hb
    | box l => exact ⟨.inl (CutPatch.tilePort l),Or.inr (Or.inr ⟨k,l,hw,rfl,rfl⟩)⟩
    | out i =>
      apply Graph.used_of_reach_ne (p.stepToCut_edge a b hab t (.box k) (.out i) hw)
      simp [stepToCut]
  | out i =>
    obtain ⟨w,hw⟩ := hv
    cases w with
    | old j =>
      obtain ⟨rfl,hja,hjb,hj⟩ := hw
      simpa [stepToCut,hja,hjb] using p.cutGraph_used_old a b hab t j hj
    | box k =>
      apply Graph.used_of_reach_ne (p.stepToCut_edge a b hab t (.out i) (.box k) hw)
      simp [stepToCut]
    | out j => exact hw.elim

theorem cutToStep_edge_ne {n : ℕ} (p : Pairing n) (a b : Fin n) (t : Tile)
    (v w : Sum (Fin 6) (Fin n)) (h : p.cutGraph a b t v w) :
    p.cutToStep a b v ≠ p.cutToStep a b w := by
  cases v with
  | inl v =>
    cases w with
    | inl w =>
      rcases h with h | h | ⟨i,j,h,rfl,rfl⟩
      · rcases p.cut_input_cases a b v w h with ⟨rfl,rfl,_⟩ | ⟨rfl,rfl,_⟩ | ⟨rfl,rfl,_⟩ <;>
          simp [cutToStep]
      · rcases p.cut_input_cases a b w v h with ⟨rfl,rfl,_⟩ | ⟨rfl,rfl,_⟩ | ⟨rfl,rfl,_⟩ <;>
          simp [cutToStep]
      · simp only [cutToStep_tilePort,ne_eq,StepVertex.box.injEq]
        intro hh
        subst j
        exact t.adj_irrefl i h
    | inr w =>
      obtain ⟨i,_,rfl,rfl⟩ := h
      fin_cases i <;> simp [cutToStep,CutPatch.boundary]
  | inr v =>
    cases w with
    | inl w =>
      obtain ⟨i,_,rfl,rfl⟩ := h
      fin_cases i <;> simp [cutToStep,CutPatch.boundary]
    | inr w =>
      simp only [cutToStep,ne_eq,StepVertex.out.injEq]
      intro hh
      subst w
      exact (p.omitTwo a b).adj_irrefl v h

theorem cutToStep_used {n : ℕ} (p : Pairing n) (a b : Fin n) (t : Tile)
    (v : Sum (Fin 6) (Fin n)) (hv : Graph.Used (p.cutGraph a b t) v) :
    Graph.Used (p.stepWiring a b t) (p.cutToStep a b v) := by
  obtain ⟨w,hw⟩ := hv
  exact Graph.used_of_reach_ne (p.cutToStep_edge a b t v w hw) (p.cutToStep_edge_ne a b t v w hw)

end Pairing

 

 


namespace CutPatch

theorem adj_four_active : ∀ (s : Shape) (t : Tile) (v : Fin 6), Adj s t 4 v → active s t 2 := by
  decide

theorem adj_five_active : ∀ (s : Shape) (t : Tile) (v : Fin 6), Adj s t 5 v → active s t 3 := by
  decide

end CutPatch

namespace Pairing

theorem cutGraph_used_four {n : ℕ} (p : Pairing n) (a b : Fin n) (t : Tile)
    (h : Graph.Used (p.cutGraph a b t) (.inl 4)) : CutPatch.active (p.cutShape a b) t 2 := by
  obtain ⟨w,hw⟩ := h
  cases w with
  | inl w => exact CutPatch.adj_four_active _ _ w hw
  | inr w =>
    obtain ⟨i,hi,hb,_⟩ := hw
    fin_cases i <;> simp_all [CutPatch.boundary]

theorem cutGraph_used_five {n : ℕ} (p : Pairing n) (a b : Fin n) (t : Tile)
    (h : Graph.Used (p.cutGraph a b t) (.inl 5)) : CutPatch.active (p.cutShape a b) t 3 := by
  obtain ⟨w,hw⟩ := h
  cases w with
  | inl w => exact CutPatch.adj_five_active _ _ w hw
  | inr w =>
    obtain ⟨i,hi,hb,_⟩ := hw
    fin_cases i <;> simp_all [CutPatch.boundary]

theorem stepToCut_retract {n : ℕ} (p : Pairing n) (a b : Fin n) (t : Tile)
    (v : StepVertex n) (hv : Graph.Used (p.stepWiring a b t) v) :
    Relation.ReflTransGen (p.stepWiring a b t) v (p.cutToStep a b (p.stepToCut a b v)) := by
  cases v with
  | old i =>
    have hi := (p.stepWiring_old_used a b t i).mp hv
    by_cases hia : i=a
    · subst i
      simp only [stepToCut,ite_true,cutToStep,Matrix.cons_val_zero]
      exact .single (Or.inl ⟨rfl,rfl,hi⟩)
    · by_cases hib : i=b
      · subst i
        simp only [stepToCut,hia,ite_false,ite_true,cutToStep,Matrix.cons_val_one,
          Matrix.cons_val_zero]
        exact .single (Or.inr ⟨rfl,rfl,hi⟩)
      · simp only [stepToCut,hia,hib,ite_false,cutToStep]
        exact .single ⟨rfl,hia,hib,hi⟩
  | box k => rw [stepToCut,cutToStep_tilePort]
  | out i => exact .refl

theorem cutToStep_retract {n : ℕ} (p : Pairing n) (a b : Fin n) (t : Tile)
    (v : Sum (Fin 6) (Fin n)) (hv : Graph.Used (p.cutGraph a b t) v) :
    Relation.ReflTransGen (p.cutGraph a b t) v (p.stepToCut a b (p.cutToStep a b v)) := by
  cases v with
  | inl k =>
    fin_cases k
    · exact .refl
    · exact .refl
    · exact .refl
    · exact .refl
    · have hi := p.cutGraph_used_four a b t hv
      obtain ⟨ha,hn⟩ := (p.cutShape_active_two a b t).mp hi
      have hpa := p.partnerOrSelf_ne a ha
      have hpb := p.partnerOrSelf_away_left a b ha hn
      change Relation.ReflTransGen (p.cutGraph a b t) (.inl 4)
        (p.stepToCut a b (.old (p.partnerOrSelf a)))
      simp only [stepToCut,hpa,hpb,ite_false]
      exact .single ⟨2,hi,rfl,rfl⟩
    · have hi := p.cutGraph_used_five a b t hv
      obtain ⟨hb,hn⟩ := (p.cutShape_active_three a b t).mp hi
      have hpb := p.partnerOrSelf_ne b hb
      have hna : ¬ p.Adj b a := fun hh => hn (adj_symm hh)
      have hpa := p.partnerOrSelf_away_left b a hb hna
      change Relation.ReflTransGen (p.cutGraph a b t) (.inl 5)
        (p.stepToCut a b (.old (p.partnerOrSelf b)))
      simp only [stepToCut,hpa,hpb,ite_false]
      exact .single ⟨3,hi,rfl,rfl⟩
  | inr i => exact .refl

def stepCutEquiv {n : ℕ} (p : Pairing n) (a b : Fin n) (hab : a≠b) (t : Tile) :
    Graph.BoundaryEquiv (p.stepWiring a b t) (p.cutGraph a b t) StepVertex.out Sum.inr where
  toFun := p.stepToCut a b
  invFun := p.cutToStep a b
  map_edge := p.stepToCut_edge a b hab t
  inv_edge := p.cutToStep_edge a b t
  map_boundary := fun _ => rfl
  inv_boundary := fun _ => rfl
  map_used := p.stepToCut_used a b hab t
  inv_used := p.cutToStep_used a b t
  retract := p.stepToCut_retract a b t
  inv_retract := p.cutToStep_retract a b t

theorem stepWiring_realizes {n : ℕ} (p : Pairing n) (a b : Fin n)
    (hab : a.val+1=b.val) (t : Tile) (q : Pairing n)
    (hq : p.tileStep a b hab t = some q) :
    GraphRealizes (p.stepWiring a b t) StepVertex.out q := by
  have hne : a≠b := by intro hh; have := congrArg Fin.val hh; omega
  exact (p.stepCutEquiv a b hne t).symm.realizes (p.cutGraph_realizes a b hab t q hq)


 

 



theorem ext_adj {n : ℕ} {p q : Pairing n} (h : ∀ i j, p.Adj i j ↔ q.Adj i j) : p=q := by
  apply Subtype.ext
  ext e
  constructor
  · intro he
    rcases (h e.1 e.2).mp (Or.inl he) with hh | hh
    · exact hh
    · have hp := p.property.1 _ he
      have hq := q.property.1 _ hh
      exact (lt_asymm hp hq).elim
  · intro he
    rcases (h e.1 e.2).mpr (Or.inl he) with hh | hh
    · exact hh
    · have hp := q.property.1 _ he
      have hq := p.property.1 _ hh
      exact (lt_asymm hp hq).elim

theorem graphRealizes {n : ℕ} (p : Pairing n) : GraphRealizes p.Adj id p where
  no_loop := fun v w h => ⟨v,⟨w,h⟩,.refl⟩
  reach := p.reach_adj_iff

end Pairing

namespace GraphRealizes

theorem unique {V : Type*} {n : ℕ} {r : V → V → Prop} {a : Fin n → V}
    {p q : Pairing n} (hp : GraphRealizes r a p) (hq : GraphRealizes r a q) : p=q := by
  apply Pairing.ext_adj
  intro i j
  by_cases hij : i=j
  · subst j; simp only [p.adj_irrefl,q.adj_irrefl]
  · have hh := (hp.reach i j).symm.trans (hq.reach i j)
    simpa only [hij,false_or] using hh

 

theorem compressed_eq {V B : Type*} {n : ℕ} {r : V → V → Prop} {a : Fin n → V}
    {p : Pairing n} (h : GraphRealizes r a p) (s : B → B → Prop) (b : Fin n → B) :
    Patch.compressed r s a b p.Occupied = Patch.compressed p.Adj s id b p.Occupied := by
  funext x y
  apply propext
  simp only [Patch.compressed,h.reach,Pairing.reach_adj_iff,id_eq]

theorem drains_glued_iff {V B : Type*} {n : ℕ} {r : V → V → Prop} {a : Fin n → V}
    {p : Pairing n} (h : GraphRealizes r a p) (s : B → B → Prop) (b : Fin n → B)
    (out : B → Prop) :
    Patch.drains (Patch.glued r s a b p.Occupied) (Patch.exteriorOutput out) ↔
      Patch.drains (Patch.glued p.Adj s id b p.Occupied) (Patch.exteriorOutput out) := by
  rw [Patch.drains_glued_iff,Patch.drains_glued_iff,h.compressed_eq s b]
  have hp := p.graphRealizes
  exact ⟨fun hh => ⟨hp.no_loop,hh.2⟩,fun hh => ⟨h.no_loop,hh.2⟩⟩

end GraphRealizes

namespace Patch

theorem realizes_iff_drains {V B : Type*} {n m : ℕ} (r : V → V → Prop)
    (s : B → B → Prop) (a : Fin n → V) (b : Fin n → B) (active : Fin n → Prop)
    (c : Fin m → B) (q : Pairing m) :
    GraphRealizes (glued r s a b active) (fun i => .inr (c i)) q ↔
      drains (glued r s a b active) (exteriorOutput (fun x => ∃ i, q.Occupied i ∧ x=c i)) ∧
      (∀ i j, Relation.ReflTransGen (compressed r s a b active) (c i) (c j) ↔ i=j ∨ q.Adj i j) := by
  constructor
  · intro h
    constructor
    · intro v w hvw
      obtain ⟨i,hi,hr⟩ := h.no_loop v w hvw
      exact ⟨.inr (c i),⟨i,hi,rfl⟩,hr⟩
    · intro i j
      exact (exterior_reach_iff r s a b active).symm.trans (h.reach i j)
  · rintro ⟨hd,hr⟩
    constructor
    · intro v w hvw
      obtain ⟨x,hx,hvx⟩ := hd v w hvw
      cases x with
      | inl x => exact hx.elim
      | inr x =>
        obtain ⟨i,hi,rfl⟩ := hx
        exact ⟨i,hi,hvx⟩
    · intro i j
      exact (exterior_reach_iff r s a b active).trans (hr i j)

end Patch

namespace GraphRealizes

theorem substitute_iff {V B : Type*} {n m : ℕ} {r : V → V → Prop} {a : Fin n → V}
    {p : Pairing n} (h : GraphRealizes r a p) (s : B → B → Prop) (b : Fin n → B)
    (c : Fin m → B) (q : Pairing m) :
    GraphRealizes (Patch.glued r s a b p.Occupied) (fun i => .inr (c i)) q ↔
      GraphRealizes (Patch.glued p.Adj s id b p.Occupied) (fun i => .inr (c i)) q := by
  rw [Patch.realizes_iff_drains,Patch.realizes_iff_drains,h.compressed_eq s b,h.drains_glued_iff s b]

end GraphRealizes
end
end CriticalStrip.Diagram

end OAI
