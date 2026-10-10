import OAI.Computability.MeanPayoff.Realizer

namespace OAI

namespace MeanPayoff
namespace RandomTree
 theorem all_read {α : Type} {Q : α→Prop} (t : RandomTree α) (h : t.All Q) (bits : ℕ→Bool) : Q (t.read bits) := by
  induction t generalizing bits with
  | leaf a => exact h
  | coin l r il ir =>
    simp only [read]
    split
    · exact ir h.2 _
    · exact il h.1 _
end RandomTree
namespace RegisterBits
 theorem tree_coinFree {K : ℕ} (P : Program K) (hq : CoinFree P) (n : ℕ) (c : Config P) :
    (tree P n c).All (fun z => z=advance P (fun _ => false) c n) := by
  induction n generalizing c with
  | zero => rfl
  | succ n ih =>
    rw [advance_front]
    simp only [tree,RandomTree.All,step_coinFree P hq c true]
    exact ⟨ih _,ih _⟩
namespace Compile
 theorem deterministic_packet {K : ℕ} (P : Program K) (hq : CoinFree P) (input : List Bool) (n : ℕ)
    (out : List Bool) (hc : (advance P (fun _ => false) (initial P input) n).control=none)
    (ho : (advance P (fun _ => false) (initial P input) n).output=out) :
    (MeanPayoff.run (machine P) input (fun _ => false) (2*bound P input n)).control=none ∧
    (MeanPayoff.run (machine P) input (fun _ => false) (2*bound P input n)).tape 2=BinaryStack.cells out 0 := by
  have ht : (tree P n (initial P input)).All (fun c => c.control=none ∧ c.output=out) :=
    RandomTree.all_mono _ (tree_coinFree P hq n (initial P input)) (fun c he => by rw [he]; exact ⟨hc,ho⟩)
  have hh : (tree P n (initial P input)).All (fun c => c.control=none) :=
    RandomTree.all_mono _ ht (fun _ h => h.1)
  have hi := (initialized_all P input n _).mpr ht
  have hr := RandomTree.all_read (initializedTree P input n) hi
    (padBits (TwoPhase.even (fun _ : Fin (2*bound P input n) => false)))
  have hp := machine_packet P input n hh (fun _ => false)
  change _ ∧ _=BinaryStack.cells ((initializedTree P input n).read
    (padBits (TwoPhase.even (fun _ : Fin (2*bound P input n) => false)))).output 0 at hp
  rw [hr.2] at hp
  have hf : padBits (fun _ : Fin (2*bound P input n) => false)=(fun _ => false) := by
    funext j
    simp [padBits]
  rw [hf] at hp
  exact hp
end Compile
end RegisterBits

def freeze (M : Machine) : Machine where
  states := M.states
  start := M.start
  transition s cells _ := M.transition s cells false

def freezeConfig (M : Machine) (c : Configuration M) : Configuration (freeze M) :=
  ⟨c.control,c.head,c.tape⟩
 theorem freeze_deterministic (M : Machine) : Deterministic (freeze M) := by
  intro s cells
  rfl
 theorem freeze_step (M : Machine) (c : Configuration M) (b : Bool) :
    step (freeze M) (freezeConfig M c) b=freezeConfig M (step M c false) := by
  cases c with
  | mk control head tape =>
    cases control with
    | none => rfl
    | some s =>
      simp only [step,freezeConfig,freeze]
      cases M.transition s (fun k => tape k (head k)) false <;> rfl
 theorem freeze_run (M : Machine) (input : List Bool) (n : ℕ) :
    run (freeze M) input (fun _ => false) n=freezeConfig M (run M input (fun _ => false) n) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [run,ih,freeze_step]
 theorem freeze_correct (G : Game) (M : Machine) (c : Configuration M) (hc : CorrectOutput G c) :
    CorrectOutput G (freezeConfig M c) := hc

namespace DetRealizer
open RegisterBits BinaryData TreeDevice TreeDevice.Certified
noncomputable def machine : Machine := freeze (Compile.machine program)
 theorem machine_deterministic : Deterministic machine := freeze_deterministic _
 theorem correct (G : Game) : CorrectOutput G (run machine (input G) (fun _ => false) (total ⟨input G⟩)) := by
  have he := runs ⟨input G⟩ (fun _ => false)
  have hp := Compile.deterministic_packet program program_quiet (input G) (limit ⟨input G⟩)
    (DetPreparation.value ⟨input G⟩) (by rw [he]) (by rw [he])
  have ho : BinaryInput.CorrectList G (DetPreparation.value ⟨input G⟩) := by
    rw [DetPreparation.value_game,BinaryInput.correctList_ofFn]
    exact Label.mainLabels_correct G
  have hc := correctList_packet G (Compile.machine program) _ _ ho hp.1 hp.2
  rw [machine,freeze_run]
  exact freeze_correct G _ _ hc
end DetRealizer

 theorem deterministic_main : DeterministicMainClaim := by
  obtain ⟨C,hC,hbound⟩ := DetRealizer.total_quasi
  exact ⟨DetRealizer.machine,DetRealizer.machine_deterministic,C,hC,fun G =>
    ⟨DetRealizer.total ⟨input G⟩,hbound ⟨input G⟩,DetRealizer.correct G⟩⟩
end MeanPayoff

theorem deterministic_quasipolynomial_mean_payoff : MeanPayoff.DeterministicMainClaim := MeanPayoff.deterministic_main

end OAI
