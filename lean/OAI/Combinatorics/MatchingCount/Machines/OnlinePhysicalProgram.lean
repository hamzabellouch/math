import Mathlib
import OAI.Combinatorics.MatchingCount.Machines.TreePostRealization
import OAI.Combinatorics.MatchingCount.Machines.PhysicalProgram
import OAI.Combinatorics.MatchingCount.Machines.OnlineTree

namespace OAI

namespace MatchingFPRAS.OnlineTree
open Turing TreeTyped TreeData TreeFunction TreeMachine TreePost PhysicalPost PhysicalStream

lemma input_height {A : Type} [Codec A] (a : A) : OnlineStack.height (inputStacks a)=weight a := by
  apply le_antisymm
  · exact Finset.sup_le (fun k _=>inputStacks_bound a k)
  · have h:=OnlineStack.height_bound (inputStacks a) (Sum.inl (0 : Reg))
    simpa only [inputStacks,encodeEnv,env,ite_true,weight,TreeFunction.size] using h

lemma cfg_packed {A : Type} [Codec A] (P : OnlineProc.Proc (K Reg)) (a : A) (l : Option P.Label) :
    upCfg (OnlineStack.cfg (⟨l,none,inputStacks a⟩ : StoreCfg P))=
      ⟨l.map (fun u=>(Sum.inl (TM1to1.Λ'.normal (TM2to1.Λ'.normal u)),none)),Tape.mk₁ (packed a)⟩ := by
  simp only [upCfg,OnlineStack.cfg,OnlineStack.stackCfg,input_height,CoinTM1.trCfg,
    TM1to1.trCfg,TM1to1.trTape,TM1to1.trTape',Tape.mk₁,Tape.mk₂,Tape.mk'_left,Tape.mk'_right₀,
    ListBlank.flatMap_mk,List.flatMap_nil,Option.map_map]
  rw [Tape.map_mk']
  rfl

noncomputable def physicalProgram {A B : Type} [Codec A] [Codec B]
    {f : A→Experiment B} (F : Realizer f) : Program where
  State := OnlineStack.Q (K Reg) (fun _=>Bool) F.program.Label RegisterProc.Store
  table := liftBool (OnlineStack.table F.program.code F.program.coin)
  states := OnlineStack.states F.program.code
  supported := liftBool_supported _ _ (OnlineStack.table_supported F.program.code F.program.coin)
  entry := OnlineStack.initialState
  entry_mem := OnlineStack.initialState_mem F.program.code

noncomputable def physicalCost {A B : Type} [Codec A] [Codec B]
    {f : A→Experiment B} (F : Realizer f) (a : A) : ℕ :=
  F.cost a*OnlineStack.Executes.factor F.program.code (weight a) (F.cost a)

lemma physical_realizes {A B : Type} [Codec A] [Codec B]
    {f : A→Experiment B} (F : Realizer f) (a : A) :
    (physicalProgram F).Realizes (Tape.mk₁ (packed a))
      ((f a).map (fun b=>Tape.mk₁ (packed b))) (physicalCost F a) := by
  obtain ⟨p,hp,hm,hc⟩:=F.correct a .nil
  obtain ⟨q,hq,hqm,hqc⟩:=hp.compile (weight a) (inputStacks_bound a)
  have he:=hq.up
  have hi : upCfg (OnlineStack.cfg (initial F.program (encode a) .nil))=
      (physicalProgram F).initial (Tape.mk₁ (packed a)) := cfg_packed F.program a (some default)
  have ho (b : B) : upCfg (OnlineStack.cfg (final F.program (encode b) .nil))=
      (physicalProgram F).final (Tape.mk₁ (packed b)) := cfg_packed F.program b none
  rw [hi] at he
  simp_rw [ho] at he
  refine ⟨q.map (fun b=>Tape.mk₁ (packed b)),?_,?_,?_⟩
  · exact he.map_all _ _ (Experiment.all_true _ |>.mono (fun _ _=>rfl))
  · intro w
    rw [Experiment.mean_map,hqm,hm,Experiment.mean_map]
  · rw [Experiment.cost_map]
    exact hqc.trans (Nat.mul_le_mul hc (OnlineStack.Executes.factor_mono _ _ _ _ le_rfl hc))
end MatchingFPRAS.OnlineTree

end OAI
