import Mathlib
import OAI.Analysis.MatrixSigning.Machines.FixedLoop
import OAI.Analysis.MatrixSigning.Machines.FixedBranch
import OAI.Analysis.MatrixSigning.Machines.BinaryStackMoves
import OAI.Analysis.MatrixSigning.Machines.FixedCopyRestore
import OAI.Analysis.MatrixSigning.Machines.BinaryTrimMachine
import OAI.Analysis.MatrixSigning.Machines.BorrowActivity
import OAI.Analysis.MatrixSigning.Machines.FixedRun
import OAI.Analysis.MatrixSigning.Machines.MachineTransport

namespace OAI

section

namespace KS.W19.DivisionMachine
open KS.W01.FixedStack KS.W29.FixedSequential KS.W19.FixedRun

def trialPorts : Fin 3 ↪ Fin 10 := ⟨![4,6,9], by decide⟩
def divisorPorts : Fin 3 ↪ Fin 10 := ⟨![2,7,9], by decide⟩
def subtractPorts : Fin 3 ↪ Fin 10 := ⟨![6,7,8], by decide⟩
def trimPorts : Fin 3 ↪ Fin 10 := ⟨![0,4,8], by decide⟩

def copyTrial : Program 10 := KS.W01.FixedCopy.program trialPorts
def copyDivisor : Program 10 := KS.W01.FixedCopy.program divisorPorts
def subtract : Program 10 := ofMachine (lift3 BorrowSubtractor.machine subtractPorts)
def prepareTail : Program 10 := compose copyDivisor subtract
def prepare : Program 10 := compose copyTrial prepareTail

def keepTrial : Program 10 := KS.W04.BinaryStackMoves.clearProgram 8
def trimCandidate : Program 10 := ofMachine (lift3 BinaryTrimMachine.machine trimPorts)
def useCandidate : Program 10 := compose (KS.W04.BinaryStackMoves.clearProgram 4) trimCandidate

def select (heads : Fin 10 → Fin 3) (_coin : Bool) : KS.W29.FixedBranch.SelectInstruction 10 :=
  let borrowed := (heads 6).val == 2
  ⟨if borrowed then .left else .right,
    Vector.ofFn (fun j => if j = 6 then .pop else if j = 5 then .push (!borrowed) else .stay)⟩

def choose : Program 10 := KS.W29.FixedBranch.branch keepTrial useCandidate 5 select
def body : Program 10 := compose prepare choose

def guard (heads : Fin 10 → Fin 3) (_coin : Bool) : KS.W29.FixedLoop.GuardInstruction 10 :=
  if (heads 3).val = 0 then ⟨.halt, Vector.ofFn (fun _ => .stay)⟩
  else ⟨.call, Vector.ofFn (fun j => if j = 3 then .pop
    else if j = 4 then .push ((heads 3).val == 2) else .stay)⟩

def loop : Program 10 := KS.W29.FixedLoop.loop body guard

def «stacks» (d pending q r a b c scratch : List Bool) : Fin 10 → List Bool :=
  ![[],[],d,pending,r,q,a,b,c,scratch]

theorem copyTrial_run (d pending q r coins : List Bool) (hc : coins.length = 2 * r.length + 2) :
    copyTrial.toMachine.run ⟨some copyTrial.initial, «stacks» d pending q r [] [] [] []⟩ coins =
      ⟨none, «stacks» d pending q r r [] [] []⟩ := by
  have h := KS.W01.FixedCopy.run_copy_restore trialPorts («stacks» d pending q r [] [] [] []) r coins
    rfl rfl rfl hc
  refine (KS.W19.MachineTransport.run_ofMachine (KS.W01.FixedCopy.machine trialPorts) _ coins).trans ?_
  refine h.trans ?_
  apply config_ext
  · rfl
  · intro j
    fin_cases j <;> simp [Function.update, «stacks», trialPorts] <;> rfl

theorem copyTrial_halts (d pending q r coins : List Bool) (hc : coins.length = 2 * r.length + 2) :
    HaltsAfter copyTrial ⟨some copyTrial.initial, «stacks» d pending q r [] [] [] []⟩ coins :=
  KS.W01.FixedCopy.haltsAfter trialPorts _ r coins rfl rfl rfl hc

theorem copyDivisor_run (d pending q r coins : List Bool) (hc : coins.length = 2 * d.length + 2) :
    copyDivisor.toMachine.run ⟨some copyDivisor.initial, «stacks» d pending q r r [] [] []⟩ coins =
      ⟨none, «stacks» d pending q r r d [] []⟩ := by
  have h := KS.W01.FixedCopy.run_copy_restore divisorPorts («stacks» d pending q r r [] [] []) d coins
    rfl rfl rfl hc
  refine (KS.W19.MachineTransport.run_ofMachine (KS.W01.FixedCopy.machine divisorPorts) _ coins).trans ?_
  refine h.trans ?_
  apply config_ext
  · rfl
  · intro j
    fin_cases j <;> simp [Function.update, «stacks», divisorPorts] <;> rfl

theorem copyDivisor_halts (d pending q r coins : List Bool) (hc : coins.length = 2 * d.length + 2) :
    HaltsAfter copyDivisor ⟨some copyDivisor.initial, «stacks» d pending q r r [] [] []⟩ coins :=
  KS.W01.FixedCopy.haltsAfter divisorPorts _ d coins rfl rfl rfl hc

theorem subtract_start (d pending q r : List Bool) :
    (⟨some subtract.initial, «stacks» d pending q r r d [] []⟩ : Config 10 subtract.states) =
      pack subtractPorts (BorrowSubtractor.cfg (some 0) r d [])
        («stacks» d pending q r [] [] [] []) := by
  apply config_ext
  · rfl
  · intro j
    fin_cases j <;> rfl

theorem subtract_run (d pending q r coins : List Bool) (hc : coins.length = max r.length d.length + 1) :
    subtract.toMachine.run ⟨some subtract.initial, «stacks» d pending q r r d [] []⟩ coins =
      ⟨none, «stacks» d pending q r [subtractionBorrow r d false] [] (subtractBits r d false).reverse []⟩ := by
  erw [subtract_start]
  refine (KS.W19.MachineTransport.run_ofMachine (lift3 BorrowSubtractor.machine subtractPorts) _ coins).trans ?_
  refine (run_pack BorrowSubtractor.machine subtractPorts _ _ coins).trans ?_
  refine (congrArg (fun c => pack subtractPorts c («stacks» d pending q r [] [] [] []))
    (BorrowSubtractor.run_sub false r d [] coins hc)).trans ?_
  apply config_ext
  · rfl
  · intro j
    fin_cases j <;> simp only [List.append_nil] <;> rfl

theorem prepare_run (d pending q r first second third : List Bool)
    (h₁ : first.length = 2 * r.length + 2) (h₂ : second.length = 2 * d.length + 2)
    (h₃ : third.length = max r.length d.length + 1) :
    prepare.toMachine.run ⟨some prepare.initial, «stacks» d pending q r [] [] [] []⟩
      (first ++ (second ++ third)) =
      ⟨none, «stacks» d pending q r [subtractionBorrow r d false] [] (subtractBits r d false).reverse []⟩ := by
  change (compose copyTrial prepareTail).toMachine.run
    (liftLeft copyTrial prepareTail ⟨some copyTrial.initial, _⟩) _ = _
  erw [run_compose copyTrial prepareTail _ first _ (copyTrial_halts d pending q r first h₁),
    copyTrial_run d pending q r first h₁]
  change liftRight copyTrial prepareTail ((compose copyDivisor subtract).toMachine.run
    (liftLeft copyDivisor subtract ⟨some copyDivisor.initial, _⟩) _) = _
  erw [run_compose copyDivisor subtract _ second _ (copyDivisor_halts d pending q r second h₂),
    copyDivisor_run d pending q r second h₂, subtract_run d pending q r third h₃]
  rfl

theorem choose_step_borrowed (d pending q r candidate : List Bool) (coin : Bool) :
    choose.toMachine.step
      ⟨some choose.initial, «stacks» d pending q r [true] [] candidate []⟩ coin =
      KS.W29.FixedBranch.liftLeft keepTrial useCandidate
        ⟨some keepTrial.initial, «stacks» d pending (false :: q) r [] [] candidate []⟩ := by
  unfold choose
  erw [KS.W29.FixedBranch.step_start]
  apply config_ext
  · rfl
  · intro j
    fin_cases j <;> rfl

theorem choose_step_candidate (d pending q r candidate : List Bool) (coin : Bool) :
    choose.toMachine.step
      ⟨some choose.initial, «stacks» d pending q r [false] [] candidate []⟩ coin =
      KS.W29.FixedBranch.liftRight keepTrial useCandidate
        ⟨some useCandidate.initial, «stacks» d pending (true :: q) r [] [] candidate []⟩ := by
  unfold choose
  erw [KS.W29.FixedBranch.step_start]
  apply config_ext
  · rfl
  · intro j
    fin_cases j <;> rfl

theorem keepTrial_run (d pending q r candidate coins : List Bool)
    (hc : coins.length = candidate.length + 1) :
    keepTrial.toMachine.run ⟨some keepTrial.initial, «stacks» d pending q r [] [] candidate []⟩ coins =
      ⟨none, «stacks» d pending q r [] [] [] []⟩ := by
  have h := KS.W04.BinaryStackMoves.run_clear_stacks (8 : Fin 10)
    («stacks» d pending q r [] [] candidate []) coins hc
  refine (KS.W19.MachineTransport.run_ofMachine (KS.W04.BinaryStackMoves.clearMachine (8 : Fin 10)) _ coins).trans ?_
  refine h.trans ?_
  apply config_ext
  · rfl
  · intro j
    fin_cases j <;> rfl

theorem clearRemainder_run (d pending q r candidate coins : List Bool)
    (hc : coins.length = r.length + 1) :
    (KS.W04.BinaryStackMoves.clearProgram (4 : Fin 10)).toMachine.run
      ⟨some (0 : Fin 1), «stacks» d pending q r [] [] candidate []⟩ coins =
      ⟨none, «stacks» d pending q [] [] [] candidate []⟩ := by
  have h := KS.W04.BinaryStackMoves.run_clear_stacks (4 : Fin 10)
    («stacks» d pending q r [] [] candidate []) coins hc
  refine (KS.W19.MachineTransport.run_ofMachine (KS.W04.BinaryStackMoves.clearMachine (4 : Fin 10)) _ coins).trans ?_
  refine h.trans ?_
  apply config_ext
  · rfl
  · intro j
    fin_cases j <;> rfl

theorem trim_start (d pending q candidate : List Bool) :
    (⟨some trimCandidate.initial, «stacks» d pending q [] [] [] candidate []⟩ : Config 10 trimCandidate.states) =
      pack trimPorts (BinaryTrimMachine.cfg (some 0) [] [] candidate)
        («stacks» d pending q [] [] [] [] []) := by
  apply config_ext
  · rfl
  · intro j
    fin_cases j <;> rfl

theorem trim_run (d pending q candidate coins : List Bool)
    (hc : coins.length = candidate.length + 1) :
    trimCandidate.toMachine.run ⟨some trimCandidate.initial, «stacks» d pending q [] [] [] candidate []⟩ coins =
      ⟨none, «stacks» d pending q (trimBits candidate.reverse) [] [] [] []⟩ := by
  erw [trim_start]
  refine (KS.W19.MachineTransport.run_ofMachine (lift3 BinaryTrimMachine.machine trimPorts) _ coins).trans ?_
  refine (run_pack BinaryTrimMachine.machine trimPorts _ _ coins).trans ?_
  refine (congrArg (fun c => pack trimPorts c («stacks» d pending q [] [] [] [] []))
    (BinaryTrimMachine.run_trim [] [] candidate coins hc)).trans ?_
  apply config_ext
  · rfl
  · intro j
    fin_cases j <;> simp only [List.append_nil] <;> rfl

theorem useCandidate_run (d pending q r candidate first second : List Bool)
    (hf : first.length = r.length + 1) (hs : second.length = candidate.length + 1) :
    useCandidate.toMachine.run ⟨some useCandidate.initial, «stacks» d pending q r [] [] candidate []⟩
      (first ++ second) =
      ⟨none, «stacks» d pending q (trimBits candidate.reverse) [] [] [] []⟩ := by
  have hh := KS.W04.BinaryStackMoves.clear_haltsAfter_stacks (4 : Fin 10)
    («stacks» d pending q r [] [] candidate []) first hf
  change (compose (KS.W04.BinaryStackMoves.clearProgram (4 : Fin 10)) trimCandidate).toMachine.run
    (liftLeft _ _ ⟨some (0 : Fin 1), _⟩) _ = _
  erw [run_compose _ _ _ first second hh, clearRemainder_run d pending q r candidate first hf,
    trim_run d pending q candidate second hs]
  rfl

theorem choose_run_borrowed (d pending q r candidate coins : List Bool) (coin : Bool)
    (hc : coins.length = candidate.length + 1) :
    choose.toMachine.run ⟨some choose.initial, «stacks» d pending q r [true] [] candidate []⟩
      (coin :: coins) = ⟨none, «stacks» d pending (false :: q) r [] [] [] []⟩ := by
  erw [Machine.run, choose_step_borrowed]
  change (KS.W29.FixedBranch.branch keepTrial useCandidate 5 select).toMachine.run _ _ = _
  erw [KS.W29.FixedBranch.run_left, keepTrial_run d pending (false :: q) r candidate coins hc]
  rfl

theorem choose_run_candidate (d pending q r candidate first second : List Bool) (coin : Bool)
    (hf : first.length = r.length + 1) (hs : second.length = candidate.length + 1) :
    choose.toMachine.run ⟨some choose.initial, «stacks» d pending q r [false] [] candidate []⟩
      (coin :: (first ++ second)) =
      ⟨none, «stacks» d pending (true :: q) (trimBits candidate.reverse) [] [] [] []⟩ := by
  erw [Machine.run, choose_step_candidate]
  change (KS.W29.FixedBranch.branch keepTrial useCandidate 5 select).toMachine.run _ _ = _
  erw [KS.W29.FixedBranch.run_right,
    useCandidate_run d pending (true :: q) r candidate first second hf hs]
  rfl

theorem subtract_halts (d pending q r coins : List Bool) (hc : coins.length = max r.length d.length + 1) :
    HaltsAfter subtract ⟨some subtract.initial, «stacks» d pending q r r d [] []⟩ coins := by
  erw [subtract_start]
  apply (haltsAfter_lift3_iff BorrowSubtractor.machine subtractPorts _ coins).2
  erw [project_pack]
  exact BorrowSubtractor.haltsAfter_sub false r d [] coins hc

theorem prepare_halts (d pending q r first second third : List Bool)
    (h₁ : first.length = 2 * r.length + 2) (h₂ : second.length = 2 * d.length + 2)
    (h₃ : third.length = max r.length d.length + 1) :
    HaltsAfter prepare ⟨some prepare.initial, «stacks» d pending q r [] [] [] []⟩
      (first ++ (second ++ third)) := by
  apply compose_haltsAfter copyTrial prepareTail _ first (second ++ third)
    (copyTrial_halts d pending q r first h₁)
  erw [copyTrial_run d pending q r first h₁]
  apply compose_haltsAfter copyDivisor subtract _ second third
    (copyDivisor_halts d pending q r second h₂)
  erw [copyDivisor_run d pending q r second h₂]
  exact subtract_halts d pending q r third h₃

theorem body_run_borrowed (d pending q r first second third cleanup : List Bool) (coin : Bool)
    (hborrow : subtractionBorrow r d false = true)
    (h₁ : first.length = 2 * r.length + 2) (h₂ : second.length = 2 * d.length + 2)
    (h₃ : third.length = max r.length d.length + 1)
    (hc : cleanup.length = max r.length d.length + 1) :
    body.toMachine.run ⟨some body.initial, «stacks» d pending q r [] [] [] []⟩
      ((first ++ (second ++ third)) ++ (coin :: cleanup)) =
      ⟨none, «stacks» d pending (false :: q) r [] [] [] []⟩ := by
  change (compose prepare choose).toMachine.run (liftLeft prepare choose ⟨some prepare.initial, _⟩) _ = _
  erw [run_compose prepare choose _ _ _ (prepare_halts d pending q r first second third h₁ h₂ h₃),
    prepare_run d pending q r first second third h₁ h₂ h₃, hborrow]
  erw [choose_run_borrowed d pending q r (subtractBits r d false).reverse cleanup coin
    (by simpa only [List.length_reverse, subtractBits_length] using hc)]
  rfl

theorem body_run_candidate (d pending q r first second third clear trim : List Bool) (coin : Bool)
    (hborrow : subtractionBorrow r d false = false)
    (h₁ : first.length = 2 * r.length + 2) (h₂ : second.length = 2 * d.length + 2)
    (h₃ : third.length = max r.length d.length + 1)
    (hc : clear.length = r.length + 1) (ht : trim.length = max r.length d.length + 1) :
    body.toMachine.run ⟨some body.initial, «stacks» d pending q r [] [] [] []⟩
      ((first ++ (second ++ third)) ++ (coin :: (clear ++ trim))) =
      ⟨none, «stacks» d pending (true :: q) (trimBits (subtractBits r d false)) [] [] [] []⟩ := by
  change (compose prepare choose).toMachine.run (liftLeft prepare choose ⟨some prepare.initial, _⟩) _ = _
  erw [run_compose prepare choose _ _ _ (prepare_halts d pending q r first second third h₁ h₂ h₃),
    prepare_run d pending q r first second third h₁ h₂ h₃, hborrow]
  erw [choose_run_candidate d pending q r (subtractBits r d false).reverse clear trim coin hc
    (by simpa only [List.length_reverse, subtractBits_length] using ht)]
  simp only [List.reverse_reverse, liftRight]
  rfl

end KS.W19.DivisionMachine

end

end OAI
