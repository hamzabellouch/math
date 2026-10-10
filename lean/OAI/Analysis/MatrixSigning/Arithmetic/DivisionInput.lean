import Mathlib
import OAI.Analysis.MatrixSigning.Arithmetic.DivisionLoopRun
import OAI.Analysis.MatrixSigning.Encoding.FrameActivity

namespace OAI

section

namespace KS.W19.DivisionInput
open KS.W01.FixedStack KS.W29.FixedSequential KS.W19.FixedRun

def firstPorts : Fin 3 ↪ Fin 10 := ⟨![0,1,9], by decide⟩
def secondPorts : Fin 3 ↪ Fin 10 := ⟨![0,2,9], by decide⟩
def parseFirst : Program 10 := ofMachine (lift3 KS.W29.FrameDecoder.machine firstPorts)
def parseSecond : Program 10 := ofMachine (lift3 KS.W29.FrameDecoder.machine secondPorts)
def reverseInput : Program 10 := KS.W04.BinaryStackMoves.moveProgram 1 3

def loopStage : Program 10 := compose reverseInput DivisionMachine.loop
def secondStage : Program 10 := compose parseSecond loopStage
def program : Program 10 := compose parseFirst secondStage
def machine : Machine := program.toMachine

def «stacks» (input xs d pending : List Bool) : Fin 10 → List Bool :=
  ![input,xs,d,pending,[],[],[],[],[],[]]

theorem first_init (xs d : List Bool) :
    parseFirst.toMachine.init (KS.W01.frame xs ++ KS.W01.frame d) =
      pack firstPorts (KS.W29.FrameDecoder.machine.init (KS.W01.frame xs ++ KS.W01.frame d))
        (fun _ => []) := by
  apply config_ext
  · rfl
  · intro j
    fin_cases j <;> rfl

theorem first_run (xs d coins : List Bool) (hc : coins.length = 3 * xs.length + 2) :
    parseFirst.toMachine.run (parseFirst.toMachine.init (KS.W01.frame xs ++ KS.W01.frame d)) coins =
      ⟨none, «stacks» (KS.W01.frame d) xs [] []⟩ := by
  erw [first_init]
  refine (KS.W19.MachineTransport.run_ofMachine (lift3 KS.W29.FrameDecoder.machine firstPorts) _ coins).trans ?_
  refine (run_pack KS.W29.FrameDecoder.machine firstPorts _ _ coins).trans ?_
  refine (congrArg (fun c => pack firstPorts c (fun _ => []))
    (KS.W29.FrameDecoder.run_frame xs (KS.W01.frame d) coins hc)).trans ?_
  apply config_ext
  · rfl
  · intro j
    fin_cases j <;> rfl

theorem first_halts (xs d coins : List Bool) (hc : coins.length = 3 * xs.length + 2) :
    HaltsAfter parseFirst (parseFirst.toMachine.init (KS.W01.frame xs ++ KS.W01.frame d)) coins := by
  erw [first_init]
  apply (haltsAfter_lift3_iff _ firstPorts _ coins).2
  erw [project_pack]
  exact FrameActivity.haltsAfter_frame xs (KS.W01.frame d) coins hc

theorem second_start (xs d : List Bool) :
    (⟨some parseSecond.initial, «stacks» (KS.W01.frame d) xs [] []⟩ : Config 10 parseSecond.states) =
      pack secondPorts (KS.W29.FrameDecoder.machine.init (KS.W01.frame d ++ []))
        («stacks» [] xs [] []) := by
  apply config_ext
  · rfl
  · intro j
    fin_cases j <;> simp [pack, «stacks», secondPorts, KS.W29.BinaryMachine.init]

theorem second_run (xs d coins : List Bool) (hc : coins.length = 3 * d.length + 2) :
    parseSecond.toMachine.run ⟨some parseSecond.initial, «stacks» (KS.W01.frame d) xs [] []⟩ coins =
      ⟨none, «stacks» [] xs d []⟩ := by
  erw [second_start]
  refine (KS.W19.MachineTransport.run_ofMachine (lift3 KS.W29.FrameDecoder.machine secondPorts) _ coins).trans ?_
  refine (run_pack KS.W29.FrameDecoder.machine secondPorts _ _ coins).trans ?_
  refine (congrArg (fun c => pack secondPorts c («stacks» [] xs [] []))
    (KS.W29.FrameDecoder.run_frame d [] coins hc)).trans ?_
  apply config_ext
  · rfl
  · intro j
    fin_cases j <;> rfl

theorem second_halts (xs d coins : List Bool) (hc : coins.length = 3 * d.length + 2) :
    HaltsAfter parseSecond ⟨some parseSecond.initial, «stacks» (KS.W01.frame d) xs [] []⟩ coins := by
  erw [second_start]
  apply (haltsAfter_lift3_iff _ secondPorts _ coins).2
  erw [project_pack]
  exact FrameActivity.haltsAfter_frame d [] coins hc

theorem reverse_run (xs d coins : List Bool) (hc : coins.length = xs.length + 1) :
    reverseInput.toMachine.run ⟨some reverseInput.initial, «stacks» [] xs d []⟩ coins =
      ⟨none, DivisionMachine.«stacks» d xs.reverse [] [] [] [] [] []⟩ := by
  have h := KS.W04.BinaryStackMoves.run_move_stacks (1 : Fin 10) 3 (by decide)
    («stacks» [] xs d []) coins hc
  refine (KS.W19.MachineTransport.run_ofMachine
    (KS.W04.BinaryStackMoves.moveMachine (1 : Fin 10) 3) _ coins).trans ?_
  refine h.trans ?_
  apply config_ext
  · rfl
  · intro j
    fin_cases j <;> simp [KS.W04.BinaryStackMoves.twoConfig, «stacks»,
      DivisionMachine.«stacks»]

theorem reverse_halts (xs d coins : List Bool) (hc : coins.length = xs.length + 1) :
    HaltsAfter reverseInput ⟨some reverseInput.initial, «stacks» [] xs d []⟩ coins :=
  KS.W04.BinaryStackMoves.move_haltsAfter_stacks (1 : Fin 10) 3 (by decide) _ coins hc

theorem run_input (xs d first second rev work : List Bool)
    (hf : first.length = 3 * xs.length + 2) (hs : second.length = 3 * d.length + 2)
    (hr : rev.length = xs.length + 1)
    (hw : xs.length * (8 * (xs.length + 2 * d.length + 2) + 1) + 1 ≤ work.length) :
    machine.run (machine.init (KS.W01.frame xs ++ KS.W01.frame d))
      (first ++ (second ++ (rev ++ work))) =
      ⟨none, DivisionMachine.«stacks» d [] (DivisionLoop.process d xs.reverse [] []).1
        (DivisionLoop.process d xs.reverse [] []).2 [] [] [] []⟩ := by
  have hi : machine.init (KS.W01.frame xs ++ KS.W01.frame d) =
      liftLeft parseFirst secondStage (parseFirst.toMachine.init (KS.W01.frame xs ++ KS.W01.frame d)) := by
    apply config_ext
    · rfl
    · intro j
      rfl
  erw [hi]
  change (compose parseFirst secondStage).toMachine.run _ _ = _
  erw [run_compose parseFirst secondStage _ first _ (first_halts xs d first hf), first_run xs d first hf]
  change liftRight parseFirst secondStage ((compose parseSecond loopStage).toMachine.run
    (liftLeft parseSecond loopStage ⟨some parseSecond.initial, _⟩) _) = _
  erw [run_compose parseSecond loopStage _ second _ (second_halts xs d second hs), second_run xs d second hs]
  change liftRight parseFirst secondStage (liftRight parseSecond loopStage
    ((compose reverseInput DivisionMachine.loop).toMachine.run
      (liftLeft reverseInput DivisionMachine.loop ⟨some reverseInput.initial, _⟩) _)) = _
  erw [run_compose reverseInput DivisionMachine.loop _ rev _ (reverse_halts xs d rev hr),
    reverse_run xs d rev hr, DivisionMachine.loop_payload d xs work hw]
  rfl

def inputFuel (xs d : List Bool) : Nat :=
  (3 * xs.length + 2) + ((3 * d.length + 2) + ((xs.length + 1) +
    (xs.length * (8 * (xs.length + 2 * d.length + 2) + 1) + 1)))

theorem run_input_tape (xs d bits : List Bool) (hb : bits.length = inputFuel xs d) :
    machine.run (machine.init (KS.W01.frame xs ++ KS.W01.frame d)) bits =
      ⟨none, DivisionMachine.«stacks» d [] (DivisionLoop.process d xs.reverse [] []).1
        (DivisionLoop.process d xs.reverse [] []).2 [] [] [] []⟩ := by
  unfold inputFuel at hb
  obtain ⟨first, rest, rfl, hf, ht⟩ := DivisionMachine.split_exact bits (3 * xs.length + 2) _ hb
  obtain ⟨second, rest, rfl, hs, ht⟩ := DivisionMachine.split_exact rest (3 * d.length + 2) _ ht
  obtain ⟨rev, work, rfl, hr, hw⟩ := DivisionMachine.split_exact rest (xs.length + 1) _ ht
  exact run_input xs d first second rev work hf hs hr hw.ge

theorem inputFuel_quadratic (xs d : List Bool) :
    inputFuel xs d ≤ KS.W29.polynomialFuel 16 2 (KS.W01.frame xs ++ KS.W01.frame d).length := by
  simp only [inputFuel, KS.W29.polynomialFuel, List.length_append, KS.W01.length_frame]
  nlinarith [Nat.zero_le (xs.length * d.length), Nat.zero_le (xs.length ^ 2), Nat.zero_le (d.length ^ 2)]

theorem run_input_polynomial (xs d bits : List Bool)
    (hb : bits.length = KS.W29.polynomialFuel 16 2 (KS.W01.frame xs ++ KS.W01.frame d).length) :
    machine.run (machine.init (KS.W01.frame xs ++ KS.W01.frame d)) bits =
      ⟨none, DivisionMachine.«stacks» d [] (DivisionLoop.process d xs.reverse [] []).1
        (DivisionLoop.process d xs.reverse [] []).2 [] [] [] []⟩ := by
  have ht : inputFuel xs d ≤ bits.length := by rw [hb]; exact inputFuel_quadratic xs d
  have hh := run_input_tape xs d (bits.take (inputFuel xs d))
    (by simp [List.length_take, Nat.min_eq_left ht])
  conv_lhs => rw [← List.take_append_drop (inputFuel xs d) bits]
  erw [Machine.run_append, hh]
  exact machine.run_halted _ rfl _

theorem run_naturals (n d : Nat) (hd : 0 < d) (bits : List Bool)
    (hb : bits.length = KS.W29.polynomialFuel 16 2 (KS.W01.encodeNat n ++ KS.W01.encodeNat d).length) :
    let result := machine.run (machine.init (KS.W01.encodeNat n ++ KS.W01.encodeNat d)) bits
    result.state = none ∧ result.«stacks» (2 : Fin 10) = Computability.encodeNat d ∧
      n = d * bitsValue (result.«stacks» (5 : Fin 10)) + bitsValue (result.«stacks» (4 : Fin 10)) ∧
      bitsValue (result.«stacks» (4 : Fin 10)) < d := by
  dsimp only
  simp only [KS.W01.encodeNat] at hb ⊢
  erw [run_input_polynomial (Computability.encodeNat n) (Computability.encodeNat d) bits hb]
  have h := DivisionLoop.process_payload_correct (Computability.encodeNat d) (Computability.encodeNat n)
    (by simpa only [bitsValue_encodeNat] using hd)
  simp only [bitsValue_encodeNat] at h
  exact ⟨rfl, rfl, h.1, h.2⟩

theorem haltsWithin_polynomial (n d : Nat) :
    machine.HaltsWithin (KS.W01.encodeNat n ++ KS.W01.encodeNat d)
      (KS.W29.polynomialFuel 16 2 (KS.W01.encodeNat n ++ KS.W01.encodeNat d).length) := by
  intro seed
  change (machine.run (machine.init _) (List.ofFn seed)).state = none
  simp only [KS.W01.encodeNat]
  erw [run_input_polynomial (Computability.encodeNat n) (Computability.encodeNat d) _ (List.length_ofFn)]

end KS.W19.DivisionInput

end

end OAI
