import OAI.Computability.Scheduling.MachineBridge

namespace OAI

section
namespace ThreeMachine.StackCompiler

theorem enc_request {n : ℕ} (x : Request n) :
    enc x = enc (ThreeMachine.encodeInput x.graph x.deadline) := rfl

theorem requestAnswer_time_charge {n : ℕ} (x : Request n) :
    Uniform.requestAnswer.time n x =
      Uniform.requestAnswer.charge (enc (ThreeMachine.encodeInput x.graph x.deadline)) := by
  unfold Uniform.time
  exact congrArg Uniform.requestAnswer.charge (enc_request x)

theorem Uniform.exists_requestMachine
    (R : Uniform (fun n (x : Request n) => Algorithm.output x.graph x.deadline)) :
    ∃ k q g, ∃ M : Machine k q g, ∀ n (x : Request n),
      M.Produces (ThreeMachine.encodeInput x.graph x.deadline)
        (Algorithm.output x.graph x.deadline)
        (2000*(R.time n x+(ThreeMachine.encodeInput x.graph x.deadline).length+
          (Algorithm.output x.graph x.deadline).length+1)) := by
  obtain ⟨k,q,g,M,hM⟩ := R.routine.exists_rawMachine
  refine ⟨k,q,g,M,?_⟩
  intro n x
  have hc := R.correct n x
  rw [enc_request] at hc
  have hr := hM (ThreeMachine.encodeInput x.graph x.deadline)
    (Algorithm.output x.graph x.deadline) hc
  simpa only [Uniform.time,enc_request] using hr

def requestRawBound (x : RequestData.Index) : ℕ :=
  2000*(Uniform.requestAnswer.time x.1 x.2+(RequestData.bits x).length+
    (Algorithm.output x.2.graph x.2.deadline).length+1)

theorem requestRawBound_poly : Poly RequestData.size requestRawBound 150011 := by
  have ht := Costs.requestAnswer
  have hb := RequestData.bitsPoly
  have ho := Costs.requestOutputLength
  unfold requestRawBound
  poly_auto

abbrev SmallDeadline := {x : RequestData.Index // x.2.deadline.getD 0 ≤ x.1}

theorem requestRawBound_length : Poly (fun x : SmallDeadline => (RequestData.bits x.1).length)
    (fun x => requestRawBound x.1) 150020 := by
  let s (x : SmallDeadline) := (RequestData.bits x.1).length
  have hsize : Poly s (fun x => RequestData.size x.1) 1 := by
    apply Poly.of_le (fun x : SmallDeadline => requestSize_le x.1.2 x.2)
    exact (Poly.const s 4).mul (Poly.size s)
  have h := Poly.reparam (r := 1) requestRawBound_poly (Subtype.val : SmallDeadline → RequestData.Index) hsize
  exact h.lift (by omega)

end ThreeMachine.StackCompiler
namespace ThreeMachine
open StackCompiler

theorem main_theorem : ReleaseTheorem := by
  obtain ⟨k,q,g,M,hM⟩ := Uniform.exists_requestMachine Uniform.requestAnswer
  obtain ⟨C,hC⟩ := requestRawBound_length
  refine ⟨k,q,g,M,C+1,by omega,?_⟩
  intro n G hn hG deadline hd
  let x : Request n := ⟨G,deadline⟩
  have hsmall : deadline.getD 0 ≤ n := by
    cases deadline with
    | none => simp only [Option.getD_none]; omega
    | some T => exact (hd T (by simp)).2
  let y : SmallDeadline := ⟨⟨n,x⟩,hsmall⟩
  refine ⟨Algorithm.output G deadline,Algorithm.output_correct G hn hG deadline,?_⟩
  have hr := hM n x
  have hb : 2000*(Uniform.requestAnswer.time n x+
      (encodeInput G deadline).length+(Algorithm.output G deadline).length+1) ≤
        (C+1)*((encodeInput G deadline).length+2)^150020 := by
    calc
      _ = requestRawBound y.1 := rfl
      _ ≤ C*((encodeInput G deadline).length+2)^150020 := by
        have hy := hC y
        dsimp only [RequestData.bits,y,x] at hy
        exact hy
      _ ≤ (C+1)*((encodeInput G deadline).length+2)^150020 :=
        Nat.mul_le_mul_right _ (Nat.le_succ C)
  obtain ⟨t,ht,halt,out⟩ := hr
  exact ⟨t,ht.trans hb,halt,out⟩

end ThreeMachine

end

end OAI
