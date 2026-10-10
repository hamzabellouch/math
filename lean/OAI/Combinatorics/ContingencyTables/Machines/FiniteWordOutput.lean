import OAI.Combinatorics.ContingencyTables.Machines.FiniteWordMachine

namespace OAI

/-! # Every-path output properties of the finite-word machine -/

namespace ContingencyTables.FiniteWordExecution
open MatchingFPRAS MatchingFPRAS.PhysicalStream Turing
open scoped BigOperators Classical

variable {n : List Symbol → ℕ} {f : List Symbol×List Bool → List Symbol}

/-- A property verified for every finite source word holds on every actual
machine tape once the fixed execution bound has elapsed. -/
theorem machine_all (N : TreeTyped.Realizer n) (F : TreeTyped.Realizer f)
    (as : List Symbol) (ha : ∀ a∈as,a≠0)
    (hout : ∀ bs,∀ a∈f (as,bs),a≠6 ∧ a≠7)
    (P : Tape Symbol → Prop)
    (hf : ∀ bits : Bits (n as),P (Tape.mk₁ (f (as,List.ofFn bits))))
    (t : ℕ) (ht : machineTime N F as≤t) :
    ∀ bits : Bits t,P (run (machine N F) as bits).tape := by
  let g : Tape Symbol → ℚ := fun tape => if P tape then 0 else 1
  have hm := (machine_law N F as ha hout t ht).2 g
  have hz : average (fun bits : Bits t => g (run (machine N F) as bits).tape)=0 := by
    rw [hm]
    have he : (fun bits : Bits (n as) => g (Tape.mk₁ (f (as,List.ofFn bits))))=
        (fun _ => (0:ℚ)) := by
      funext bits
      exact ite_eq_left (hf bits)
    rw [he,average_const]
  have hpow : (2:ℚ)^t≠0 := pow_ne_zero _ (by norm_num)
  have hs : ∑ bits : Bits t,g (run (machine N F) as bits).tape=0 := by
    have h := congrArg (fun a : ℚ => a*(2:ℚ)^t) hz
    simpa only [average,div_mul_cancel₀ _ hpow,zero_mul] using h
  have hnonneg (bits : Bits t) : 0≤g (run (machine N F) as bits).tape := by
    dsimp only [g]
    split_ifs <;> norm_num
  intro bits
  have hb := (Finset.sum_eq_zero_iff_of_nonneg (fun b _ => hnonneg b)).mp hs bits (Finset.mem_univ bits)
  by_contra hn
  have hbad : (1:ℚ)=0 := by simpa only [g,ite_eq_right hn] using hb
  norm_num at hbad

end ContingencyTables.FiniteWordExecution

end OAI
