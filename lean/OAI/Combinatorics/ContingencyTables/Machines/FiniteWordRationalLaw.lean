import OAI.Combinatorics.ContingencyTables.Machines.FiniteWordOutput

namespace OAI

/-! # Transferring rational-output events to the fixed public machine -/

namespace ContingencyTables.FiniteWordExecution
open MatchingFPRAS MatchingFPRAS.PhysicalStream Turing
open scoped BigOperators Classical
noncomputable section
variable {n : List Symbol → ℕ} {f : List Symbol×List Bool → List Symbol}

/-- An event verified on the rational value survives literal output and
finite-word compilation, without requiring a decoding oracle. -/
theorem machine_rational_event (N : TreeTyped.Realizer n) (F : TreeTyped.Realizer f)
    (as : List Symbol) (ha : ∀ a∈as,a≠0)
    (hout : ∀ bs,∀ a∈f (as,bs),a≠6 ∧ a≠7)
    (draw : Bits (n as) → ℚ) (hf : ∀ bits,f (as,List.ofFn bits)=encodeRat (draw bits))
    (P : ℚ → Prop) (t : ℕ) (ht : machineTime N F as≤t) :
    average (fun bits : Bits (n as) => if P (draw bits) then 1 else 0) ≤
      ((Finset.univ.filter (fun bits : Bits t =>
        ∃ q : ℚ,Outputs (machine N F) as bits q ∧ P q)).card:ℚ)/(2:ℚ)^t := by
  let g : Tape Symbol → ℚ := fun tape =>
    if ∃ q : ℚ,tape.right₀=ListBlank.mk (encodeRat q) ∧ P q then 1 else 0
  obtain ⟨hh,hm⟩ := machine_law N F as ha hout t ht
  have hsource : average (fun bits : Bits (n as) => if P (draw bits) then 1 else 0) ≤
      average (fun bits : Bits (n as) => g (Tape.mk₁ (f (as,List.ofFn bits)))) := by
    unfold average
    apply div_le_div_of_nonneg_right _ (by positivity)
    apply Finset.sum_le_sum
    intro bits _
    by_cases hp : P (draw bits)
    · have hg : ∃ q : ℚ,(Tape.mk₁ (f (as,List.ofFn bits))).right₀=
          ListBlank.mk (encodeRat q) ∧ P q := by
        refine ⟨draw bits,?_,hp⟩
        simp only [hf,Tape.mk₁,Tape.mk₂,Tape.mk'_right₀]
      simp only [hp,ite_true,g,hg]
      exact le_rfl
    · simp only [hp,ite_false]
      dsimp only [g]
      split_ifs <;> norm_num
  rw [←hm g] at hsource
  simpa only [average,g,Outputs,hh,true_and,Finset.sum_boole] using hsource

/-- All finite source words have a rational output satisfying P, so the
compiled machine has that property on every random tape. -/
theorem machine_rational_all (N : TreeTyped.Realizer n) (F : TreeTyped.Realizer f)
    (as : List Symbol) (ha : ∀ a∈as,a≠0)
    (hout : ∀ bs,∀ a∈f (as,bs),a≠6 ∧ a≠7)
    (draw : Bits (n as) → ℚ) (hf : ∀ bits,f (as,List.ofFn bits)=encodeRat (draw bits))
    (P : ℚ → Prop) (hP : ∀ bits,P (draw bits))
    (t : ℕ) (ht : machineTime N F as≤t) :
    ∀ bits : Bits t,∃ q : ℚ,Outputs (machine N F) as bits q ∧ P q := by
  have hp := machine_all N F as ha hout (fun tape =>
    ∃ q : ℚ,tape.right₀=ListBlank.mk (encodeRat q) ∧ P q) (fun bits => by
      refine ⟨draw bits,?_,hP bits⟩
      simp only [hf,Tape.mk₁,Tape.mk₂,Tape.mk'_right₀]) t ht
  have hh := (machine_law N F as ha hout t ht).1
  intro bits
  obtain ⟨q,hq,hPq⟩ := hp bits
  exact ⟨q,⟨hh bits,hq⟩,hPq⟩

end
end ContingencyTables.FiniteWordExecution

end OAI
