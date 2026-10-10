import OAI.Combinatorics.ContingencyTables.Machines.FiniteWordOutput
import OAI.Combinatorics.ContingencyTables.Machines.MatrixEncoding
import OAI.Combinatorics.ContingencyTables.Machines.FiniteFairBits

namespace OAI

/-! # Identifying public table probabilities with finite-word masses -/

namespace ContingencyTables.FiniteWordExecution
open MatchingFPRAS MatchingFPRAS.PhysicalStream Turing Algorithms
open ResidualMixture FirstSuccess
open scoped BigOperators Classical

variable {n : List MatchingFPRAS.Symbol → ℕ} {f : List MatchingFPRAS.Symbol×List Bool → List MatchingFPRAS.Symbol}

/-- Exact finite-word compilation preserves each table's probability,
including the quotient of the public output tape by trailing blanks. -/
theorem machine_tableMass (N : TreeTyped.Realizer n) (F : TreeTyped.Realizer f)
    (as : List MatchingFPRAS.Symbol) (ha : ∀ a∈as,a≠0)
    (hout : ∀ bs,∀ a∈f (as,bs),a≠6 ∧ a≠7)
    {m j L : ℕ} {r : Fin m → ℕ} {c : Fin j → ℕ}
    (hL : n as=L) (draw : Bits L → Table r c)
    (hf : ∀ bits,f (as,List.ofFn bits)=encodeMatrix (draw bits).val)
    (t : ℕ) (ht : machineTime N F as≤t) (X : Table r c) :
    tableMass (machine N F) as t X.val=
      ((mapLaw (uniformLaw (α := Bits L)) draw).mass X:ℝ) := by
  let g : Tape MatchingFPRAS.Symbol → ℚ := fun tape => if tape.right₀=ListBlank.mk (encodeMatrix X.val) then 1 else 0
  obtain ⟨hhalt,hm⟩ := machine_law N F as ha hout t ht
  have he := hm g
  rw [hL] at he
  have hl : average (fun bits : Bits t => g (run (machine N F) as bits).tape)=
      ((Finset.univ.filter (fun bits : Bits t => OutputsTable (machine N F) as bits X.val)).card:ℚ)/(2:ℚ)^t := by
    simp only [average,g,OutputsTable,hhalt,true_and,Finset.sum_boole]
  have hg (bits : Bits L) : g (Tape.mk₁ (f (as,List.ofFn bits)))=
      if draw bits=X then (1:ℚ) else 0 := by
    simp only [g,hf,Tape.mk₁,Tape.mk₂,Tape.mk'_right₀]
    have hi : ListBlank.mk (encodeMatrix (draw bits).val)=ListBlank.mk (encodeMatrix X.val) ↔
        draw bits=X := by
      constructor
      · intro h
        exact Subtype.ext (blankMatrix_injective _ _ h)
      · rintro h
        rw [h]
    rw [hi]
  have hr : average (fun bits : Bits L => g (Tape.mk₁ (f (as,List.ofFn bits))))=
      (mapLaw (uniformLaw (α := Bits L)) draw).mass X := by
    simp_rw [hg]
    simp only [average,mapLaw,uniformLaw,uniformMass,Fintype.card_fun,Fintype.card_bool,
      Fintype.card_fin,Finset.sum_div]
    apply Finset.sum_congr rfl
    intro bits _
    split_ifs <;> simp
  rw [hl,hr] at he
  have heR := congrArg (fun z : ℚ => (z:ℝ)) he
  simpa only [Rat.cast_div,Rat.cast_natCast,Rat.cast_pow,Rat.cast_ofNat,tableMass] using heR

end ContingencyTables.FiniteWordExecution

end OAI
