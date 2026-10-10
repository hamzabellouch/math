import Mathlib
import OAI.Computability.VertexCover.Machines.ListNat
import OAI.Computability.VertexCover.Machines.ParseClause

namespace OAI

section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
                              
section

namespace VertexCover.Machine.FormulaParser
open UniqueGames.BinaryFormula UniqueGames.BinaryEncoding

theorem frame_sound (input digits rest : List Bool) (h : parseFrame input=some (digits,rest)) :
    input=UniqueGames.BinaryEncoding.frame digits++rest := by
  induction input using List.twoStepInduction generalizing digits rest with
  | nil => simp [parseFrame] at h
  | singleton b =>
    cases b with
    | true => simp [parseFrame] at h
    | false =>
      simp only [parseFrame,Option.some.injEq,Prod.mk.injEq] at h
      rcases h with ⟨rfl,rfl⟩
      rfl
  | cons_cons a b bs ih _ =>
    cases a with
    | false =>
      simp only [parseFrame,Option.some.injEq,Prod.mk.injEq] at h
      rcases h with ⟨rfl,rfl⟩
      rfl
    | true =>
      cases hp : parseFrame bs with
      | none => simp [parseFrame,hp] at h
      | some p =>
        rcases p with ⟨ds,rs⟩
        simp only [parseFrame,hp,Option.bind_eq_bind,Option.pure_def,Option.bind_some,Option.some.injEq,Prod.mk.injEq] at h
        rcases h with ⟨rfl,rfl⟩
        rw [ih ds rs hp]
        rfl

theorem name_sound (input : List Bool) (n : ℕ) (rest : List Bool)
    (h : parseName input=some (n,rest)) : input=nameBits n++rest := by
  cases hp : parseFrame input with
  | none => simp [parseName,hp] at h
  | some p =>
    rcases p with ⟨digits,rs⟩
    simp only [parseName,hp,Option.bind_eq_bind,Option.bind_some] at h
    split at h
    · rename_i hc
      have he := Option.some.inj h
      cases he
      have hf := frame_sound input digits rest hp
      simpa only [nameBits,← hc] using hf
    · contradiction

theorem literal_sound (input : List Bool) (l : Literal) (rest : List Bool)
    (h : parseLiteral input=some (l,rest)) : input=literalBits l++rest := by
  cases input with
  | nil => simp [parseLiteral] at h
  | cons b bs =>
    cases hp : parseName bs with
    | none => simp [parseLiteral,hp] at h
    | some p =>
      rcases p with ⟨n,rs⟩
      simp only [parseLiteral,hp,Option.bind_eq_bind,Option.bind_some,Option.pure_def] at h
      have he := Option.some.inj h
      cases he
      have hn := name_sound bs n rest hp
      simpa only [literalBits,List.cons_append] using congrArg (List.cons b) hn

theorem clause_sound (input : List Bool) (clause : Clause) (rest : List Bool)
    (h : parseClause input=some (clause,rest)) : input=clauseBits clause++rest := by
  cases h₁ : parseLiteral input with
  | none => simp [parseClause,h₁] at h
  | some a =>
    rcases a with ⟨a,rs₁⟩
    cases h₂ : parseLiteral rs₁ with
    | none => simp [parseClause,h₁,h₂] at h
    | some b =>
      rcases b with ⟨b,rs₂⟩
      cases h₃ : parseLiteral rs₂ with
      | none => simp [parseClause,h₁,h₂,h₃] at h
      | some c =>
        rcases c with ⟨c,rs₃⟩
        simp only [parseClause,h₁,h₂,h₃,Option.bind_eq_bind,Option.bind_some,Option.pure_def] at h
        cases Option.some.inj h
        rw [literal_sound input a rs₁ h₁,literal_sound rs₁ b rs₂ h₂,literal_sound rs₂ c rest h₃]
        simp only [clauseBits,List.append_assoc]
        rfl

theorem clause_code_bound (clause : Clause) :
    2*(clauseCode clause).length+2 ≤ 16*(clauseBits clause).length := by
  simp only [clauseCode,literalCode,prodBits,pairBits_length,boolBits,List.length_nil,
    clauseBits,List.length_append,literalBits,List.length_cons,nameBits,UniqueGames.BinaryEncoding.frame_length]
  omega

noncomputable def rawLength : Poly id natBits List.length :=
  (Poly.rawToList.comp (Poly.listLength boolBits false)).congr (fun _ => rfl)

end VertexCover.Machine.FormulaParser
end


end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
