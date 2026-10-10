import Mathlib
import OAI.Combinatorics.MatchingCount.Tapes.FixedAlphabetCompiler

namespace OAI

namespace MatchingFPRAS.FixedEncoding
variable (Γ : Type*) [Fintype Γ] [Inhabited Γ]
noncomputable def enc (a : Γ) : List.Vector Bool (Fintype.card Γ) := by
  classical
  exact List.Vector.ofFn (fun i=>decide (a≠default ∧ Fintype.equivFin Γ a=i))
lemma blank : enc Γ default=List.Vector.replicate (Fintype.card Γ) false := by
  classical
  apply List.Vector.ext
  intro i
  simp [enc]
lemma injective : Function.Injective (enc Γ) := by
  classical
  intro a b hab
  by_cases ha : a=default
  · by_cases hb : b=default
    · exact ha.trans hb.symm
    · have hh:=congrArg (fun v : List.Vector Bool (Fintype.card Γ)=>v.get (Fintype.equivFin Γ b)) hab
      simp [enc,ha,hb] at hh
  · have hh:=congrArg (fun v : List.Vector Bool (Fintype.card Γ)=>v.get (Fintype.equivFin Γ a)) hab
    simp only [enc,List.Vector.get_ofFn] at hh
    have ht : decide (b≠default ∧ Fintype.equivFin Γ b=Fintype.equivFin Γ a)=true := by
      simpa [ha] using hh.symm
    exact ((Fintype.equivFin Γ).injective (of_decide_eq_true ht).2).symm
noncomputable def dec : List.Vector Bool (Fintype.card Γ) → Γ := Function.invFun (enc Γ)
lemma left_inverse (a : Γ) : dec Γ (enc Γ a)=a :=
  Function.leftInverse_invFun (injective Γ) a
lemma bitsWord_length {Γ : Type*} {w : ℕ} (e : Γ → List.Vector Bool w) (input : List Γ) :
    (FixedAlphabetCompiler.bitsWord e input).length=w*input.length := by
  induction input with
  | nil => simp [FixedAlphabetCompiler.bitsWord]
  | cons a input ih =>
    simp only [FixedAlphabetCompiler.bitsWord,List.flatMap_cons,List.length_append] at ih ⊢
    rw [show (e a).toList.length=w from (e a).2,ih,List.length_cons,Nat.mul_add,Nat.mul_one]
    omega
end MatchingFPRAS.FixedEncoding

end OAI
