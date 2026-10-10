import OAI.NumberTheory.DirichletL.Reflection.MarkedSource
import OAI.NumberTheory.DirichletL.Reflection.SlotCoefficients

namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators
open ActualEisensteinCubic CompletedGauss CanonicalQuadraticSieve InverseMoment
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O

lemma prime_dvd_cube_mul (P H A : Ideal Eis) (hP : Prime P) :
    P∣H^3*A ↔ P∣H ∨ P∣A := by
  constructor
  · intro h
    rcases hP.dvd_mul.mp h with h|h
    · exact Or.inl (hP.dvd_of_dvd_pow h)
    · exact Or.inr h
  · rintro (h|h)
    · exact dvd_mul_of_dvd_left (dvd_pow h (by decide : (3:ℕ)≠0)) A
    · exact dvd_mul_of_dvd_right h _

variable {σ : Type*} [Fintype σ] [DecidableEq σ]

def cubeActiveSlots (H : Ideal Eis) (S : PrimeFamily σ) : Finset σ :=
  Finset.univ.filter (fun i => ¬S.ideal i∣H)

omit [DecidableEq σ] in
lemma cube_shifted_mark (H A : Ideal Eis) (S : PrimeFamily σ) :
    (∏ i,if S.ideal i∣H^3*A then (1:ℂ) else 0)=
      ∏ i∈cubeActiveSlots H S,if S.ideal i∣A then (1:ℂ) else 0 := by
  rw [cubeActiveSlots,Finset.prod_filter]
  apply Finset.prod_congr rfl
  intro i hi
  have hp : Prime (S.ideal i) := Ideal.prime_of_isPrime (NeZero.ne _) inferInstance
  rw [prime_dvd_cube_mul _ H A hp]
  by_cases hh : S.ideal i∣H
  · simp only [hh,true_or,ite_true,not_true_eq_false,ite_false]
  · simp only [hh,false_or,not_false_eq_true,ite_true]

omit [DecidableEq σ] in
lemma cube_shifted_mark_restrict (H A : Ideal Eis) (S : PrimeFamily σ) :
    (∏ i,if S.ideal i∣H^3*A then (1:ℂ) else 0)=
      ∏ i : cubeActiveSlots H S,if (S.restrict (cubeActiveSlots H S)).ideal i∣A then (1:ℂ) else 0 := by
  rw [cube_shifted_mark]
  symm
  exact Finset.prod_coe_sort (cubeActiveSlots H S) (fun i => if S.ideal i∣A then (1:ℂ) else 0)

omit [DecidableEq σ] in
theorem markedCompletedT_cube_shift (Ψ : Eis→*ℂ) (W : ℝ→ℂ) (X : ℝ)
    (H : Ideal Eis) (S : PrimeFamily σ) :
    markedCompletedT Ψ W X (fun A => ∏ i,if S.ideal i∣H^3*A then (1:ℂ) else 0)=
      markedCompletedT Ψ W X
        (fun A => ∏ i : cubeActiveSlots H S,if (S.restrict (cubeActiveSlots H S)).ideal i∣A then (1:ℂ) else 0) := by
  congr 1
  funext A
  exact cube_shifted_mark_restrict H A S

end
end SevenEighths.InverseReflectedPhase

end OAI
