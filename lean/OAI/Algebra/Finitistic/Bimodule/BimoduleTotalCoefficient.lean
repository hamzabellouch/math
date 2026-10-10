import OAI.Algebra.Finitistic.Localization.FiniteSupportReindex
import OAI.Algebra.Finitistic.Bimodule.BimoduleLeftNaturality

namespace OAI
noncomputable section
open CategoryTheory CategoryTheory.Limits
namespace LittleFinitistic.BimoduleTotal
open ExternalTensor.Section4
universe u
variable (k B : Type u) [Field k] [Ring B] [Algebra k B]
variable (P : BiComplex k B) (Z : CochainComplex (ModuleCat.{u} B) ℤ)
variable {l : ℕ} (p : Fin l → ℤ) (hp : StrictMono p)

def coefficient (n a : ℤ) : TotalTerm k B P p Z n →ₗ[B] Term k B P Z a (n + -a) :=
  FiniteSupportReindex.coefficient (fun a => ModuleCat.of B (Term k B P Z a (n + -a))) p a

include hp in
@[simp] theorem coefficient_at (n : ℤ) (i : Fin l) (x : TotalTerm k B P p Z n) :
    coefficient k B P Z p n (p i) x = x i :=
  FiniteSupportReindex.coefficient_at
    (fun a => ModuleCat.of B (Term k B P Z a (n + -a))) p hp.injective i x

theorem coefficient_outside (n a : ℤ) (ha : ∀ i, p i ≠ a) : coefficient k B P Z p n a = 0 :=
  FiniteSupportReindex.coefficient_outside _ p a ha

theorem term_left_isZero (a q : ℤ) (ha : IsZero (P.X a)) :
    IsZero (ModuleCat.of B (Term k B P Z a q)) :=
  (BimoduleBalancedTensor.functor k B (ComplexTensor.leftTerm k B Z q)).map_isZero ha

variable (hP : ∀ a, (∀ i, p i ≠ a) → IsZero (P.X a))

include hP in
/-- The original total differential, read in any integer left degree, including
zero degrees outside the chosen finite support. -/
theorem coefficient_d_sum (n a : ℤ) (x : TotalTerm k B P p Z n) :
    coefficient k B P Z p (n+1) a (((total k B P p hp Z).d n (n+1)).hom x) =
      (show Term k B P Z a ((n+1) + -a) from
        ((ComplexTensor.column k B (right k B P) Z a).d n (n+1)).hom
          (coefficient k B P Z p n a x)) +
      ∑ i : Fin l, entryBetween k B P Z n (n+1) (p i) a rfl (x i) := by
  classical
  by_cases ha : ∃ i, p i=a
  · obtain ⟨i,rfl⟩ := ha
    erw [coefficient_at k B P Z p hp,coefficient_at k B P Z p hp]
    exact total_d_apply k B P Z p hp n (n+1) rfl x i
  · let := ModuleCat.subsingleton_of_isZero
      (term_left_isZero k B P Z a ((n+1) + -a) (hP a (by simpa only [not_exists] using ha)))
    exact Subsingleton.elim _ _

include hp in
/-- The horizontal sum has at most its immediately preceding left-degree component. -/
theorem horizontal_sum_predecessor (n a : ℤ) (x : TotalTerm k B P p Z n) :
    (∑ i : Fin l, entryBetween k B P Z n (n+1) (p i) a rfl (x i)) =
      horizontalBetween k B P Z n (n+1) (a-1) a rfl (by omega)
        (coefficient k B P Z p n (a-1) x) := by
  classical
  by_cases ha : ∃ i, p i=a-1
  · obtain ⟨i,hi⟩ := ha
    rw [Finset.sum_eq_single i]
    · have transfer (b : ℤ) (hb : b=p i) (hba : b+1=a) :
          horizontalBetween k B P Z n (n+1) b a rfl hba
            (coefficient k B P Z p n b x) =
          entryBetween k B P Z n (n+1) (p i) a rfl (x i) := by
        subst b
        rw [coefficient_at k B P Z p hp]
        unfold entryBetween
        rw [dite_eq_left hba]
      exact (transfer (a-1) hi.symm (by omega)).symm
    · intro j _ hji
      unfold entryBetween
      rw [dite_eq_right (fun h => hji (hp.injective (by omega)))]
      rfl
    · simp
  · have ha' : ∀ i, p i ≠ a-1 := by simpa only [not_exists] using ha
    rw [coefficient_outside k B P Z p n (a-1) ha',LinearMap.zero_apply,map_zero]
    apply Finset.sum_eq_zero
    intro i _
    unfold entryBetween
    rw [dite_eq_right (fun h => ha' i (by omega))]
    rfl

include hP in
/-- The complete finite tensor differential consists of its signed vertical term
and its immediately preceding horizontal term. -/
theorem coefficient_d (n a : ℤ) (x : TotalTerm k B P p Z n) :
    coefficient k B P Z p (n+1) a (((total k B P p hp Z).d n (n+1)).hom x) =
      (show Term k B P Z a ((n+1) + -a) from
        ((ComplexTensor.column k B (right k B P) Z a).d n (n+1)).hom
          (coefficient k B P Z p n a x)) +
      horizontalBetween k B P Z n (n+1) (a-1) a rfl (by omega)
        (coefficient k B P Z p n (a-1) x) := by
  rw [coefficient_d_sum k B P Z p hp hP,horizontal_sum_predecessor k B P Z p hp]
end LittleFinitistic.BimoduleTotal

end

end OAI
