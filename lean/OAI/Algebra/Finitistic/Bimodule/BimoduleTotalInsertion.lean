import OAI.Algebra.Finitistic.Bimodule.BimoduleTotalCoefficient

namespace OAI
noncomputable section
open CategoryTheory CategoryTheory.Limits
namespace LittleFinitistic.BimoduleTotal
open ExternalTensor.Section4
universe u
variable (k B : Type u) [Field k] [Ring B] [Algebra k B]
variable (P : BiComplex k B) (Z : CochainComplex (ModuleCat.{u} B) ℤ)
variable {l : ℕ} (p : Fin l → ℤ) (hp : StrictMono p)

/-- Insert one actual left-degree component into the finite total. -/
def insertion (n a : ℤ) : Term k B P Z a (n + -a) →ₗ[B] TotalTerm k B P p Z n := by
  classical
  exact LinearMap.pi (fun i => if h : p i=a then
    (eqToHom (congrArg (fun a => ModuleCat.of B (Term k B P Z a (n + -a))) h.symm)).hom else 0)

@[simp] theorem insertion_same (n : ℤ) (i : Fin l) (y : Term k B P Z (p i) (n + -(p i))) :
    insertion k B P Z p n (p i) y i = y := by
  classical
  simp [insertion]

theorem insertion_other (n a : ℤ) (i : Fin l) (h : p i ≠ a) (y : Term k B P Z a (n + -a)) :
    insertion k B P Z p n a y i = 0 := by
  classical
  simp only [insertion,LinearMap.pi_apply,dite_eq_right h,LinearMap.zero_apply]

include hp in
theorem coefficient_insertion_other (n a b : ℤ) (h : b ≠ a) (y : Term k B P Z a (n + -a)) :
    coefficient k B P Z p n b (insertion k B P Z p n a y) = 0 := by
  classical
  by_cases hb : ∃ i, p i=b
  · obtain ⟨i,rfl⟩ := hb
    rw [coefficient_at k B P Z p hp]
    exact insertion_other k B P Z p n a i h y
  · rw [coefficient_outside k B P Z p n b (by simpa only [not_exists] using hb),LinearMap.zero_apply]

variable (hP : ∀ a, (∀ i, p i ≠ a) → IsZero (P.X a))

include hp hP in
theorem coefficient_insertion_self (n a : ℤ) (y : Term k B P Z a (n + -a)) :
    coefficient k B P Z p n a (insertion k B P Z p n a y) = y := by
  classical
  by_cases ha : ∃ i, p i=a
  · obtain ⟨i,rfl⟩ := ha
    rw [coefficient_at k B P Z p hp,insertion_same]
  · let := ModuleCat.subsingleton_of_isZero
      (term_left_isZero k B P Z a (n + -a) (hP a (by simpa only [not_exists] using ha)))
    exact Subsingleton.elim _ _

include hP in
theorem coefficient_d_between (n m : ℤ) (h : n+1=m) (a : ℤ) (x : TotalTerm k B P p Z n) :
    coefficient k B P Z p m a (((total k B P p hp Z).d n m).hom x) =
      (show Term k B P Z a (m + -a) from
        ((ComplexTensor.column k B (right k B P) Z a).d n m).hom
          (coefficient k B P Z p n a x)) +
      horizontalBetween k B P Z n m (a-1) a h (by omega)
        (coefficient k B P Z p n (a-1) x) := by
  subst m
  exact coefficient_d k B P Z p hp hP n a x

include hP in
/-- A correction inserted in degree a cannot affect total coordinates above a+1. -/
theorem coefficient_d_insertion_above (n m : ℤ) (h : n+1=m) (a b : ℤ) (hab : a+1<b)
    (y : Term k B P Z a (n + -a)) :
    coefficient k B P Z p m b
      (((total k B P p hp Z).d n m).hom (insertion k B P Z p n a y)) = 0 := by
  rw [coefficient_d_between k B P Z p hp hP n m h b]
  rw [coefficient_insertion_other k B P Z p hp n a b (by omega),
    coefficient_insertion_other k B P Z p hp n a (b-1) (by omega)]
  erw [map_zero, add_zero]
  rfl

include hP in
/-- The next coordinate of the inserted correction is exactly its horizontal differential. -/
theorem coefficient_d_insertion_next (n m : ℤ) (h : n+1=m) (a b : ℤ) (hab : a+1=b)
    (y : Term k B P Z a (n + -a)) :
    coefficient k B P Z p m b
      (((total k B P p hp Z).d n m).hom (insertion k B P Z p n a y)) =
      horizontalBetween k B P Z n m a b h hab y := by
  rw [coefficient_d_between k B P Z p hp hP n m h b]
  erw [coefficient_insertion_other k B P Z p hp n a b (by omega),map_zero,zero_add]
  have transfer (c : ℤ) (hc : c=a) (hcb : c+1=b) :
      horizontalBetween k B P Z n m c b h hcb
        (coefficient k B P Z p n c (insertion k B P Z p n a y)) =
      horizontalBetween k B P Z n m a b h hab y := by
    subst c
    rw [coefficient_insertion_self k B P Z p hp hP]
  exact transfer (b-1) (by omega) (by omega)
end LittleFinitistic.BimoduleTotal

end

end OAI
