import OAI.NumberTheory.Ostmann.Characters.TemplateOneSidedCancellationVariation
import OAI.NumberTheory.Ostmann.Characters.TemplateOneSidedRelabelGuards

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.Characters.TemplateOneSidedRelabel
open SymbolicHistory TemplateOneSidedCancellation Template TemplateSupportRemoval
open scoped BigOperators
variable {ι κ σ τ : Type*} [DecidableEq ι] [DecidableEq κ]

def pullOther (π : ι ≃ κ) (i : ι) (x : Other (π i) → ℤ) : Other i → ℤ :=
  fun j=>x ⟨π j.val,fun h=>j.property (π.injective h)⟩

theorem insertCoordinate_pullOther (π : ι ≃ κ) (i : ι)
    (x : Other (π i) → ℤ) (n : ℤ) :
    (fun j=>insertCoordinate (π i) x n (π j)) = insertCoordinate i (pullOther π i x) n := by
  funext j
  by_cases h : j=i
  · subst j
    simp only [insertCoordinate_self]
  · have hh : π j≠π i := fun h'=>h (π.injective h')
    simp only [insertCoordinate,h,hh,dite_false,pullOther]

theorem sectionPolynomial_rename (π : ι ≃ κ) (i : ι) (x : Other (π i) → ℤ)
    (P : MvPolynomial ι ℤ) :
    sectionPolynomial (π i) x (MvPolynomial.rename π P) =
      sectionPolynomial i (pullOther π i x) P := by
  unfold sectionPolynomial
  rw [MvPolynomial.eval₂_rename]
  congr 1
  funext j
  by_cases h : j=i
  · subst j
    simp
  · have hh : π j≠π i := fun h'=>h (π.injective h')
    simp [h,hh,pullOther]

@[simp] theorem argument_relabel (π : ι ≃ κ) (i : ι) (x : Other (π i) → ℤ) (e : Expr ι) :
    argument (π i) x (relabel π e) = argument i (pullOther π i x) e := by
  simp only [argument,relabel_denominator,relabel_numerator,sectionPolynomial_rename]

omit [DecidableEq ι] [DecidableEq κ] in
@[simp] theorem positiveDenominator_relabel (π : ι → κ) (e : Expr ι) :
    TemplateOneSidedCancellation.denominator (relabel π e) =
      TemplateOneSidedCancellation.denominator e := by
  simp only [TemplateOneSidedCancellation.denominator,relabel_denominator]

@[simp] theorem guardPolynomial_relabel (π : ι ≃ κ) (i : ι) (x : Other (π i) → ℤ)
    (g : Guard ι) :
    (relabelGuard π g).polynomial (π i) x = g.polynomial i (pullOther π i x) := by
  simp only [Guard.polynomial,relabelGuard,argument_relabel,positiveDenominator_relabel]

theorem guardPolynomials_relabel (π : ι ≃ κ) (i : ι) (x : Other (π i) → ℤ)
    (g : σ → Guard ι) :
    guardPolynomials (fun s=>relabelGuard π (g s)) (π i) x =
      guardPolynomials g i (pullOther π i x) := by
  funext s
  exact congrArg Neg.neg (guardPolynomial_relabel π i x (g s))

omit [DecidableEq ι] [DecidableEq κ] in
@[simp] theorem profileGuards_relabel [Fintype σ] [Fintype τ]
    (π : ι → κ) (g : σ → Guard ι) (e : τ → Expr ι) (X A B : ℝ)
    (s : σ ⊕ (τ × Bool)) :
    profileGuards (fun r=>relabelGuard π (g r)) (fun r=>relabel π (e r)) X A B s =
      relabelGuard π (profileGuards g e X A B s) := by
  rcases s with s | ⟨t,b⟩
  · rfl
  · cases b <;> rfl

omit [DecidableEq ι] [DecidableEq κ] in
theorem profileGuards_relabel_fun [Fintype σ] [Fintype τ]
    (π : ι → κ) (g : σ → Guard ι) (e : τ → Expr ι) (X A B : ℝ) :
    profileGuards (fun r=>relabelGuard π (g r)) (fun r=>relabel π (e r)) X A B =
      fun s=>relabelGuard π (profileGuards g e X A B s) :=
  funext (profileGuards_relabel π g e X A B)

theorem leafData_relabel [Fintype σ] [Fintype τ]
    (π : ι ≃ κ) (k : ℕ) (g : σ → Guard ι) (leaf : τ → BottomExpression (ι:=ι) k)
    (i : ι) (x : Other (π i) → ℤ) (X A B : ℝ) :
    leafData k (fun s=>relabelGuard π (g s)) (fun t=>relabelBottom π (leaf t))
      (π i) x X A B = leafData k g leaf i (pullOther π i x) X A B := by
  simp only [leafData,relabelBottom,periodExpression_relabel,profileGuards_relabel_fun]
  rw [guardPolynomials_relabel π i x]
  simp only [argument_relabel,positiveDenominator_relabel,relabelGuard]

omit [DecidableEq ι] [DecidableEq κ] in
theorem leafDegreeBudget_relabel [Fintype σ] [Fintype τ]
    (π : ι → κ) (k : ℕ) (g : σ → Guard ι) (leaf : τ → BottomExpression (ι:=ι) k)
    (X A B : ℝ) :
    leafDegreeBudget k (fun s=>relabelGuard π (g s)) (fun t=>relabelBottom π (leaf t)) X A B =
      leafDegreeBudget k g leaf X A B := by
  simp only [leafDegreeBudget,relabelBottom,periodExpression_relabel,profileGuards_relabel_fun]
  simp only [relabelGuard,relabel_degreeBudget]

end Ostmann.Characters.TemplateOneSidedRelabel

end

end OAI
