import OAI.NumberTheory.Ostmann.Characters.RationalHistory
import OAI.NumberTheory.Ostmann.Characters.ZeroVariable

namespace OAI

noncomputable section
namespace Ostmann.Characters.RationalHistory.Expr
open MvPolynomial
variable {ι:Type*} [DecidableEq ι]

def atoms : Expr ι→Finset ι
  | .atom i => {i}
  | .fixed _ => ∅
  | .add a b => atoms a∪atoms b
  | .sub a b => atoms a∪atoms b
  | .mul a b => atoms a∪atoms b
  | .divide a b => atoms a∪atoms b

private theorem vars_mul_within {P Q:MvPolynomial ι ℤ} {S:Finset ι}
    (hP:P.vars⊆S) (hQ:Q.vars⊆S) : (P*Q).vars⊆S :=
  (vars_mul P Q).trans (Finset.union_subset hP hQ)

theorem fraction_vars_subset (e:Expr ι) :
    e.numerator.vars⊆e.atoms ∧ e.denominator.vars⊆e.atoms := by
  induction e with
  | atom i => simp only [numerator,denominator,fraction,atoms,vars_X,vars_one]; exact ⟨le_rfl,Finset.empty_subset _⟩
  | fixed c => simp only [numerator,denominator,fraction,atoms,vars_C,vars_one]; exact ⟨le_rfl,le_rfl⟩
  | add a b ia ib =>
    have ha := ia.1.trans (Finset.subset_union_left (s₂:=b.atoms))
    have ha' := ia.2.trans (Finset.subset_union_left (s₂:=b.atoms))
    have hb := ib.1.trans (Finset.subset_union_right (s₁:=a.atoms))
    have hb' := ib.2.trans (Finset.subset_union_right (s₁:=a.atoms))
    exact ⟨(vars_add_subset _ _).trans (Finset.union_subset
      (vars_mul_within ha hb') (vars_mul_within hb ha')),vars_mul_within ha' hb'⟩
  | sub a b ia ib =>
    have ha := ia.1.trans (Finset.subset_union_left (s₂:=b.atoms))
    have ha' := ia.2.trans (Finset.subset_union_left (s₂:=b.atoms))
    have hb := ib.1.trans (Finset.subset_union_right (s₁:=a.atoms))
    have hb' := ib.2.trans (Finset.subset_union_right (s₁:=a.atoms))
    exact ⟨(vars_sub_subset (p := a.numerator*b.denominator) (q := b.numerator*a.denominator)).trans (Finset.union_subset
      (vars_mul_within ha hb') (vars_mul_within hb ha')),vars_mul_within ha' hb'⟩
  | mul a b ia ib =>
    have ha := ia.1.trans (Finset.subset_union_left (s₂:=b.atoms))
    have ha' := ia.2.trans (Finset.subset_union_left (s₂:=b.atoms))
    have hb := ib.1.trans (Finset.subset_union_right (s₁:=a.atoms))
    have hb' := ib.2.trans (Finset.subset_union_right (s₁:=a.atoms))
    exact ⟨vars_mul_within ha hb,vars_mul_within ha' hb'⟩
  | divide a b ia ib =>
    have ha := ia.1.trans (Finset.subset_union_left (s₂:=b.atoms))
    have ha' := ia.2.trans (Finset.subset_union_left (s₂:=b.atoms))
    have hb := ib.1.trans (Finset.subset_union_right (s₁:=a.atoms))
    have hb' := ib.2.trans (Finset.subset_union_right (s₁:=a.atoms))
    exact ⟨vars_mul_within ha hb',vars_mul_within ha' hb⟩

private theorem setZero_eq_self_of_not_mem_vars (P:MvPolynomial ι ℤ)
    (i:ι) (hi:i∉P.vars) : ZeroVariable.setZero i P=P := by
  calc
    _ = eval₂Hom C X P := by
      apply eval₂Hom_congr' rfl _ rfl
      intro j hj _
      have hji:j≠i := fun he=>hi (he ▸ hj)
      simp only [hji,ite_false]
    _ = P := eval₂_eta P

theorem setZero_numerator_of_not_mem (e:Expr ι) (i:ι) (hi:i∉e.atoms) :
    ZeroVariable.setZero i e.numerator=e.numerator :=
  setZero_eq_self_of_not_mem_vars _ i (fun h=>hi (e.fraction_vars_subset.1 h))

theorem setZero_denominator_of_not_mem (e:Expr ι) (i:ι) (hi:i∉e.atoms) :
    ZeroVariable.setZero i e.denominator=e.denominator :=
  setZero_eq_self_of_not_mem_vars _ i (fun h=>hi (e.fraction_vars_subset.2 h))

end Ostmann.Characters.RationalHistory.Expr

end

end OAI
