import OAI.NumberTheory.Ostmann.Arithmetic.HistoryFieldEvaluation
import OAI.NumberTheory.Ostmann.Characters.RationalHistoryDegree
import OAI.NumberTheory.Ostmann.Characters.RationalHistoryVariables

namespace OAI

noncomputable section
namespace Ostmann.Characters.RationalHistory.Expr
variable {ι κ τ : Type*}

def rename (f : ι → κ) : Expr ι → Expr κ
  | .atom i => .atom (f i)
  | .fixed c => .fixed c
  | .add a b => .add (a.rename f) (b.rename f)
  | .sub a b => .sub (a.rename f) (b.rename f)
  | .mul a b => .mul (a.rename f) (b.rename f)
  | .divide a b => .divide (a.rename f) (b.rename f)

@[simp] theorem rename_id (e : Expr ι) : e.rename id = e := by
  induction e <;> simp_all [rename]

@[simp] theorem rename_comp (e : Expr ι) (f : ι → κ) (g : κ → τ) :
    (e.rename f).rename g = e.rename (g ∘ f) := by
  induction e <;> simp_all [rename]

theorem fraction_rename (e : Expr ι) (f : ι → κ) :
    (e.rename f).fraction =
      (MvPolynomial.rename f e.fraction.1, MvPolynomial.rename f e.fraction.2) := by
  induction e <;> simp_all [rename, fraction, map_add, map_sub, map_mul]

@[simp] theorem numerator_rename (e : Expr ι) (f : ι → κ) :
    (e.rename f).numerator = MvPolynomial.rename f e.numerator :=
  congrArg Prod.fst (fraction_rename e f)

@[simp] theorem denominator_rename (e : Expr ι) (f : ι → κ) :
    (e.rename f).denominator = MvPolynomial.rename f e.denominator :=
  congrArg Prod.snd (fraction_rename e f)

@[simp] theorem rationalEval_rename (e : Expr ι) (f : ι → κ) (x : κ → ℚ) :
    (e.rename f).rationalEval x = e.rationalEval (x ∘ f) := by
  induction e <;> simp_all [rename, rationalEval]

@[simp] theorem integerEval_rename (e : Expr ι) (f : ι → κ) (x : κ → ℤ) :
    (e.rename f).integerEval x = e.integerEval (x ∘ f) := by
  induction e <;> simp_all [rename, integerEval]

@[simp] theorem fieldEval_rename {K : Type*} [Field K]
    (e : Expr ι) (f : ι → κ) (x : κ → K) :
    (e.rename f).fieldEval x = e.fieldEval (x ∘ f) := by
  induction e <;> simp_all [rename, fieldEval]

@[simp] theorem regularAt_rename (e : Expr ι) (f : ι → κ) (x : κ → ℚ) :
    (e.rename f).RegularAt x ↔ e.RegularAt (x ∘ f) := by
  induction e <;> simp_all [rename, RegularAt]

@[simp] theorem integralAt_rename (e : Expr ι) (f : ι → κ) (x : κ → ℤ) :
    (e.rename f).IntegralAt x ↔ e.IntegralAt (x ∘ f) := by
  induction e <;> simp_all [rename, IntegralAt]

@[simp] theorem fieldRegularAt_rename {K : Type*} [Field K]
    (e : Expr ι) (f : ι → κ) (x : κ → K) :
    (e.rename f).FieldRegularAt x ↔ e.FieldRegularAt (x ∘ f) := by
  induction e <;> simp_all [rename, FieldRegularAt]

@[simp] theorem atomCount_rename (e : Expr ι) (f : ι → κ) :
    (e.rename f).atomCount = e.atomCount := by
  induction e <;> simp_all [rename, atomCount]

@[simp] theorem atoms_rename [DecidableEq ι] [DecidableEq κ]
    (e : Expr ι) (f : ι → κ) :
    (e.rename f).atoms = e.atoms.image f := by
  induction e <;> simp_all [rename, atoms, Finset.image_union]

end Ostmann.Characters.RationalHistory.Expr
end

end OAI
