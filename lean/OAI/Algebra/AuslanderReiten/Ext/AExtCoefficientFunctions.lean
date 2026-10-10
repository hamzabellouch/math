import OAI.Algebra.AuslanderReiten.Ext.AExtCoefficientCore

namespace OAI

noncomputable section
open CategoryTheory CategoryTheory.Abelian
open scoped TensorProduct ModuleCat.Algebra
namespace ArExplicit.Resolution
universe u
variable {k : Type u} [Field k] [CharP k 2] (q : k)
variable [HasDerivedCategory (ModuleCat.{u} (ArExplicit.T k q))]
variable (hq : q ≠ 0) (hq1 : 1+q ≠ 0) (h : NoPositivePowerOne q)

abbrev aCoefficientFunction (n : ℕ) := fun x : ASelfExt q (3*n) =>
  tTensorCoefficientEquiv q hq hq1 h n (aExtKunnethEquiv q (3*n) x)

theorem aCoefficientFunction_injective (n : ℕ) :
    Function.Injective (aCoefficientFunction q hq hq1 h n) :=
  (tTensorCoefficientEquiv q hq hq1 h n).injective.comp
    (aExtKunnethEquiv q (3*n)).injective

theorem aCoefficientFunction_surjective (n : ℕ) :
    Function.Surjective (aCoefficientFunction q hq hq1 h n) :=
  (tTensorCoefficientEquiv q hq hq1 h n).surjective.comp
    (aExtKunnethEquiv q (3*n)).surjective

theorem aCoefficientFunction_add (n : ℕ) (x y : ASelfExt q (3*n)) :
    type_of% ((congrArg (tTensorCoefficientEquiv q hq hq1 h n)
      ((aExtKunnethEquiv q (3*n)).map_add x y)).trans
        ((tTensorCoefficientEquiv q hq hq1 h n).map_add
          (aExtKunnethEquiv q (3*n) x) (aExtKunnethEquiv q (3*n) y))) :=
  (congrArg (tTensorCoefficientEquiv q hq hq1 h n)
    ((aExtKunnethEquiv q (3*n)).map_add x y)).trans
      ((tTensorCoefficientEquiv q hq hq1 h n).map_add
        (aExtKunnethEquiv q (3*n) x) (aExtKunnethEquiv q (3*n) y))

end ArExplicit.Resolution

end

end OAI
