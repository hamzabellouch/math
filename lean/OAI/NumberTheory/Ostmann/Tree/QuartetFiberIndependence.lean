import OAI.NumberTheory.Ostmann.Tree.CutFiberAverage
import OAI.NumberTheory.Ostmann.Tree.QuartetFactorizationFibers

namespace OAI

namespace Ostmann.Tree
noncomputable section
open scoped BigOperators
open Ostmann.Arithmetic.ResidueHaar
open QuartetFactorization

local instance fiberIndependenceDecEq {F : Type*} [Field F] : DecidableEq F := Classical.decEq F
local instance fiberIndependenceFintype {A B : Type*} [Fintype A] (f : A → B) (y : B) :
    Fintype {x : A // f x=y} := Fintype.ofFinite _

theorem average_pi_product {I : Type*} [Fintype I] [DecidableEq I]
    {A : I → Type*} [∀i,Fintype (A i)] (f : ∀i,A i → ℂ) :
    average (fun x : ∀i,A i => ∏i,f i (x i)) = ∏i,average (f i) := by
  classical
  simp only [average,Fintype.card_pi,Nat.cast_prod,Finset.prod_inv_distrib,
    Finset.prod_mul_distrib,← Fintype.prod_sum]

theorem quartet_fiber_product {F : Type*} [Field F] [Fintype F]
    (k : ℕ) (totals : Leaves k → Fˣ)
    (w : Leaves k → (Leaves 2 → Fˣ) → ℂ) :
    fiberAverage (bottomCut k).project
      (fun M => ∏v,w v (bottomLeaves k M v)) totals =
      ∏v,fiberAverage Parameters.leafProduct (w v) (totals v) := by
  classical
  have he := average_equiv (productFiberEquiv k totals)
    (fun x => ∏v,w v (x v).val)
  have hp := average_pi_product (fun v (x : {m : Leaves 2 → Fˣ // Parameters.leafProduct m=totals v}) => w v x.val)
  exact he.trans hp

theorem quartet_fiber_product_real {F : Type*} [Field F] [Fintype F]
    (k : ℕ) (totals : Leaves k → Fˣ)
    (w : Leaves k → (Leaves 2 → Fˣ) → ℝ) :
    Density.average (fun M : {M : Leaves (k+2) → Fˣ // (bottomCut k).project M=totals} =>
      ∏v,w v (bottomLeaves k M.val v)) =
    ∏v,Density.average (fun m : {m : Leaves 2 → Fˣ // Parameters.leafProduct m=totals v} => w v m.val) := by
  apply Complex.ofReal_injective
  have h := quartet_fiber_product k totals (fun v m => (w v m:ℂ))
  simpa only [fiberAverage,average,Density.average,Complex.ofReal_mul,Complex.ofReal_inv,
    Complex.ofReal_sum,Complex.ofReal_prod,Complex.ofReal_natCast] using h

end
end Ostmann.Tree

end OAI
