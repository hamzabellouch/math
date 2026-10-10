import OAI.NumberTheory.Ostmann.Tree.QuartetAverage
import OAI.NumberTheory.Ostmann.Tree.QuartetCrossAction
import OAI.NumberTheory.Ostmann.Tree.SquareMajorant

namespace OAI

noncomputable section
open scoped BigOperators
namespace Ostmann.Tree.Quartet
open Density

theorem real_average_equiv {A B : Type*} [Fintype A] [Fintype B]
    (e : A ≃ B) (f : B → ℝ) : average (fun x => f (e x)) = average f := by
  unfold average
  rw [Fintype.card_congr e, e.bijective.sum_comp f]

theorem real_average_prod {A B : Type*} [Fintype A] [Fintype B]
    (f : A → B → ℝ) :
    average (fun x : A × B => f x.1 x.2) = average (fun a => average (f a)) := by
  simp only [average, Fintype.card_prod, Nat.cast_mul, mul_inv_rev,
    Fintype.sum_prod_type, ← Finset.mul_sum]
  ring

theorem real_average_const {A : Type*} [Fintype A] [Nonempty A] (c : ℝ) :
    average (fun _ : A => c) = c := by
  simp [average, Fintype.card_ne_zero]

namespace NodeInput
open Ostmann.FiniteField
variable {p : ℕ} [Fact p.Prime]

def crossLocalMajorant (N : NodeInput (ZMod p) 1) (g : ZMod p → ℂ)
    (a b : Bool) (ρ : MulChar (ZMod p) ℂ) (y : ZMod p) : ℝ :=
  8*‖(p:ℂ)/(Fintype.card (ZMod p)ˣ:ℂ)‖^2 *
    crossSquareMajorant (signedFunction g (parameterSign N.left a))
      (signedFunction g (parameterSign N.right b)) (orientation a) (orientation b)
      (pairMode a) (pairMode b) ρ y

theorem crossLocalMajorant_nonneg (N : NodeInput (ZMod p) 1) (g : ZMod p → ℂ)
    (a b : Bool) (ρ : MulChar (ZMod p) ℂ) (y : ZMod p) :
    0 ≤ N.crossLocalMajorant g a b ρ y := by
  unfold crossLocalMajorant
  exact mul_nonneg (by positivity) (crossSquareMajorant_nonneg _ _ _ _ _ _ _ _)

theorem crossAction_fiber_bound (N : NodeInput (ZMod p) 1)
    (hcons : N.parameters.consistent) (hopp : N.parameters.bottomOpposite)
    (g : ZMod p → ℂ) (hg0 : g 0=0) (a b : Bool) (m : (ZMod p)ˣ)
    (ρ : MulChar (ZMod p) ℂ) :
    average (fun M : {M : Leaves 2 → (ZMod p)ˣ // Parameters.leafProduct M=m} =>
      ‖mellin (fun z : (ZMod p)ˣ => N.parameters.evaluate g N.D N.Xleft N.Xright 0
        (moveCross M.val a b z)) ρ‖^2) ≤ N.crossLocalMajorant g a b ρ (N.familyRoot m) := by
  classical
  have he := real_average_equiv (crossFiberEquiv a b m)
    (fun M : {M : Leaves 2 → (ZMod p)ˣ // Parameters.leafProduct M=m} =>
      ‖mellin (fun z : (ZMod p)ˣ => N.parameters.evaluate g N.D N.Xleft N.Xright 0
        (moveCross M.val a b z)) ρ‖^2)
  rw [← he]
  change average (fun x : (ZMod p)ˣ × (ZMod p)ˣ × (ZMod p)ˣ =>
    ‖mellin (fun z : (ZMod p)ˣ => N.parameters.evaluate g N.D N.Xleft N.Xright 0
      (moveCross (crossAssignment a b m x.1 x.2.1 x.2.2) a b z)) ρ‖^2) ≤ _
  simp_rw [crossAction_coefficient_norm]
  rw [real_average_prod (fun h (t : (ZMod p)ˣ × (ZMod p)ˣ) =>
    ‖mellin (N.crossFamilyFunction g a b m h t.1) ρ‖^2)]
  have ht (h : (ZMod p)ˣ) :
      average (fun t : (ZMod p)ˣ × (ZMod p)ˣ =>
        ‖mellin (N.crossFamilyFunction g a b m h t.1) ρ‖^2) =
      average (fun k : (ZMod p)ˣ => ‖mellin (N.crossFamilyFunction g a b m h k) ρ‖^2) := by
    rw [real_average_prod (fun k (_ : (ZMod p)ˣ) =>
      ‖mellin (N.crossFamilyFunction g a b m h k) ρ‖^2)]
    simp_rw [real_average_const]
  simp_rw [ht]
  exact crossFamily_average_coefficient N hcons hopp g hg0 a b m ρ

end NodeInput
end Ostmann.Tree.Quartet
end

end OAI
