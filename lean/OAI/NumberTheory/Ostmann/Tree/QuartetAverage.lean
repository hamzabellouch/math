import OAI.NumberTheory.Ostmann.Tree.QuartetCoefficient
import OAI.NumberTheory.Ostmann.Tree.QuartetSquareMeasure
import OAI.NumberTheory.Ostmann.Tree.TwoPairRatioEnergy

namespace OAI

noncomputable section
open scoped BigOperators

namespace Ostmann.Tree.Quartet
open Density

theorem average_sum {A B : Type*} [Fintype A] (s : Finset B) (f : B → A → ℝ) :
    average (fun x => ∑ b ∈ s, f b x) = ∑ b ∈ s, average (f b) := by
  unfold average
  rw [Finset.sum_comm, Finset.mul_sum]

theorem sum_inverse_square {G : Type*} [CommGroup G] [Fintype G] [DecidableEq G]
    (ρ : G) (B : G → ℝ) :
    (∑ χ : G with χ^2=ρ⁻¹, B χ⁻¹) = ∑ ν : G with ν^2=ρ, B ν := by
  classical
  have hs := (Equiv.inv G).bijective.sum_comp (fun ν : G => if ν^2=ρ then B ν else 0)
  simp only [Equiv.inv_apply, inv_pow, inv_eq_iff_eq_inv] at hs
  simpa only [Finset.sum_filter] using hs

end Ostmann.Tree.Quartet

namespace Ostmann.FiniteField
open Ostmann.Tree.Density Ostmann.Tree.Quartet
variable {p : ℕ} [Fact p.Prime]

theorem crossMajorant_average_sum (g h : ZMod p → ℂ) (σ τ : (ZMod p)ˣ)
    (L R : PairMode) (ρ : MulChar (ZMod p) ℂ) (y : (ZMod p)ˣ) :
    average (fun lam : (ZMod p)ˣ => average (fun mu : (ZMod p)ˣ =>
      ∑ χ : MulChar (ZMod p) ℂ with χ^2=ρ⁻¹,
        ‖twoPairConvolution g h σ τ L R χ⁻¹ lam mu y‖^2)) =
      ∑ ν : MulChar (ZMod p) ℂ with ν^2=ρ, crossMajorant g h σ τ L R ν y := by
  classical
  simp_rw [average_sum]
  rw [sum_inverse_square ρ (fun ν => average (fun lam : (ZMod p)ˣ =>
    average (fun mu : (ZMod p)ˣ => ‖twoPairConvolution g h σ τ L R ν lam mu y‖^2)))]
  apply Finset.sum_congr rfl
  intro ν _
  unfold average crossMajorant
  rw [← Finset.mul_sum]
  ring

end Ostmann.FiniteField

namespace Ostmann.Tree.Quartet.NodeInput
open Density Ostmann.FiniteField
variable {p : ℕ} [Fact p.Prime]

theorem crossFamily_average_coefficient (N : NodeInput (ZMod p) 1)
    (hcons : N.parameters.consistent) (hopp : N.parameters.bottomOpposite)
    (g : ZMod p → ℂ) (hg0 : g 0=0) (a b : Bool) (m : (ZMod p)ˣ)
    (ρ : MulChar (ZMod p) ℂ) :
    average (fun h : (ZMod p)ˣ => average (fun k : (ZMod p)ˣ =>
      ‖mellin (N.crossFamilyFunction g a b m h k) ρ‖^2)) ≤
      8*‖(p:ℂ)/(Fintype.card (ZMod p)ˣ:ℂ)‖^2 *
        ∑ ν : MulChar (ZMod p) ℂ with ν^2=ρ,
          crossMajorant (signedFunction g (parameterSign N.left a))
            (signedFunction g (parameterSign N.right b)) (orientation a) (orientation b)
            (pairMode a) (pairMode b) ν (N.familyRoot m) := by
  classical
  let C : ℝ := 2*‖(p:ℂ)/(Fintype.card (ZMod p)ˣ:ℂ)‖^2
  let H : (ZMod p)ˣ → (ZMod p)ˣ → ℝ := fun lam mu =>
    ∑ χ : MulChar (ZMod p) ℂ with χ^2=ρ⁻¹,
      ‖twoPairConvolution (signedFunction g (parameterSign N.left a))
        (signedFunction g (parameterSign N.right b)) (orientation a) (orientation b)
        (pairMode a) (pairMode b) χ⁻¹ lam mu (N.familyRoot m)‖^2
  have hH : ∀ lam mu, 0 ≤ H lam mu := by
    intro lam mu
    exact Finset.sum_nonneg (fun χ _ => sq_nonneg _)
  calc
    _ ≤ average (fun h : (ZMod p)ˣ => average (fun k : (ZMod p)ˣ =>
        C*H (N.leftLambda m a*h^2) (N.rightLambda m b*k^2))) := by
      apply average_mono
      intro h
      apply average_mono
      intro k
      exact crossFamily_coefficient_bound N hcons hopp g hg0 a b m h k ρ
    _ = C*average (fun h : (ZMod p)ˣ => average (fun k : (ZMod p)ˣ =>
        H (N.leftLambda m a*h^2) (N.rightLambda m b*k^2))) := by
      simp_rw [average_const_mul]
    _ ≤ C*(4*average (fun lam : (ZMod p)ˣ => average (H lam))) := by
      have hs := independent_square_domination (N.leftLambda m a) (N.rightLambda m b) H hH
      have havg {A : Type} (i j : Fintype A) (f : A → ℝ) :
          @average A i f = @average A j f := by
        congr
        exact Subsingleton.elim _ _
      simp only [havg _ (inferInstance : Fintype (ZMod p)ˣ)] at hs
      exact mul_le_mul_of_nonneg_left hs (by dsimp [C]; positivity)
    _ = _ := by
      dsimp [H, C]
      rw [crossMajorant_average_sum]
      ring

end Ostmann.Tree.Quartet.NodeInput
end

end OAI
