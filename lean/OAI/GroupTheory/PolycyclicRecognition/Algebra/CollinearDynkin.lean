import OAI.GroupTheory.PolycyclicRecognition.Algebra.DynkinWords
import OAI.GroupTheory.PolycyclicRecognition.Geometry.ExponentialTangentUniqueness
import OAI.GroupTheory.PolycyclicRecognition.Geometry.ExponentialProductChart

namespace OAI

/-! # Collinear restrictions of the finite BCH formula

All nonlinear bracket terms vanish on a line. The derivative of a genuine
one-parameter subgroup then determines the remaining linear term, without
assuming injectivity of the exponential.
-/

noncomputable section
namespace PolycyclicRecognition

variable {L I : Type*} [LieRing L] [LieAlgebra ℝ L]

theorem finiteDynkinPolynomial_zero {c n : ℕ} (coeff : DynkinCoefficients c n) :
    finiteDynkinPolynomial coeff (0 : Fin n → L) = 0 := by
  have hw (w : FreeMagma (Fin n)) : evalBracketWord (0 : Fin n → L) w = 0 := by
    induction w using FreeMagma.rec with
    | of i => rfl
    | mul u v hu hv => simp only [evalBracketWord, hu, hv, lie_zero]
  simp only [finiteDynkinPolynomial, hw, smul_zero, Finset.sum_const_zero]

theorem eval_rightNestedWord_succ_collinear (a : I → ℝ) (v : L)
    (d : ℕ) (w : Fin (d + 2) → I) :
    evalBracketWord (fun i => a i • v) (rightNestedWord (d + 1) w) = 0 := by
  induction d with
  | zero => simp [rightNestedWord, evalBracketWord, lie_smul, smul_lie]
  | succ d ih =>
    change ⁅a (w 0) • v,
      evalBracketWord (fun i => a i • v) (rightNestedWord (d + 1) (fun i => w i.succ))⁆ = 0
    rw [ih, lie_zero]

theorem finiteDynkinPolynomial_collinear_smul {c n : ℕ}
    (coeff : DynkinCoefficients c n) (a : Fin n → ℝ) (v : L) (s : ℝ) :
    finiteDynkinPolynomial coeff (fun i => (s * a i) • v) =
      s • finiteDynkinPolynomial coeff (fun i => a i • v) := by
  have hw (k : ℕ) (w : Fin (k + 1) → Fin n) :
      evalBracketWord (fun i => (s * a i) • v) (rightNestedWord k w) =
        s • evalBracketWord (fun i => a i • v) (rightNestedWord k w) := by
    cases k with
    | zero => simp only [rightNestedWord, evalBracketWord, smul_smul]
    | succ k => simp only [eval_rightNestedWord_succ_collinear, smul_zero]
  simp only [finiteDynkinPolynomial, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro d _
  apply Finset.sum_congr rfl
  intro w _
  rw [hw, smul_smul, smul_smul, mul_comm (coeff d w) s]

open scoped Manifold

variable {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace G] [ChartedSpace E G] [Group G]
  [LieGroup (𝓘(ℝ, E)) ⊤ G]

/-- A single nonzero logarithm is fixed by the BCH polynomial, as follows
from the actual derivative of its exponential curve. -/
theorem finiteDynkinPolynomial_single_of_product
    {Exp : GroupLieAlgebra (𝓘(ℝ, E)) G → G} (hExp : IsGroupExponential Exp)
    {c n : ℕ} (coeff : DynkinCoefficients c n)
    (hprod : ∀ X : Fin n → GroupLieAlgebra (𝓘(ℝ, E)) G,
      (List.ofFn (fun i => Exp (X i))).prod = Exp (finiteDynkinPolynomial coeff X))
    (i : Fin n) (v : GroupLieAlgebra (𝓘(ℝ, E)) G) :
    finiteDynkinPolynomial coeff (Pi.single i v) = v := by
  classical
  apply hExp.eq_of_oneParameter_eq
  intro s
  have hbase : (fun j : Fin n => ((Pi.single i (1 : ℝ) : Fin n → ℝ) j) • v) = Pi.single i v := by
    funext j
    by_cases h : j = i <;> simp [h]
  have hscaled : (fun j : Fin n => (s * ((Pi.single i (1 : ℝ) : Fin n → ℝ) j)) • v) =
      Pi.single i (s • v) := by
    funext j
    by_cases h : j = i <;> simp [h]
  rw [← hbase, ← finiteDynkinPolynomial_collinear_smul, hscaled, ← hprod]
  simpa only [Pi.single_eq_same] using list_prod_ofFn_eq_single
    (fun j => Exp ((Pi.single i (s • v) :
      Fin n → GroupLieAlgebra (𝓘(ℝ, E)) G) j)) i (by
      intro j hj
      simp [Pi.single_eq_of_ne hj, hExp.map_zero])

end PolycyclicRecognition

end

end OAI
