import Mathlib.Analysis.Calculus.TaylorIntegral
import OAI.Geometry.NodalSets.Elliptic.SmoothJet

namespace OAI

namespace Yau.Jets
open MvPolynomial
open scoped ContDiff
noncomputable section

def tensorPolynomial : {n : ℕ} →
    ContinuousMultilinearMap ℝ (fun _ : Fin n ↦ Coord) ℂ → CPoly
  | 0, T => C (T 0)
  | _n + 1, T => ∑ i : Fin 4, X i * tensorPolynomial (T.curryLeft (Pi.single i 1))

lemma coord_basis_sum (x : Coord) : ∑ i : Fin 4, x i • Pi.single i 1 = x := by
  ext j
  simp [Finset.sum_apply, Pi.single_apply, smul_eq_mul, mul_ite]

theorem reval_tensorPolynomial {n : ℕ}
    (T : ContinuousMultilinearMap ℝ (fun _ : Fin n ↦ Coord) ℂ) (x : Coord) :
    reval (tensorPolynomial T) x = T (fun _ ↦ x) := by
  induction n with
  | zero => simp [tensorPolynomial, reval]; congr; ext i; exact Fin.elim0 i
  | succ n ih =>
    simp only [tensorPolynomial, reval, map_sum, map_mul, eval_X]
    change (∑ i, (x i : ℂ) * reval (tensorPolynomial (T.curryLeft (Pi.single i 1))) x) = _
    simp_rw [ih]
    have h := congrArg (fun z : Coord ↦ (T.curryLeft z) (fun _ ↦ x)) (coord_basis_sum x)
    have he : Fin.cons x (fun _ : Fin n ↦ x) = fun _ ↦ x := by ext i; exact Fin.cases rfl (fun _ ↦ rfl) i
    simpa [map_sum, map_smul, ContinuousMultilinearMap.curryLeft_apply, he,
      RCLike.real_smul_eq_coe_mul] using h

lemma tensorPolynomial_homogeneous {n : ℕ}
    (T : ContinuousMultilinearMap ℝ (fun _ : Fin n ↦ Coord) ℂ) :
    (tensorPolynomial T).IsHomogeneous n := by
  induction n with
  | zero => exact isHomogeneous_C _ _
  | succ n ih =>
    apply IsHomogeneous.sum
    intro i _
    simpa [Nat.add_comm] using (isHomogeneous_X ℂ i).mul (ih _)

def taylorPolynomial (f : Coord → ℂ) (y : Coord) (m : ℕ) : CPoly :=
  ∑ k ∈ Finset.range (m + 1), C (((k.factorial : ℝ)⁻¹ : ℝ) : ℂ) *
    tensorPolynomial (iteratedFDeriv ℝ k f y)

theorem reval_taylorPolynomial (f : Coord → ℂ) (y x : Coord) (m : ℕ) :
    reval (taylorPolynomial f y m) x =
      ∑ k ∈ Finset.range (m + 1), (k.factorial : ℝ)⁻¹ •
        iteratedFDeriv ℝ k f y (fun _ ↦ x) := by
  simp only [taylorPolynomial, reval, map_sum, map_mul, eval_C]
  change (∑ k ∈ Finset.range (m + 1), _ * reval (tensorPolynomial _) x) = _
  simp_rw [reval_tensorPolynomial, RCLike.real_smul_eq_coe_mul]
  rfl

theorem taylorPolynomial_remainder (f : Coord → ℂ) (hf : ContDiff ℝ ∞ f)
    (y x : Coord) (m : ℕ) :
    f (y + x) - reval (taylorPolynomial f y m) x =
      (m.factorial : ℝ)⁻¹ • ∫ t in (0 : ℝ)..1, (1 - t)^m •
        iteratedFDeriv ℝ (m + 1) f (y + t • x) (fun _ ↦ x) := by
  rw [reval_taylorPolynomial, sub_eq_iff_eq_add']
  exact map_add_eq_sum_add_integral_iteratedFDeriv (fun t _ ↦
    hf.contDiffAt.of_le (by exact_mod_cast (show ((m + 1 : ℕ) : ℕ∞) ≤ ⊤ from le_top)))

end
end Yau.Jets

end OAI
