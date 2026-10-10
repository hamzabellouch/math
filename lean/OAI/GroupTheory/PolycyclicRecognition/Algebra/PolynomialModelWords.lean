import OAI.GroupTheory.PolycyclicRecognition.Algebra.PolynomialModelDifference
import OAI.GroupTheory.PolycyclicRecognition.Geometry.PolynomialModelExponential
import OAI.GroupTheory.PolycyclicRecognition.Algebra.OrderedCentralWords

namespace OAI

/-! # Ordered real powers in a polynomial Lie model -/

noncomputable section
namespace PolycyclicRecognition
open Module
variable {L : Type*} [RealNormedLieAlgebra L] [FiniteDimensional ℝ L]
  [P : PolynomialExponentialCoordinates L] {d : ℕ}

def modelLineHom (v : L) : Multiplicative ℝ →* L where
  toFun t := t.toAdd • v
  map_one' := by change (0 : ℝ) • v = 1; rw [zero_smul, P.one_eq_zero]
  map_mul' s t := (PolynomialExponentialCoordinates.smul_mul v s.toAdd t.toAdd).symm

theorem model_zpow (v : L) (n : ℤ) : v ^ n = (n : ℝ) • v := by
  have h : modelLineHom v (Multiplicative.ofAdd 1) = v := one_smul ℝ v
  calc
    v ^ n = (modelLineHom v (Multiplicative.ofAdd 1)) ^ n := congrArg (fun x : L => x ^ n) h.symm
    _ = modelLineHom v ((Multiplicative.ofAdd 1) ^ n) := (map_zpow _ _ _).symm
    _ = (n : ℝ) • v := by
      change (n • (1 : ℝ)) • v = (n : ℝ) • v
      rw [zsmul_eq_mul, mul_one]

omit [FiniteDimensional ℝ L] P in
theorem IsPolynomialInBasis.coordinate_smul (b : Basis (Fin d) ℝ L)
    (i : Fin d) (v : L) : IsPolynomialInBasis b b (fun x => b.equivFun x i • v) := by
  simpa only [IsPolynomialInBasis, LinearEquiv.apply_symm_apply, map_smul] using
    (IsCoordinatePolynomial.coordinate_smul i (b.equivFun v))

theorem IsPolynomialInBasis.list_prod (b : Basis (Fin d) ℝ L) (fs : List (L → L))
    (hfs : ∀ f ∈ fs, IsPolynomialInBasis b b f) :
    IsPolynomialInBasis b b (fun x => (fs.map (fun f => f x)).prod) := by
  induction fs with
  | nil =>
    simpa only [IsPolynomialInBasis, List.map_nil, List.prod_nil, P.one_eq_zero, map_zero] using
      (IsCoordinatePolynomial.const (I := Fin d) (0 : Fin d → ℝ))
  | cons f fs ih =>
    exact (hfs f (List.mem_cons_self ..)).mul
      (ih (fun g hg => hfs g (List.mem_cons_of_mem _ hg)))

def orderedRealWord (b : Basis (Fin d) ℝ L) (X : Fin d → L) (x : L) : L :=
  (List.ofFn (fun i => b.equivFun x i • X i)).prod

theorem orderedRealWord_polynomial (b : Basis (Fin d) ℝ L) (X : Fin d → L) :
    IsPolynomialInBasis b b (orderedRealWord b X) := by
  have h := IsPolynomialInBasis.list_prod b
    (List.ofFn (fun i : Fin d => fun x : L => b.equivFun x i • X i)) (by
      intro f hf
      obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hf
      exact IsPolynomialInBasis.coordinate_smul b i (X i))
  change IsPolynomialInBasis b b (fun x => (List.ofFn (fun i => b.equivFun x i • X i)).prod)
  simpa only [List.map_ofFn, Function.comp_def] using h

theorem orderedRealWord_integer (b : Basis (Fin d) ℝ L) (X : Fin d → L)
    (z : Fin d → ℤ) :
    orderedRealWord b X (b.equivFun.symm (fun i => (z i : ℝ))) = orderedWord X z := by
  simp only [orderedRealWord, LinearEquiv.apply_symm_apply, orderedWord, model_zpow]

theorem orderedWord_map {H K : Type*} [Group H] [Group K]
    (f : H →* K) (X : Fin d → H) (z : Fin d → ℤ) :
    orderedWord (fun i => f (X i)) z = f (orderedWord X z) := by
  simp only [orderedWord, map_list_prod, List.map_ofFn, Function.comp_def, map_zpow]

end PolycyclicRecognition

end

end OAI
