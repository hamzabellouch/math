import OAI.GroupTheory.PolycyclicRecognition.Algebra.CollinearDynkin
import OAI.GroupTheory.PolycyclicRecognition.Algebra.PolynomialGroupLaws
import Mathlib.Analysis.Calculus.Deriv.Pi

namespace OAI

/-! # Local BCH parameters without an exponential bijection

The basis-input BCH polynomial is smooth and has derivative the identity
at zero. Its derivative follows from the one-coordinate restrictions,
already determined by the actual exponential curves.
-/

noncomputable section
namespace PolycyclicRecognition

open Module
open scoped ContDiff

variable {L : Type*} [LieRing L] [LieAlgebra ℝ L] {c n : ℕ}

def basisDynkinParameter (coeff : DynkinCoefficients c n) (b : Basis (Fin n) ℝ L)
    (x : Fin n → ℝ) : Fin n → ℝ :=
  bilinearDynkinPolynomial coeff (basisBracket b) (fun i => b.equivFun (x i • b i))

theorem basisDynkinParameter_eq (coeff : DynkinCoefficients c n)
    (b : Basis (Fin n) ℝ L) (x : Fin n → ℝ) :
    basisDynkinParameter coeff b x =
      b.equivFun (finiteDynkinPolynomial coeff (fun i => x i • b i)) := by
  unfold basisDynkinParameter bilinearDynkinPolynomial finiteDynkinPolynomial
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro d _
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro w _
  rw [evalBilinearWord_basisBracket, map_smul]

theorem contDiff_basisDynkinParameter (coeff : DynkinCoefficients c n)
    (b : Basis (Fin n) ℝ L) : ContDiff ℝ ∞ (basisDynkinParameter coeff b) := by
  have hX : ∀ i : Fin n, ContDiff ℝ ∞
      (fun x : Fin n → ℝ => b.equivFun (x i • b i)) := by
    intro i
    let d : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ) :=
      (ContinuousLinearMap.proj i).smulRight (b.equivFun (b i))
    have heq : (fun x : Fin n → ℝ => b.equivFun (x i • b i)) = d := by
      funext x
      exact map_smul b.equivFun (x i) (b i)
    rw [heq]
    exact d.contDiff

  exact contDiff_bilinearDynkinPolynomial coeff
    (fun _ : Fin n → ℝ => basisBracket b)
    (fun (x : Fin n → ℝ) i => b.equivFun (x i • b i)) contDiff_const hX

@[simp] theorem basisDynkinParameter_zero (coeff : DynkinCoefficients c n)
    (b : Basis (Fin n) ℝ L) : basisDynkinParameter coeff b 0 = 0 := by
  rw [basisDynkinParameter_eq]
  simp only [Pi.zero_apply, zero_smul]
  exact (congrArg b.equivFun (finiteDynkinPolynomial_zero coeff)).trans (map_zero _)

open scoped Manifold

variable {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace G] [ChartedSpace E G] [Group G]
  [LieGroup (𝓘(ℝ, E)) ⊤ G]

theorem basisDynkinParameter_single_of_product
    {Exp : GroupLieAlgebra (𝓘(ℝ, E)) G → G} (hExp : IsGroupExponential Exp)
    (coeff : DynkinCoefficients c n)
    (hprod : ∀ X : Fin n → GroupLieAlgebra (𝓘(ℝ, E)) G,
      (List.ofFn (fun i => Exp (X i))).prod = Exp (finiteDynkinPolynomial coeff X))
    (b : Basis (Fin n) ℝ (GroupLieAlgebra (𝓘(ℝ, E)) G)) (i : Fin n) (s : ℝ) :
    basisDynkinParameter coeff b (Pi.single i s) = Pi.single i s := by
  classical
  have heq : (fun j => (Pi.single i s : Fin n → ℝ) j • b j) = Pi.single i (s • b i) := by
    funext j
    by_cases h : j = i <;> simp [h]
  rw [basisDynkinParameter_eq, heq,
    finiteDynkinPolynomial_single_of_product hExp coeff hprod]
  ext j
  simp only [map_smul, Pi.smul_apply, smul_eq_mul, Basis.equivFun_self]
  by_cases h : i = j <;> simp [h, eq_comm]

theorem hasFDerivAt_basisDynkinParameter_zero
    {Exp : GroupLieAlgebra (𝓘(ℝ, E)) G → G} (hExp : IsGroupExponential Exp)
    (coeff : DynkinCoefficients c n)
    (hprod : ∀ X : Fin n → GroupLieAlgebra (𝓘(ℝ, E)) G,
      (List.ofFn (fun i => Exp (X i))).prod = Exp (finiteDynkinPolynomial coeff X))
    (b : Basis (Fin n) ℝ (GroupLieAlgebra (𝓘(ℝ, E)) G)) :
    HasFDerivAt (basisDynkinParameter coeff b) (ContinuousLinearMap.id ℝ (Fin n → ℝ)) 0 := by
  have hd := (contDiff_basisDynkinParameter coeff b).differentiable (by simp)
  have hcol (i : Fin n) : fderiv ℝ (basisDynkinParameter coeff b) 0 (Pi.single i 1) =
      Pi.single i 1 := by
    have hh := (hd 0).hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ)
      (hasDerivAt_single i (0 : ℝ)) (by simp)
    have heq : (fun s : ℝ => basisDynkinParameter coeff b (Pi.single i s)) =
        fun s => (Pi.single i s : Fin n → ℝ) := by
      funext s
      exact basisDynkinParameter_single_of_product hExp coeff hprod b i s
    change HasDerivAt (fun s : ℝ => basisDynkinParameter coeff b (Pi.single i s)) _ 0 at hh
    rw [heq] at hh
    exact hh.unique (hasDerivAt_single i (0 : ℝ))
  apply (hd 0).hasFDerivAt.congr_fderiv
  apply ContinuousLinearMap.ext
  intro x
  change fderiv ℝ (basisDynkinParameter coeff b) 0 x = x
  calc
    _ = fderiv ℝ (basisDynkinParameter coeff b) 0 (∑ i, x i • Pi.single i 1) :=
      congrArg _ (pi_eq_sum_univ' x)
    _ = ∑ i, x i • Pi.single i 1 := by simp only [map_sum, map_smul, hcol]
    _ = x := (pi_eq_sum_univ' x).symm

end PolycyclicRecognition

end

end OAI
