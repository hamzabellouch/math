import OAI.Analysis.FreeEntropy.MixedGaussianSeries

namespace OAI

noncomputable section
namespace FiniteEntropySeparation
open Finset FreeSeries
namespace FreeSeries
variable {n : ℕ}

def heatCoefficients (u : ℝ) (a : Fin (n+n)) (b : Fin n) : ℂ :=
  Fin.addCases (fun i => if i=b then 1 else 0)
    (fun i => if i=b then (Real.sqrt u : ℂ) else 0) a
@[simp] theorem heatCoefficients_left (u : ℝ) (a b : Fin n) :
    heatCoefficients u (leftIndex a) b = if a=b then 1 else 0 := Fin.addCases_left a
@[simp] theorem heatCoefficients_right (u : ℝ) (a b : Fin n) :
    heatCoefficients u (rightIndex a) b = if a=b then (Real.sqrt u : ℂ) else 0 := Fin.addCases_right a
 theorem heatCoefficients_R (u : ℝ) (hu : 0 ≤ u) (R : Series (Fin n)) :
    reparam (heatCoefficients u) (gaussianJointR R) = R + (u : ℂ) • quadratic := by
  rw [gaussianJointR, reparam_add, reparam_liftSeries, reparam_liftSeries]
  simp only [heatCoefficients_left, heatCoefficients_right, reparam_identity, reparam_scalar_quadratic]
  congr 2
  exact_mod_cast Real.sq_sqrt hu
end FreeSeries

namespace FreeTensor
variable {B N G : Type} [Group G] [DecidableEq B] [DecidableEq N] [DecidableEq G]
variable {n : ℕ}
 theorem heat_linear_tuple (X : Fin n → Space B N G →L[ℂ] Space B N G)
    (σ : Fin n → N) (u : ℝ) :
    (fun i => ∑ j, heatCoefficients u j i • jointTuple X σ j) =
      heatTuple X (fun i => semicircularN (σ i)) u := by
  funext i
  rw [Fin.sum_univ_add]
  change (∑ j : Fin n, heatCoefficients u (leftIndex j) i • jointTuple X σ (leftIndex j)) +
    (∑ j : Fin n, heatCoefficients u (rightIndex j) i • jointTuple X σ (rightIndex j)) = _
  simp only [heatCoefficients_left, heatCoefficients_right, jointTuple_left,
    jointTuple_right, ite_smul, one_smul,
    zero_smul ℂ (A := Space B N G →L[ℂ] Space B N G), Finset.sum_ite_eq',
    Finset.mem_univ, ite_true, heatTuple]

theorem heat_moments_cumulants (J : Set N)
    (X : Fin n → Space B N G →L[ℂ] Space B N G) (hX : ∀ i, X i ∈ backgroundAlgebra J)
    (σ : Fin n → N) (hσ : Function.Injective σ) (hs : ∀ i, σ i ∉ J)
    (u : ℝ) (hu : 0 ≤ u) :
    wordMoment (tracialVector B N G) (heatTuple X (fun i => semicircularN (σ i)) u) =
      moments (cumulants (wordMoment (tracialVector B N G) X) + (u : ℂ) • quadratic) := by
  rw [← heat_linear_tuple X σ u, ← reparam_wordMoment,
    joint_moments_cumulants J X hX σ hσ hs,
    reparam_moments (heatCoefficients u) (gaussianJointR_nil _ (cumulants_nil _)),
    heatCoefficients_R u hu]
 theorem heat_cumulants (J : Set N)
    (X : Fin n → Space B N G →L[ℂ] Space B N G) (hX : ∀ i, X i ∈ backgroundAlgebra J)
    (σ : Fin n → N) (hσ : Function.Injective σ) (hs : ∀ i, σ i ∉ J)
    (u : ℝ) (hu : 0 ≤ u) :
    cumulants (wordMoment (tracialVector B N G) (heatTuple X (fun i => semicircularN (σ i)) u)) =
      cumulants (wordMoment (tracialVector B N G) X) + (u : ℂ) • quadratic := by
  let R := cumulants (wordMoment (tracialVector B N G) X) + (u : ℂ) • quadratic
  have hR : R [] = 0 := by simp [R]
  rw [heat_moments_cumulants J X hX σ hσ hs u hu]
  exact (cumulants_unique (moments_nil _) (moments_eq hR)).symm
end FreeTensor
end FiniteEntropySeparation

end

end OAI
