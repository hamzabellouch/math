import OAI.Probability.SignedSweeps.DensityComparison
import OAI.Probability.SignedSweeps.TensorSupport

namespace OAI

noncomputable section
namespace SignedSweeps
open scoped BigOperators TensorProduct
open Module
open scoped BigOperators
open scoped BigOperators ComplexOrder Classical
open scoped BigOperators TensorProduct ComplexOrder Classical

lemma missingCellFactor_nonneg {A B : Type*} [Fintype A] [Fintype B]
    (W : Finset (A × B)) : 0 ≤ missingCellFactor W :=
  Finset.prod_nonneg (fun _ _ => missingLineFactor_nonneg _ _)

end SignedSweeps
end

noncomputable section
namespace SignedSweeps
open scoped BigOperators TensorProduct
open Module
open scoped BigOperators
open scoped BigOperators ComplexOrder Classical
open scoped BigOperators TensorProduct ComplexOrder Classical
variable {A B : Type} [Fintype A] [Fintype B] [Nonempty B]
variable (E : FiniteComplexHilbert) (W : Finset (A × B)) (e : Fin W.card ≃ {x // x ∈ W})

def columnDensityTensor (R : B → E →ₗ[ℂ] E) :
    tensorHilbertPower E W.card →ₗ[ℂ] tensorHilbertPower E W.card :=
  tensorOperator E (fun k => R (e k).1.2)

def rowDensityTensor (S : A → E →ₗ[ℂ] E) :
    tensorHilbertPower E W.card →ₗ[ℂ] tensorHilbertPower E W.card :=
  tensorOperator E (fun k => S (e k).1.1)

def meanDensityTensor (R : B → E →ₗ[ℂ] E) :
    tensorHilbertPower E W.card →ₗ[ℂ] tensorHilbertPower E W.card :=
  tensorOperator E (fun _ : Fin W.card => densityMean R)

theorem tensor_one_sided_density_comparison
    {I J : Type*} [Fintype I] [Fintype J]
    (H K P : tensorHilbertPower E W.card →ₗ[ℂ] tensorHilbertPower E W.card)
    (hH : H.IsSymmetric) (hHH : H * H = H)
    (hK : K.IsSymmetric) (hKK : K * K = K)
    (hP : P.IsSymmetric) (hPP : P * P = P)
    (R : I → B → E →ₗ[ℂ] E) (hR : ∀ i j, (R i j).IsPositive)
    (S : J → A → E →ₗ[ℂ] E) (hS : ∀ j i, (S j i).IsPositive)
    (htrS : ∀ j i, (LinearMap.trace ℂ E (S j i)).re = 1)
    (w : I → ℝ) (hw : ∀ i, 0 ≤ w i) (hsumw : ∑ i, w i = 1)
    (v : J → ℝ) (hv : ∀ j, 0 ≤ v j) (hsumv : ∑ j, v j = 1)
    {a b t : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (ht : 0 ≤ t)
    (hdomH : ((a : ℂ) • (∑ i, (w i : ℂ) • columnDensityTensor E W e (R i)) - H).IsPositive)
    (hdomK : ((b : ℂ) • (∑ j, (v j : ℂ) • rowDensityTensor E W e (S j)) - K).IsPositive)
    (hTK : ∀ i, meanDensityTensor E W (R i) * K = K * meanDensityTensor E W (R i))
    (hTP : ∀ i, meanDensityTensor E W (R i) * P = P * meanDensityTensor E W (R i))
    (hglobal : ∀ i, ‖(meanDensityTensor E W (R i) * P).toContinuousLinearMap‖ ≤ t) :
    ‖(H * K * P).toContinuousLinearMap‖ ^ 2 ≤ min 1 (a * b * t * missingCellFactor W) := by
  apply one_sided_density_comparison H K P hH hHH hK hKK hP hPP
    (fun i => columnDensityTensor E W e (R i))
    (fun i => tensorOperator_positive E _ (fun k => hR i (e k).1.2))
    (fun j => rowDensityTensor E W e (S j))
    (fun j => tensorOperator_positive E _ (fun k => hS j (e k).1.1))
    w hw hsumw v hv hsumv (fun i => meanDensityTensor E W (R i))
    (fun i => tensorOperator_positive E _ (fun _ => densityMean_positive (R i) (hR i)))
    (fun i => tensor_density_right_support E W e (R i) (hR i)) hTK hTP
    ha hb ht (by exact missingCellFactor_nonneg W) hdomH hdomK hglobal
  exact fun i j => tensor_density_cell_bound E W e (R i) (hR i) (S j) (hS j) (htrS j)

end SignedSweeps
end

end OAI
