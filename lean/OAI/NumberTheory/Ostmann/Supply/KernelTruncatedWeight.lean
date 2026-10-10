import OAI.NumberTheory.Ostmann.Supply.KernelTensor
import OAI.NumberTheory.Ostmann.Supply.TruncatedWeight

namespace OAI

noncomputable section
namespace Ostmann.Supply
open scoped BigOperators
open TensorOperators BivariateTruncation

def operatorPairing {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F] (x : F) (y : E) :
    (E→L[ℂ]F)→ₗ[ℂ]ℂ where
  toFun K := inner ℂ x (K y)
  map_add' K L := by simp
  map_smul' c K := by simp

variable (p : ℕ→ℕ) [∀i,NeZero (p i)] (S : ∀i,Finset (ZMod (p i)))

theorem kernelTruncation_point_pairing (n K : ℕ)
    (a b : ∀i,ZMod (p i)) (ha : ∀i<n,a i∈S i) (hb : ∀i<n,b i∈(S i)ᶜ) :
    inner ℂ (pureTensor (E:=kernelCodomain p S) (fun i => localPoint (S i) (a i)) n)
      (rectangularTruncation (kernelTensorPolynomial p S n) K
        (pureTensor (E:=kernelDomain p S) (fun i => localPoint (S i)ᶜ (b i)) n)) =
      (truncatedWeight (Finset.range n)
        (fun i => localKernel (S i) sparseKernelScale (a i-b i)) K:ℂ) := by
  let x := pureTensor (E:=kernelCodomain p S) (fun i => localPoint (S i) (a i)) n
  let y := pureTensor (E:=kernelDomain p S) (fun i => localPoint (S i)ᶜ (b i)) n
  change operatorPairing x y (rectangularTruncation (kernelTensorPolynomial p S n) K)=_
  rw [←rectangularTruncation_mapCoefficients]
  apply rectangularTruncation_eq_weight
  intro u v
  rw [eval_mapCoefficients,eval_kernelTensorPolynomial]
  exact kernelTensor_point_pairing p S n u v a b ha hb

theorem kernelTruncation_error (n K : ℕ)
    (hp : ∀i<n,1000≤p i) (hlo : ∀i<n,(1/3:ℝ)≤density (S i))
    (hhi : ∀i<n,density (S i)≤2/3) (hg : ∀i<n,gamma (S i) ≤ supplyEpsilon^2) :
    ‖rectangularTruncation (kernelTensorPolynomial p S n) K-kernelTensor p S n 1 1‖ ≤
      2*Real.exp (3*reciprocalMass (Finset.range n) p)*((103/100:ℝ)⁻¹)^K /
        (1-(103/100:ℝ)⁻¹)^2 := by
  rw [←eval_kernelTensorPolynomial]
  apply rectangularTruncation_error_le _ (by norm_num : (1:ℝ)<103/100)
  intro u v hu hv
  rw [eval_kernelTensorPolynomial]
  exact kernelTensor_norm_uniform p S n u v hp hlo hhi hg hu.le hv.le

theorem kernelTruncation_norm (n K : ℕ)
    (hp : ∀i<n,1000≤p i) (hlo : ∀i<n,(1/3:ℝ)≤density (S i))
    (hhi : ∀i<n,density (S i)≤2/3) (hg : ∀i<n,gamma (S i) ≤ supplyEpsilon^2) :
    ‖rectangularTruncation (kernelTensorPolynomial p S n) K‖ ≤
      kernelUnitProduct (Finset.range n) p S*Real.exp (-(8/5:ℝ)*reciprocalMass (Finset.range n) p)+
      2*Real.exp (3*reciprocalMass (Finset.range n) p)*((103/100:ℝ)⁻¹)^K /
        (1-(103/100:ℝ)⁻¹)^2 := by
  have h := norm_le_norm_sub_add (rectangularTruncation (kernelTensorPolynomial p S n) K)
    (kernelTensor p S n 1 1)
  have htail := kernelTruncation_error p S n K hp hlo hhi hg
  have hfull := kernelTensor_norm_contraction p S n hp hlo hhi hg
  linarith

end Ostmann.Supply

end

end OAI
