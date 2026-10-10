import OAI.NumberTheory.Ostmann.Supply.KernelProducts
import OAI.NumberTheory.Ostmann.Supply.LocalKernelPolynomial

namespace OAI

noncomputable section
namespace Ostmann.Supply
open scoped BigOperators ComplexConjugate
open TensorOperators

variable (p : ℕ→ℕ) [∀i,NeZero (p i)] (S : ∀i,Finset (ZMod (p i)))

abbrev kernelDomain (i : ℕ) : FiniteHilbertSpace :=
  ⟨LocalCoordinates (S i)ᶜ⟩

abbrev kernelCodomain (i : ℕ) : FiniteHilbertSpace :=
  ⟨LocalCoordinates (S i)⟩

def kernelTensor (n : ℕ) (u v : ℂ) :
    tensorSpace (kernelDomain p S) n →L[ℂ] tensorSpace (kernelCodomain p S) n :=
  tensorOp (E:=kernelDomain p S) (F:=kernelCodomain p S) (fun i => localKernelBlock (S i) sparseKernelScale u v) n

def kernelTensorPolynomial (n : ℕ) :
    (ℕ×ℕ) →₀ (tensorSpace (kernelDomain p S) n →L[ℂ] tensorSpace (kernelCodomain p S) n) :=
  tensorFamilyPolynomial (E:=kernelDomain p S) (F:=kernelCodomain p S) (fun i => localKernelPolynomial (S i) sparseKernelScale) n

theorem eval_kernelTensorPolynomial (n : ℕ) (u v : ℂ) :
    BivariateTruncation.eval (kernelTensorPolynomial p S n) u v = kernelTensor p S n u v := by
  unfold kernelTensorPolynomial kernelTensor
  rw [eval_tensorFamilyPolynomial]
  congr 1
  funext i
  exact eval_localKernelPolynomial (S i) sparseKernelScale u v

theorem kernelTensor_norm_contraction (n : ℕ)
    (hp : ∀i<n,1000≤p i) (hlo : ∀i<n,(1/3:ℝ)≤density (S i))
    (hhi : ∀i<n,density (S i)≤2/3) (hg : ∀i<n,gamma (S i)≤ supplyEpsilon^2) :
    ‖kernelTensor p S n 1 1‖ ≤ kernelUnitProduct (Finset.range n) p S*
      Real.exp (-(8/5:ℝ)*reciprocalMass (Finset.range n) p) := by
  apply (norm_tensorOp_le (E:=kernelDomain p S) (F:=kernelCodomain p S) (fun i => localKernelBlock (S i) sparseKernelScale 1 1) n).trans
  exact localKernel_norm_product_contraction (Finset.range n) p S
    (fun i hi => hp i (Finset.mem_range.mp hi))
    (fun i hi => hlo i (Finset.mem_range.mp hi))
    (fun i hi => hhi i (Finset.mem_range.mp hi))
    (fun i hi => hg i (Finset.mem_range.mp hi))

theorem kernelTensor_norm_uniform (n : ℕ) (u v : ℂ)
    (hp : ∀i<n,1000≤p i) (hlo : ∀i<n,(1/3:ℝ)≤density (S i))
    (hhi : ∀i<n,density (S i)≤2/3) (hg : ∀i<n,gamma (S i)≤ supplyEpsilon^2)
    (hu : ‖u‖≤103/100) (hv : ‖v‖≤103/100) :
    ‖kernelTensor p S n u v‖ ≤ Real.exp (3*reciprocalMass (Finset.range n) p) := by
  apply (norm_tensorOp_le (E:=kernelDomain p S) (F:=kernelCodomain p S) (fun i => localKernelBlock (S i) sparseKernelScale u v) n).trans
  exact localKernel_norm_product_uniform (Finset.range n) p S u v
    (fun i hi => hp i (Finset.mem_range.mp hi))
    (fun i hi => hlo i (Finset.mem_range.mp hi))
    (fun i hi => hhi i (Finset.mem_range.mp hi))
    (fun i hi => hg i (Finset.mem_range.mp hi)) hu hv

theorem kernelTensor_point_pairing (n : ℕ) (u v : ℂ)
    (a b : ∀i,ZMod (p i)) (ha : ∀i<n,a i∈S i) (hb : ∀i<n,b i∈(S i)ᶜ) :
    inner ℂ (pureTensor (E:=kernelCodomain p S) (fun i => localPoint (S i) (a i)) n)
      (kernelTensor p S n u v
        (pureTensor (E:=kernelDomain p S) (fun i => localPoint (S i)ᶜ (b i)) n)) =
      ∏i∈Finset.range n,
        ((1+u*(localKernel (S i) sparseKernelScale (a i-b i):ℂ))*
          (1+v*(localKernel (S i) sparseKernelScale (a i-b i):ℂ))) := by
  unfold kernelTensor
  rw [tensorOp_pureTensor,pureTensor_inner]
  apply Finset.prod_congr rfl
  intro i hi
  exact localKernelBlock_point_pairing (S i) sparseKernelScale u v (a i) (b i)
    (ha i (Finset.mem_range.mp hi)) (hb i (Finset.mem_range.mp hi))

end Ostmann.Supply

end

end OAI
