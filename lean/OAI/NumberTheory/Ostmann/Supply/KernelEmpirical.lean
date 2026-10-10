import OAI.NumberTheory.Ostmann.Supply.KernelTruncatedWeight
import OAI.NumberTheory.Ostmann.Supply.TensorModeLocalKernel

namespace OAI

noncomputable section
namespace Ostmann.Supply
open scoped BigOperators ComplexConjugate
open TensorOperators BivariateTruncation TensorModes

variable (p : ℕ→ℕ) [∀i,NeZero (p i)] (S : ∀i,Finset (ZMod (p i)))

abbrev kernelCenteredDomain (i : ℕ) : FiniteHilbertSpace := ⟨centeredSpace (S i)ᶜ⟩
abbrev kernelCenteredCodomain (i : ℕ) : FiniteHilbertSpace := ⟨centeredSpace (S i)⟩

def kernelOutputEmpirical {α : Type*} (A : Finset α) (a : α→∀i,ZMod (p i)) (n : ℕ) :
    tensorSpace (kernelCodomain p S) n :=
  empiricalTensor (E:=kernelCenteredCodomain p S) A
    (fun x i => (centeredSpace (S i)).orthogonalProjectionOnto (EuclideanSpace.single (a x i) 1)) n

def kernelInputEmpirical {β : Type*} (B : Finset β) (b : β→∀i,ZMod (p i)) (n : ℕ) :
    tensorSpace (kernelDomain p S) n :=
  empiricalTensor (E:=kernelCenteredDomain p S) B
    (fun x i => (centeredSpace (S i)ᶜ).orthogonalProjectionOnto (EuclideanSpace.single (b x i) 1)) n

def kernelAverageWeight {α β : Type*} (A : Finset α) (B : Finset β)
    (a : α→∀i,ZMod (p i)) (b : β→∀i,ZMod (p i)) (n K : ℕ) : ℝ :=
  (A.card:ℝ)⁻¹*(B.card:ℝ)⁻¹*∑x∈A,∑y∈B,
    truncatedWeight (Finset.range n) (fun i => localKernel (S i) sparseKernelScale (a x i-b y i)) K

theorem kernelAverageWeight_nonneg {α β : Type*} (A : Finset α) (B : Finset β)
    (a : α→∀i,ZMod (p i)) (b : β→∀i,ZMod (p i)) (n K : ℕ) :
    0≤kernelAverageWeight p S A B a b n K := by
  unfold kernelAverageWeight
  exact mul_nonneg (by positivity) (Finset.sum_nonneg (fun x hx =>
    Finset.sum_nonneg (fun y hy => truncatedWeight_nonneg _ _ _)))

theorem kernelEmpirical_pairing {α β : Type*} (A : Finset α) (B : Finset β)
    (a : α→∀i,ZMod (p i)) (b : β→∀i,ZMod (p i)) (n K : ℕ)
    (ha : ∀x∈A,∀i<n,a x i∈S i) (hb : ∀y∈B,∀i<n,b y i∈(S i)ᶜ) :
    inner ℂ (kernelOutputEmpirical p S A a n)
      (rectangularTruncation (kernelTensorPolynomial p S n) K (kernelInputEmpirical p S B b n)) =
      (kernelAverageWeight p S A B a b n K:ℂ) := by
  unfold kernelOutputEmpirical kernelInputEmpirical empiricalTensor
  dsimp +instances only [kernelCenteredCodomain, kernelCenteredDomain, kernelCodomain,
    kernelDomain, augmentedSpace, LocalCoordinates, FiniteHilbertSpace.of]
  simp only [map_smul,map_sum,inner_smul_left,inner_smul_right,sum_inner,inner_sum,
    map_inv₀,map_natCast]
  rw [←Finset.mul_sum,Finset.sum_comm]
  change (B.card:ℂ)⁻¹*((A.card:ℂ)⁻¹*
    ∑x∈A,∑y∈B,inner ℂ
      (pureTensor (E:=kernelCodomain p S) (fun i => localPoint (S i) (a x i)) n)
      (rectangularTruncation (kernelTensorPolynomial p S n) K
        (pureTensor (E:=kernelDomain p S) (fun i => localPoint (S i)ᶜ (b y i)) n))) = _
  have hsum : (∑x∈A,∑y∈B,inner ℂ
      (pureTensor (E:=kernelCodomain p S) (fun i => localPoint (S i) (a x i)) n)
      (rectangularTruncation (kernelTensorPolynomial p S n) K
        (pureTensor (E:=kernelDomain p S) (fun i => localPoint (S i)ᶜ (b y i)) n))) =
      ∑x∈A,∑y∈B,(truncatedWeight (Finset.range n)
        (fun i => localKernel (S i) sparseKernelScale (a x i-b y i)) K:ℂ) := by
    apply Finset.sum_congr rfl
    intro x hx
    apply Finset.sum_congr rfl
    intro y hy
    exact kernelTruncation_point_pairing p S n K (a x) (b y) (ha x hx) (hb y hy)
  rw [hsum]
  simp only [kernelAverageWeight,Complex.ofReal_mul,Complex.ofReal_inv,Complex.ofReal_natCast,
    Complex.ofReal_sum,mul_assoc]
  ring

theorem kernelTruncation_lowMode_pairing {α β : Type*} (A : Finset α) (B : Finset β)
    (a : α→∀i,ZMod (p i)) (b : β→∀i,ZMod (p i)) (n K : ℕ)
    (hS : ∀i<n,(S i).Nonempty) (hT : ∀i<n,(S i)ᶜ.Nonempty)
    (ha : ∀x∈A,∀i<n,a x i∈S i) (hb : ∀y∈B,∀i<n,b y i∈(S i)ᶜ) :
    kernelAverageWeight p S A B a b n K ≤
      ‖rectangularTruncation (kernelTensorPolynomial p S n) K‖*
        ‖lowModes (kernelCenteredCodomain p S) n (2*K) (kernelOutputEmpirical p S A a n)‖*
        ‖lowModes (kernelCenteredDomain p S) n (2*K) (kernelInputEmpirical p S B b n)‖ := by
  have h := norm_inner_rectangularTruncation
    (E:=kernelCenteredDomain p S) (F:=kernelCenteredCodomain p S)
    (fun i => localKernelPolynomial (S i) sparseKernelScale) n K
    (fun i hi => localKernelPolynomial_zero_output (S i) sparseKernelScale (hS i hi) (hT i hi))
    (fun i hi => localKernelPolynomial_zero_input (S i) sparseKernelScale (hS i hi) (hT i hi))
    (kernelOutputEmpirical p S A a n) (kernelInputEmpirical p S B b n)
  change ‖inner ℂ (kernelOutputEmpirical p S A a n)
    (rectangularTruncation (kernelTensorPolynomial p S n) K (kernelInputEmpirical p S B b n))‖≤_ at h
  rw [kernelEmpirical_pairing p S A B a b n K ha hb,Complex.norm_real,Real.norm_eq_abs,
    abs_of_nonneg (kernelAverageWeight_nonneg p S A B a b n K)] at h
  exact h

end Ostmann.Supply

end

end OAI
