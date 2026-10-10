import OAI.NumberTheory.Ostmann.Supply.KernelProducts
import OAI.NumberTheory.Ostmann.Supply.TruncatedWeight
import OAI.NumberTheory.Ostmann.Supply.UnitKernelGenerating
import OAI.NumberTheory.Ostmann.Tree.UnitSums

namespace OAI

noncomputable section
namespace Ostmann.Supply
open scoped BigOperators
open TensorOperators BivariateTruncation

theorem independent_unit_average {ι : Type*} [Fintype ι] [DecidableEq ι] (α : ι→Type*) [∀i,Fintype (α i)]
    (f : ∀i,α i→ℂ) :
    (Fintype.card (∀i,α i):ℂ)⁻¹*(∑x:∀i,α i,∏i,f i (x i)) =
      ∏i,(Fintype.card (α i):ℂ)⁻¹*(∑x:α i,f i x) := by
  rw [Finset.prod_mul_distrib,←Fintype.prod_sum,Fintype.card_pi,Nat.cast_prod,
    Finset.prod_inv_distrib]

theorem sum_units_eq_nonzero {F A : Type*} [Field F] [Fintype F] [DecidableEq F]
    [AddCommGroup A] (f : F→A) :
    (∑u:Fˣ,f u)=∑x∈Finset.univ.erase (0:F),f x := by
  apply add_right_cancel (b:=f 0)
  exact (Ostmann.FiniteField.sum_units_add_zero f).trans
    (Finset.sum_erase_add Finset.univ f (Finset.mem_univ 0)).symm

variable {ι : Type*} [Fintype ι] [DecidableEq ι] (p : ι→ℕ) [∀i,Fact (p i).Prime]
  (S : ∀i,Finset (ZMod (p i)))

def unitWeightPolynomial : (ℕ×ℕ)→₀ℂ :=
  (Fintype.card (∀i,(ZMod (p i))ˣ):ℂ)⁻¹ •
    ∑x:∀i,(ZMod (p i))ˣ,subsetPairPolynomial Finset.univ
      (fun i => (localKernel (S i) sparseKernelScale (x i):ℂ))

theorem eval_unitWeightPolynomial (u v : ℂ) :
    eval (unitWeightPolynomial p S) u v = ∏i,unitKernelGenerating (S i) sparseKernelScale u v := by
  change evalLinearMap u v _ = _
  rw [unitWeightPolynomial,map_smul,map_sum]
  simp only [evalLinearMap_apply,eval_subsetPairPolynomial,smul_eq_mul]
  rw [independent_unit_average (fun i => (ZMod (p i))ˣ)
    (fun i x => (1+u*(localKernel (S i) sparseKernelScale x:ℂ))*
      (1+v*(localKernel (S i) sparseKernelScale x:ℂ)))]
  apply Finset.prod_congr rfl
  intro i hi
  have hcard : (Fintype.card (ZMod (p i))ˣ:ℂ)=(p i:ℂ)-1 := by
    rw [ZMod.card_units,Nat.cast_sub (Fact.out : (p i).Prime).one_lt.le,Nat.cast_one]
  rw [hcard,sum_units_eq_nonzero (fun x : ZMod (p i) =>
    (1+u*(localKernel (S i) sparseKernelScale x:ℂ))*
      (1+v*(localKernel (S i) sparseKernelScale x:ℂ)))]
  exact (div_eq_inv_mul _ _).symm

theorem eval_unitWeightPolynomial_one : eval (unitWeightPolynomial p S) 1 1 =
    ((∏i,unitKernelMean (S i) sparseKernelScale:ℝ):ℂ) := by
  rw [eval_unitWeightPolynomial]
  simp only [unitKernelGenerating_one,Complex.ofReal_prod]

theorem truncation_unitWeightPolynomial :
    ∀K:ℕ,rectangularTruncation (unitWeightPolynomial p S) K =
      ((Fintype.card (∀i,(ZMod (p i))ˣ):ℝ)⁻¹*
        ∑x:∀i,(ZMod (p i))ˣ,truncatedWeight Finset.univ
          (fun i => localKernel (S i) sparseKernelScale (x i)) K:ℝ) := by
  intro K
  rw [←rectangularLinearMap_apply]
  rw [unitWeightPolynomial,map_smul,map_sum]
  simp only [rectangularLinearMap_apply,rectangularTruncation_real_subsetPairPolynomial]
  push_cast
  rfl

theorem unitWeightPolynomial_norm_uniform (u v : ℂ)
    (hlo : ∀i,(1/3:ℝ)≤density (S i)) (hhi : ∀i,density (S i)≤2/3)
    (hg : ∀i,gamma (S i) ≤ supplyEpsilon^2) (hu : ‖u‖≤103/100) (hv : ‖v‖≤103/100) :
    ‖eval (unitWeightPolynomial p S) u v‖ ≤
      Real.exp (8*supplyEpsilon*(∑i,1/(p i:ℝ))) := by
  rw [eval_unitWeightPolynomial,norm_prod]
  have h := real_prod_uniform Finset.univ
    (fun i => ‖unitKernelGenerating (S i) sparseKernelScale u v‖)
    (fun i => 8*supplyEpsilon/(p i:ℝ))
    (fun i _ => norm_nonneg _)
    (fun i _ => sparse_unitKernelGenerating_norm (S i) u v
      (Fact.out : (p i).Prime).two_le (hlo i) (hhi i) (hg i) hu hv)
  convert h using 1
  congr 1
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  ring

end Ostmann.Supply

end

end OAI
