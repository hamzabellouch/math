import OAI.NumberTheory.Ostmann.Supply.ContractingKernel

namespace OAI

noncomputable section
namespace Ostmann.Supply
open scoped BigOperators

def kernelUnitProduct {ι : Type*} (P : Finset ι) (p : ι→ℕ) [∀i,NeZero (p i)]
    (S : ∀i,Finset (ZMod (p i))) : ℝ :=
  ∏i∈P,unitKernelMean (S i) sparseKernelScale

def reciprocalMass {ι : Type*} (P : Finset ι) (p : ι→ℕ) : ℝ :=
  ∑i∈P,1/(p i:ℝ)

theorem kernelUnitProduct_pos {ι : Type*} (P : Finset ι) (p : ι→ℕ) [∀i,NeZero (p i)]
    (S : ∀i,Finset (ZMod (p i))) (hp : ∀i∈P,1000≤p i)
    (hlo : ∀i∈P,(1/3:ℝ)≤density (S i)) (hhi : ∀i∈P,density (S i)≤2/3)
    (hg : ∀i∈P,gamma (S i)≤ supplyEpsilon^2) : 0<kernelUnitProduct P p S := by
  apply Finset.prod_pos
  intro i hi
  exact sparse_unitKernelMean_pos (S i) (by have := hp i hi; omega)
    sparseKernelScale_nonneg sparseKernelScale_le_one
    (by linarith [hlo i hi]) (by linarith [hhi i hi]) (hg i hi)

theorem real_prod_contraction {ι : Type*} (P : Finset ι) (f U r : ι→ℝ)
    (hf : ∀i∈P,0≤f i) (hU : ∀i∈P,0≤U i)
    (hbound : ∀i∈P,f i≤U i*(1-r i)) :
    (∏i∈P,f i) ≤ (∏i∈P,U i)*Real.exp (-(∑i∈P,r i)) := by
  calc
    _ ≤ ∏i∈P,U i*Real.exp (-r i) := by
      apply Finset.prod_le_prod₀ hf
      intro i hi
      exact (hbound i hi).trans (mul_le_mul_of_nonneg_left
        (by simpa [sub_eq_add_neg,add_comm] using Real.add_one_le_exp (-r i)) (hU i hi))
    _ = _ := by rw [Finset.prod_mul_distrib,←Real.exp_sum,Finset.sum_neg_distrib]

theorem real_prod_uniform {ι : Type*} (P : Finset ι) (f r : ι→ℝ)
    (hf : ∀i∈P,0≤f i) (hbound : ∀i∈P,f i≤1+r i) :
    (∏i∈P,f i) ≤ Real.exp (∑i∈P,r i) := by
  calc
    _ ≤ ∏i∈P,Real.exp (r i) := Finset.prod_le_prod₀ hf
      (fun i hi => (hbound i hi).trans (by simpa [add_comm] using Real.add_one_le_exp (r i)))
    _ = _ := (Real.exp_sum P r).symm

theorem localKernel_norm_product_contraction {ι : Type*} (P : Finset ι)
    (p : ι→ℕ) [∀i,NeZero (p i)] (S : ∀i,Finset (ZMod (p i)))
    (hp : ∀i∈P,1000≤p i) (hlo : ∀i∈P,(1/3:ℝ)≤density (S i))
    (hhi : ∀i∈P,density (S i)≤2/3) (hg : ∀i∈P,gamma (S i)≤ supplyEpsilon^2) :
    (∏i∈P,‖localKernelBlock (S i) sparseKernelScale 1 1‖) ≤
      kernelUnitProduct P p S*Real.exp (-(8/5:ℝ)*reciprocalMass P p) := by
  have h := real_prod_contraction P
    (fun i => ‖localKernelBlock (S i) sparseKernelScale 1 1‖)
    (fun i => unitKernelMean (S i) sparseKernelScale) (fun i => (8/5:ℝ)/(p i:ℝ))
    (fun i hi => ContinuousLinearMap.opNorm_nonneg (localKernelBlock (S i) sparseKernelScale 1 1))
    (fun i hi => (sparse_unitKernelMean_pos (S i) (by have := hp i hi; omega)
      sparseKernelScale_nonneg sparseKernelScale_le_one
      (by linarith [hlo i hi]) (by linarith [hhi i hi]) (hg i hi)).le)
    (fun i hi => local_sparse_contraction (S i) (hp i hi) (hlo i hi) (hhi i hi) (hg i hi))
  convert h using 1
  unfold kernelUnitProduct reciprocalMass
  congr 2
  rw [Finset.mul_sum,←Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  ring

theorem localKernel_norm_product_uniform {ι : Type*} (P : Finset ι)
    (p : ι→ℕ) [∀i,NeZero (p i)] (S : ∀i,Finset (ZMod (p i))) (u v : ℂ)
    (hp : ∀i∈P,1000≤p i) (hlo : ∀i∈P,(1/3:ℝ)≤density (S i))
    (hhi : ∀i∈P,density (S i)≤2/3) (hg : ∀i∈P,gamma (S i)≤ supplyEpsilon^2)
    (hu : ‖u‖≤103/100) (hv : ‖v‖≤103/100) :
    (∏i∈P,‖localKernelBlock (S i) sparseKernelScale u v‖) ≤
      Real.exp (3*reciprocalMass P p) := by
  have h := real_prod_uniform P
    (fun i => ‖localKernelBlock (S i) sparseKernelScale u v‖) (fun i => 3/(p i:ℝ))
    (fun i hi => ContinuousLinearMap.opNorm_nonneg (localKernelBlock (S i) sparseKernelScale u v))
    (fun i hi => local_sparse_uniform_bound (S i) u v (hp i hi) (hlo i hi) (hhi i hi) (hg i hi) hu hv)
  convert h using 1
  congr 1
  unfold reciprocalMass
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  ring

end Ostmann.Supply

end

end OAI
