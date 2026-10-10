import Mathlib
import OAI.Probability.SKGap.Matrix.FockTensor

namespace OAI

section

noncomputable section
open scoped BigOperators
namespace SKGap.Noncrossing.Primary.Tensor.Loop
open Diagram InverseDiagram WordSeries
variable {ι : Type*} [Fintype ι]

lemma blockDegree_reverse (bs : List Bool) : blockDegree bs.reverse=blockDegree bs := by
  simp [blockDegree,List.map_reverse]
def blockReverse (n : ℕ) : Blocks n ≃ Blocks n where
  toFun bs := ⟨bs.val.reverse,by rw [blockDegree_reverse]; exact bs.property⟩
  invFun bs := ⟨bs.val.reverse,by rw [blockDegree_reverse]; exact bs.property⟩
  left_inv bs := Subtype.ext (List.reverse_reverse bs.val)
  right_inv bs := Subtype.ext (List.reverse_reverse bs.val)

def blockPrepend (n : ℕ) : Blocks (n+1) ⊕ Blocks n → Blocks (n+2)
  | .inl bs => ⟨true::bs.val,by rw [blockDegree_true,bs.property]⟩
  | .inr bs => ⟨false::bs.val,by rw [blockDegree_false,bs.property]⟩
lemma blockPrepend_bijective (n : ℕ) : Function.Bijective (blockPrepend n) := by
  constructor
  · intro x y h
    have hv := congrArg (fun q : Blocks (n+2) => q.val) h
    cases x <;> cases y <;> simp only [blockPrepend] at hv
    · exact congrArg Sum.inl (Subtype.ext (List.cons.inj hv).2)
    · exact False.elim (Bool.noConfusion (List.cons.inj hv).1)
    · exact False.elim (Bool.noConfusion (List.cons.inj hv).1)
    · exact congrArg Sum.inr (Subtype.ext (List.cons.inj hv).2)
  · rintro ⟨bs,hbs⟩
    cases bs with
    | nil => simp only [blockDegree_nil] at hbs; omega
    | cons b bs =>
      cases b with
      | true => exact ⟨.inl ⟨bs,by rw [blockDegree_true] at hbs; omega⟩,rfl⟩
      | false => exact ⟨.inr ⟨bs,by rw [blockDegree_false] at hbs; omega⟩,rfl⟩

def blockSnocEquiv (n : ℕ) : Blocks (n+1) ⊕ Blocks n ≃ Blocks (n+2) :=
  ((blockReverse (n+1)).sumCongr (blockReverse n)).trans
    ((Equiv.ofBijective (blockPrepend n) (blockPrepend_bijective n)).trans (blockReverse (n+2)))
@[simp] lemma blockSnocEquiv_inl (n : ℕ) (bs : Blocks (n+1)) :
    (blockSnocEquiv n (.inl bs)).val=bs.val++[true] := by
  change (true::bs.val.reverse).reverse=bs.val++[true]
  simp
@[simp] lemma blockSnocEquiv_inr (n : ℕ) (bs : Blocks n) :
    (blockSnocEquiv n (.inr bs)).val=bs.val++[false] := by
  change (false::bs.val.reverse).reverse=bs.val++[false]
  simp

lemma sum_blocks_snoc {M : Type*} [AddCommMonoid M] (n : ℕ) (f : List Bool→M) :
    (∑ bs : Blocks (n+2),f bs.val)=
      (∑ bs : Blocks (n+1),f (bs.val++[true]))+(∑ bs : Blocks n,f (bs.val++[false])) := by
  have h := Fintype.sum_equiv (blockSnocEquiv n)
    (fun s => match s with | .inl bs => f (bs.val++[true]) | .inr bs => f (bs.val++[false]))
    (fun bs => f bs.val) (by intro s; cases s <;> simp)
  exact h.symm.trans (Fintype.sum_sum_type _)

lemma blocks_one (bs : Blocks 1) : bs.val=[true] := by
  have h := (mem_blockEnumerate bs.val 1).mpr bs.property
  simpa [blockEnumerate] using h
instance blocksOneUnique : Unique (Blocks 1) where
  default := ⟨[true],rfl⟩
  uniq bs := Subtype.ext (blocks_one bs)

def kernel (j : ℝ) (a : ι→ℝ) (n : ℕ) : Space (ι:=ι)→ₗ[ℝ] Space (ι:=ι) :=
  ∑ bs : Blocks n,word j (chain j a bs.val)
lemma kernel_zero (j : ℝ) (a : ι→ℝ) : kernel j a 0=LinearMap.id := by
  simp [kernel,blocks_zero,word]
lemma kernel_one (j : ℝ) (a : ι→ℝ) : kernel j a 1=(diagonal a).comp (noise j) := by
  simp [kernel,blocks_one,word,letter]
lemma kernel_add_two (j : ℝ) (a : ι→ℝ) (n : ℕ) :
    kernel j a (n+2)=(kernel j a (n+1)).comp ((diagonal a).comp (noise j))-
      (j*Diagram.mean a) • (kernel j a n).comp (diagonal a) := by
  refine (sum_blocks_snoc n (fun bs => word j (chain j a bs))).trans ?_
  simp only [chain_append,chain_true,chain_false,chain_nil,word_append,word,letter,
    LinearMap.comp_id,diagonal_scale,LinearMap.comp_smul]
  ext v i I
  simp [kernel,LinearMap.sum_apply,LinearMap.comp_apply,Finset.sum_neg_distrib,
    ←Finset.mul_sum,sub_eq_add_neg]

lemma project_kernel_zero_creation (j : ℝ) (a p : ι→ℝ) (v : Space (ι:=ι)) :
    project (kernel j a 0 (diagonal p (creation v)))=0 := by
  rw [kernel_zero]; exact project_diagonal_creation p v

lemma project_kernel_creation (j : ℝ) (a : ι→ℝ) (n : ℕ) (v : Space (ι:=ι)) :
    project (kernel j a (n+1) (diagonal a (creation v)))=
      (j*Diagram.mean a) • project (kernel j a n (diagonal a v)) := by
  induction n generalizing v with
  | zero =>
    simp only [kernel_one,kernel_zero,LinearMap.comp_apply,LinearMap.id_apply,noise,
      LinearMap.add_apply,LinearMap.smul_apply,map_add,map_smul,
      annihilation_diagonal_creation,project_diagonal_creation,zero_add,smul_smul]
  | succ n ih =>
    rw [show n+1+1=n+2 by omega,kernel_add_two]
    simp only [LinearMap.sub_apply,LinearMap.comp_apply,LinearMap.smul_apply,noise,
      LinearMap.add_apply,annihilation_diagonal_creation,map_add,map_sub,map_smul,
      smul_smul]
    rw [ih]
    abel

lemma project_kernel_incoming (j : ℝ) (a p : ι→ℝ) (n : ℕ) (v : Space (ι:=ι)) :
    project (kernel j a (n+1) (diagonal p (creation v)))=
      (j*Diagram.mean p) • project (kernel j a n (diagonal a v)) := by
  cases n with
  | zero =>
    simp only [kernel_one,kernel_zero,LinearMap.comp_apply,LinearMap.id_apply,noise,
      LinearMap.add_apply,LinearMap.smul_apply,map_add,map_smul,
      annihilation_diagonal_creation,project_diagonal_creation,zero_add,smul_smul]
  | succ n =>
    rw [show n+1+1=n+2 by omega,kernel_add_two]
    simp only [LinearMap.sub_apply,LinearMap.comp_apply,LinearMap.smul_apply,noise,
      LinearMap.add_apply,annihilation_diagonal_creation,map_add,map_sub,map_smul,
      smul_smul]
    rw [project_kernel_creation]
    abel
end SKGap.Noncrossing.Primary.Tensor.Loop

end
end

end OAI
