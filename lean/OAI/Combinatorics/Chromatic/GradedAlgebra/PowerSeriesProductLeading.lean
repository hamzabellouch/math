import Mathlib
import OAI.Combinatorics.Chromatic.GradedAlgebra.PowerSeriesSplitLeading

namespace OAI

section
section
namespace ElementaryPositivity.PowerSeriesSplit
open PowerSeries
noncomputable section
variable {R : Type*} [Ring R]
lemma multiply_leading_difference (f g f' g' : PowerSeries R) (n : ℕ)
    (hf : constantCoeff f=1) (hg : constantCoeff g=1)
    (hf' : constantCoeff f'=1) (hg' : constantCoeff g'=1)
    (hff : ∀k≤n,coeff k f=coeff k f') (hgg : ∀k≤n,coeff k g=coeff k g') :
    coeff (n+1) (f*g)-coeff (n+1) (f'*g')=
      (coeff (n+1) f-coeff (n+1) f')+(coeff (n+1) g-coeff (n+1) g') := by
  rw [coeff_mul_succ _ _ _ hf hg,coeff_mul_succ _ _ _ hf' hg']
  have he : (∑i : Fin n,coeff (i.val+1) f*coeff (n-i.val) g)=
      ∑i : Fin n,coeff (i.val+1) f'*coeff (n-i.val) g' := by
    apply Finset.sum_congr rfl
    intro i _
    rw [hff (i.val+1) (by omega),hgg (n-i.val) (by omega)]
  rw [he]
  abel

variable {A : Type*} (f g : A → PowerSeries R)
lemma product_constant (l : List A) (hf : ∀a∈l,constantCoeff (f a)=1) :
    constantCoeff (l.map f).prod=1 := by
  induction l with
  | nil => exact map_one _
  | cons a l ih =>
    rw [List.map_cons,List.prod_cons,map_mul,hf a List.mem_cons_self,one_mul,
      ih (fun b hb=>hf b (List.mem_cons_of_mem a hb))]

lemma product_coeff_congr (l : List A) (n : ℕ)
    (hfg : ∀a∈l,∀k≤n,coeff k (f a)=coeff k (g a)) :
    coeff n (l.map f).prod=coeff n (l.map g).prod := by
  induction l generalizing n with
  | nil => rfl
  | cons a l ih =>
    simp only [List.map_cons,List.prod_cons]
    apply FormalLog.mul_coeff_congr
    · exact hfg a List.mem_cons_self
    · intro k hk
      exact ih k (fun b hb j hj=>hfg b (List.mem_cons_of_mem a hb) j (hj.trans hk))

lemma product_leading_difference (l : List A) (n : ℕ)
    (hf : ∀a∈l,constantCoeff (f a)=1) (hg : ∀a∈l,constantCoeff (g a)=1)
    (hfg : ∀a∈l,∀k≤n,coeff k (f a)=coeff k (g a)) :
    coeff (n+1) (l.map f).prod-coeff (n+1) (l.map g).prod=
      (l.map (fun a=>coeff (n+1) (f a)-coeff (n+1) (g a))).sum := by
  induction l with
  | nil => simp only [List.map_nil,List.prod_nil,sub_self,List.sum_nil]
  | cons a l ih =>
    have hfl : ∀b∈l,constantCoeff (f b)=1:=fun b hb=>hf b (List.mem_cons_of_mem a hb)
    have hgl : ∀b∈l,constantCoeff (g b)=1:=fun b hb=>hg b (List.mem_cons_of_mem a hb)
    have hfg' : ∀b∈l,∀k≤n,coeff k (f b)=coeff k (g b):=
      fun b hb=>hfg b (List.mem_cons_of_mem a hb)
    simp only [List.map_cons,List.prod_cons,List.sum_cons]
    rw [multiply_leading_difference _ _ _ _ n (hf a List.mem_cons_self)
      (product_constant f l hfl) (hg a List.mem_cons_self) (product_constant g l hgl)
      (hfg a List.mem_cons_self) (fun k hk=>product_coeff_congr f g l k
        (fun b hb j hj=>hfg' b hb j (hj.trans hk))),ih hfl hgl hfg']
end
end ElementaryPositivity.PowerSeriesSplit
end
end

end OAI
