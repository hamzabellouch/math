import OAI.Combinatorics.EuclideanRamsey.FiniteEuclidean

namespace OAI

universe uGroup uIndex

noncomputable section

open scoped TensorProduct RealInnerProductSpace
open scoped BigOperators
open Real Filter Topology MeasureTheory Polynomial
open Matrix MeasureTheory
open MeasureTheory
open Matrix
open scoped MatrixOrder Matrix.Norms.L2Operator
open MeasureTheory Matrix
open scoped TensorProduct
open scoped BigOperators Pointwise Topology
open MeasureTheory Filter
open scoped BigOperators Pointwise
open scoped BigOperators Topology
open scoped TensorProduct BigOperators
open scoped BigOperators MatrixOrder Matrix.Norms.L2Operator
open scoped BigOperators RealInnerProductSpace

open scoped BigOperators
namespace EuclideanRamsey
section Fractions
variable {G : Type uGroup} {ι : Type uIndex} [Group G] [DecidableEq ι]

def RightFraction (M : Submonoid (ι → G)) (z : ι → G) : Prop :=
  ∃ u ∈ M,∃ v ∈ M,z=u*v⁻¹

def HasDiagonal (M : Submonoid (ι → G)) : Prop := ∀ g : G,(fun _ => g)∈M

def PairInverse (M : Submonoid (ι → G)) : Prop :=
  ∀ i j : ι,i≠j → ∀ v∈M,∃ b∈M,v i*b i=1 ∧ v j*b j=1

omit [DecidableEq ι] in
lemma RightFraction.one (M : Submonoid (ι → G)) : RightFraction M 1 :=
  ⟨1,M.one_mem,1,M.one_mem,by simp⟩
omit [DecidableEq ι] in
lemma RightFraction.inv {M : Submonoid (ι → G)} {z : ι → G}
    (h : RightFraction M z) : RightFraction M z⁻¹ := by
  obtain ⟨u,hu,v,hv,rfl⟩ := h
  exact ⟨v,hv,u,hu,by group⟩
omit [DecidableEq ι] in
lemma RightFraction.conjugate {M : Submonoid (ι → G)} (hM : HasDiagonal M)
    {z : ι → G} (h : RightFraction M z) (g : G) :
    RightFraction M (fun i => g*z i*g⁻¹) := by
  obtain ⟨u,hu,v,hv,rfl⟩ := h
  refine ⟨(fun _ => g)*u,M.mul_mem (hM g) hu,(fun _ => g)*v,M.mul_mem (hM g) hv,?_⟩
  ext i
  simp only [Pi.mul_apply,Pi.inv_apply]
  group

lemma conjugate_single (i : ι) (g h : G) :
    (fun j => g*(Pi.mulSingle i h : ι → G) j*g⁻¹)=Pi.mulSingle i (g*h*g⁻¹) := by
  ext j
  by_cases hj : j=i <;> simp [hj]

lemma RightFraction.mul_single {M : Submonoid (ι → G)} (hM : HasDiagonal M)
    {z : ι → G} (hz : RightFraction M z) (i : ι) {g : G}
    (hg : RightFraction M (Pi.mulSingle i g)) : RightFraction M (z*Pi.mulSingle i g) := by
  obtain ⟨u,hu,v,hv,rfl⟩ := hz
  have hh := hg.conjugate hM (v i)⁻¹
  rw [conjugate_single,inv_inv] at hh
  obtain ⟨a,ha,b,hb,he⟩ := hh
  refine ⟨u*a,M.mul_mem hu ha,v*b,M.mul_mem hv hb,?_⟩
  have ht : v⁻¹*Pi.mulSingle i g = Pi.mulSingle i ((v i)⁻¹*g*v i)*v⁻¹ := by
    ext j
    by_cases hj : j=i
    · subst j; simp
    · simp [Pi.mulSingle_eq_of_ne hj]
  rw [mul_assoc,ht,he]
  group

def singleFractions (M : Submonoid (ι → G)) (hM : HasDiagonal M) (i : ι) : Subgroup G where
  carrier := {g | RightFraction M (Pi.mulSingle i g)}
  one_mem' := by simpa using RightFraction.one M
  mul_mem' {a b} ha hb := by
    change RightFraction M (Pi.mulSingle i (a*b))
    rw [Pi.mulSingle_mul]
    exact ha.mul_single hM i hb
  inv_mem' {a} ha := by
    change RightFraction M (Pi.mulSingle i a⁻¹)
    rw [Pi.mulSingle_inv]
    exact ha.inv

instance singleFractions_normal (M : Submonoid (ι → G)) (hM : HasDiagonal M) (i : ι) :
    (singleFractions M hM i).Normal where
  conj_mem g hg k := by
    change RightFraction M (Pi.mulSingle i (k*g*k⁻¹))
    rw [← conjugate_single]
    exact hg.conjugate hM k

lemma RightFraction.mul_pair {M : Submonoid (ι → G)} (hM : PairInverse M)
    {z t : ι → G} (hz : RightFraction M z) (ht : RightFraction M t)
    (i j : ι) (hij : i≠j) (hs : ∀ l,l≠i → l≠j → t l=1) :
    RightFraction M (z*t) := by
  obtain ⟨u,hu,v,hv,rfl⟩ := hz
  obtain ⟨c,hc,d,hd,rfl⟩ := ht
  obtain ⟨b,hb,hi,hj⟩ := hM i j hij v hv
  have hcomm : Commute (v*b) (c*d⁻¹) := by
    ext l
    by_cases hli : l=i
    · subst l; simp only [Pi.mul_apply,Pi.inv_apply] at *; rw [hi]; simp
    by_cases hlj : l=j
    · subst l; simp only [Pi.mul_apply,Pi.inv_apply] at *; rw [hj]; simp
    · have hh := hs l hli hlj
      change v l*b l*(c l*(d l)⁻¹) = (c l*(d l)⁻¹)*(v l*b l)
      change c l*(d l)⁻¹=1 at hh
      rw [hh]; simp
  refine ⟨u*b*c,M.mul_mem (M.mul_mem hu hb) hc,(v*b)*d,M.mul_mem (M.mul_mem hv hb) hd,?_⟩
  have he : u*v⁻¹ = (u*b)*(v*b)⁻¹ := by group
  rw [he,mul_assoc,hcomm.inv_left.eq]
  group
end Fractions
end EuclideanRamsey
namespace EuclideanRamsey
open scoped BigOperators
variable {G : Type uGroup} {ι : Type uIndex} [Group G] [DecidableEq ι]

structure GradedPaths (ι : Type uIndex) (G : Type uGroup) [Group G] where
  Holds : (ι → G) → ℕ → Prop
  diag : ∀ g,Holds (fun _ => g) 0
  mul : ∀ {u v m n},Holds u m → Holds v n → Holds (u*v) (m+n)
namespace GradedPaths
variable (P : GradedPaths ι G)
def monoid : Submonoid (ι → G) where
  carrier := {u | ∃ n,P.Holds u n}
  one_mem' := ⟨0,P.diag 1⟩
  mul_mem' := by rintro u v ⟨m,hm⟩ ⟨n,hn⟩; exact ⟨m+n,P.mul hm hn⟩
omit [DecidableEq ι] in
lemma diagonal : HasDiagonal P.monoid := fun g => ⟨0,P.diag g⟩

def BoundedFraction (z : ι → G) (c : ℕ) : Prop :=
  ∃ (u v : ι → G) (m n : ℕ),P.Holds u m ∧ P.Holds v n ∧ z=u*v⁻¹ ∧ m+n≤c
omit [DecidableEq ι] in
lemma bounded_exists {z : ι → G} (h : RightFraction P.monoid z) :
    ∃ c,P.BoundedFraction z c := by
  obtain ⟨u,⟨m,hm⟩,v,⟨n,hn⟩,he⟩ := h
  exact ⟨m+n,u,v,m,n,hm,hn,he,le_rfl⟩
omit [DecidableEq ι] in
lemma bounded_fraction {z : ι → G} {c : ℕ} (h : P.BoundedFraction z c) :
    RightFraction P.monoid z := by
  obtain ⟨u,v,m,n,hm,hn,he,_⟩ := h
  exact ⟨u,⟨m,hm⟩,v,⟨n,hn⟩,he⟩
omit [DecidableEq ι] in
lemma bounded_one : P.BoundedFraction 1 0 :=
  ⟨1,1,0,0,P.diag 1,P.diag 1,by simp,le_rfl⟩
omit [DecidableEq ι] in
lemma bounded_mono {z : ι → G} {c d : ℕ} (h : P.BoundedFraction z c) (hc : c≤d) :
    P.BoundedFraction z d := by
  obtain ⟨u,v,m,n,hm,hn,he,hc'⟩ := h
  exact ⟨u,v,m,n,hm,hn,he,hc'.trans hc⟩
omit [DecidableEq ι] in
lemma bounded_inv {z : ι → G} {c : ℕ} (h : P.BoundedFraction z c) :
    P.BoundedFraction z⁻¹ c := by
  obtain ⟨u,v,m,n,hm,hn,rfl,hc⟩ := h
  exact ⟨v,u,n,m,hn,hm,by group,by omega⟩
omit [DecidableEq ι] in
lemma bounded_conjugate {z : ι → G} {c : ℕ} (h : P.BoundedFraction z c) (g : G) :
    P.BoundedFraction (fun i => g*z i*g⁻¹) c := by
  obtain ⟨u,v,m,n,hm,hn,rfl,hc⟩ := h
  refine ⟨(fun _ => g)*u,(fun _ => g)*v,m,n,?_,?_,?_,hc⟩
  · simpa using P.mul (P.diag g) hm
  · simpa using P.mul (P.diag g) hn
  · ext i; simp only [Pi.mul_apply,Pi.inv_apply]; group
lemma bounded_mul_single {z : ι → G} {c d : ℕ} (hz : P.BoundedFraction z c)
    (i : ι) {g : G} (hg : P.BoundedFraction (Pi.mulSingle i g) d) :
    P.BoundedFraction (z*Pi.mulSingle i g) (c+d) := by
  obtain ⟨u,v,m,n,hm,hn,rfl,hc⟩ := hz
  have hh := P.bounded_conjugate hg (v i)⁻¹
  rw [conjugate_single,inv_inv] at hh
  obtain ⟨a,b,k,l,hk,hl,he,hd⟩ := hh
  refine ⟨u*a,v*b,m+k,n+l,P.mul hm hk,P.mul hn hl,?_,by omega⟩
  have ht : v⁻¹*Pi.mulSingle i g = Pi.mulSingle i ((v i)⁻¹*g*v i)*v⁻¹ := by
    ext j
    by_cases hj : j=i
    · subst j; simp
    · simp [Pi.mulSingle_eq_of_ne hj]
  rw [mul_assoc,ht,he]
  group

def singleCost (i : ι) (g : G) : ℕ := sInf {c | P.BoundedFraction (Pi.mulSingle i g) c}
lemma singleCost_bounded (i : ι) {g : G} (hg : g∈singleFractions P.monoid P.diagonal i) :
    P.BoundedFraction (Pi.mulSingle i g) (P.singleCost i g) :=
  Nat.sInf_mem (P.bounded_exists hg)
lemma singleCost_le (i : ι) {g : G} {c : ℕ} (hc : P.BoundedFraction (Pi.mulSingle i g) c) :
    P.singleCost i g ≤ c := Nat.sInf_le hc
lemma singleCost_one (i : ι) : P.singleCost i 1=0 := by
  apply Nat.eq_zero_of_le_zero
  apply P.singleCost_le
  simpa using P.bounded_one
lemma singleCost_inv (i : ι) {g : G} (hg : g∈singleFractions P.monoid P.diagonal i) :
    P.singleCost i g⁻¹=P.singleCost i g := by
  apply Nat.le_antisymm
  · apply P.singleCost_le
    rw [Pi.mulSingle_inv]
    exact P.bounded_inv (P.singleCost_bounded i hg)
  · apply P.singleCost_le
    have he := P.bounded_inv (P.singleCost_bounded i ((singleFractions _ _ i).inv_mem hg))
    simpa only [Pi.mulSingle_inv,inv_inv] using he
lemma singleCost_conjugate (i : ι) {g : G} (hg : g∈singleFractions P.monoid P.diagonal i) (k : G) :
    P.singleCost i (k*g*k⁻¹)=P.singleCost i g := by
  have hle {g : G} (hg : g∈singleFractions P.monoid P.diagonal i) (k : G) :
      P.singleCost i (k*g*k⁻¹) ≤ P.singleCost i g := by
    apply P.singleCost_le
    rw [← conjugate_single]
    exact P.bounded_conjugate (P.singleCost_bounded i hg) k
  apply Nat.le_antisymm (hle hg k)
  have he := hle ((singleFractions_normal P.monoid P.diagonal i).conj_mem g hg k) k⁻¹
  simpa only [inv_inv,inv_mul_cancel_left,mul_assoc,mul_inv_cancel_right,inv_mul_cancel,mul_one] using he
lemma singleCost_mul (i : ι) {g h : G}
    (hg : g∈singleFractions P.monoid P.diagonal i) (hh : h∈singleFractions P.monoid P.diagonal i) :
    P.singleCost i (g*h)≤P.singleCost i g+P.singleCost i h := by
  apply P.singleCost_le
  rw [Pi.mulSingle_mul]
  exact P.bounded_mul_single (P.singleCost_bounded i hg) i (P.singleCost_bounded i hh)

lemma bounded_tuple_list (l : List ι) (z : ι → G) (c : ι → ℕ)
    (h : ∀ i∈l,P.BoundedFraction (Pi.mulSingle i (z i)) (c i)) :
    P.BoundedFraction ((l.map (fun i => Pi.mulSingle i (z i))).prod) ((l.map c).sum) := by
  induction l with
  | nil => simpa using P.bounded_one
  | cons i l ih =>
    have ht := (P.bounded_mul_single (ih (by intro j hj; exact h j (by simp [hj]))) i (h i (by simp)))
    have he : (l.map (fun j => Pi.mulSingle j (z j))).prod*Pi.mulSingle i (z i)=
        Pi.mulSingle i (z i)*(l.map (fun j => Pi.mulSingle j (z j))).prod := by
      apply Commute.symm
      apply Commute.list_prod_right
      intro y hy
      obtain ⟨j,_,rfl⟩ := List.mem_map.mp hy
      by_cases hji : j=i
      · subst j; exact Commute.refl _
      · ext k
        by_cases hki : k=i
        · subst k; simp [Pi.mulSingle_eq_of_ne (Ne.symm hji)]
        · simp [Pi.mulSingle_eq_of_ne hki]
    simpa [he,Nat.add_comm] using ht
end GradedPaths
end EuclideanRamsey

end

end OAI
