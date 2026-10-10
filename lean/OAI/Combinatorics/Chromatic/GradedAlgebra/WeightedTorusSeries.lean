import Mathlib
import OAI.Combinatorics.Chromatic.QuantumTorus.QuantumTorus
import OAI.Combinatorics.Chromatic.Shuffle.DimensionGrid

namespace OAI

section
namespace ElementaryPositivity.WeightedTorusSeries
open ElementaryPositivity.RawShuffle ElementaryPositivity.QuantumTorus
open PowerSeries
noncomputable section
universe u
variable {I : Type u} [Fintype I] [DecidableEq I]
variable (w : I → ℕ) [hw : Fact (∀i,0<w i)]

def weight : (I → ℕ) →+ ℕ where
  toFun d:=∑i,d i*w i
  map_zero':=by simp
  map_add' d e:=by simp [add_mul,Finset.sum_add_distrib]

omit [DecidableEq I] in
include hw in
lemma coord_le_weight (d : I → ℕ) (i : I) : d i≤weight w d :=
  (Nat.le_mul_of_pos_right _ (hw.out i)).trans
    (Finset.single_le_sum (fun j _=>Nat.zero_le (d j*w j)) (Finset.mem_univ i))

abbrev Slice (n : ℕ) := {d : I → ℕ // weight w d=n}
instance sliceFinite (n : ℕ) : Finite (Slice w n) :=
  Finite.of_injective (fun d : Slice w n=>fun i=>(⟨d.val i,by
    have H:=coord_le_weight w d.val i
    rw [d.property] at H
    omega⟩ : Fin (n+1))) (fun x y h=>Subtype.ext (funext (fun i=>congrArg Fin.val (congrArg (fun f=>f i) h))))

noncomputable instance sliceFintype (n : ℕ) : Fintype (Slice w n) := Fintype.ofFinite _

omit [Fintype I] [DecidableEq I] in
private lemma split_heq {d e : I → ℕ} {s : DimensionSplit d} {t : DimensionSplit e}
    (H : d=e) (hs : s.left=t.left) : HEq s t := by
  cases H
  exact heq_of_eq (DimensionSplit.ext hs)

def splitSliceEquiv (n : ℕ) :
    (Σ d : Slice w n,DimensionSplit d.val) ≃
      {p : (I→ℕ)×(I→ℕ) // weight w p.1+weight w p.2=n} where
  toFun x:=⟨(x.2.left,x.2.right),by rw [←map_add,DimensionSplit.left_add_right]; exact x.1.property⟩
  invFun p:=⟨⟨p.val.1+p.val.2,by rw [map_add,p.property]⟩,DimensionSplit.ofPair _ _ rfl⟩
  left_inv x:=by
    apply Sigma.ext (Subtype.ext (DimensionSplit.left_add_right x.2))
    exact split_heq (DimensionSplit.left_add_right x.2) rfl
  right_inv p:=by apply Subtype.ext; simp

def pairSliceEquiv (n : ℕ) :
    (Σ k : Fin (n+1),Slice w k.val × Slice w (n-k.val)) ≃
      {p : (I→ℕ)×(I→ℕ) // weight w p.1+weight w p.2=n} where
  toFun x:=⟨(x.2.1.val,x.2.2.val),by rw [x.2.1.property,x.2.2.property]; omega⟩
  invFun p:=⟨⟨weight w p.val.1,by have H:=p.property; omega⟩,⟨p.val.1,rfl⟩,
    ⟨p.val.2,by dsimp only; have H:=p.property; omega⟩⟩
  left_inv x:=by
    rcases x with ⟨⟨k,hk⟩,⟨d,hd⟩,⟨e,he⟩⟩
    dsimp only at hd he ⊢
    subst k
    rfl
  right_inv p:=rfl

lemma sum_split {A : Type*} [AddCommMonoid A] (n : ℕ) (H : (I→ℕ) → (I→ℕ) → A) :
    (∑d : Slice w n,∑s : DimensionSplit d.val,H s.left s.right)=
      ∑k : Fin (n+1),∑d : Slice w k.val,∑e : Slice w (n-k.val),H d.val e.val := by
  classical
  let E := (splitSliceEquiv w n).trans (pairSliceEquiv w n).symm
  calc
    _ = ∑x : (Σ d : Slice w n,DimensionSplit d.val),H x.2.left x.2.right :=
      (Fintype.sum_sigma (fun x : (Σ d : Slice w n,DimensionSplit d.val)=>H x.2.left x.2.right)).symm
    _ = ∑y : (Σ k : Fin (n+1),Slice w k.val × Slice w (n-k.val)),H y.2.1.val y.2.2.val :=
      Fintype.sum_equiv E _ _ (fun _=>rfl)
    _ = _ := by
      rw [Fintype.sum_sigma]
      apply Finset.sum_congr rfl
      intro k hk
      exact Fintype.sum_prod_type _

variable {R M : Type*} [CommRing R] [AddCommGroup M]
variable (v : Rˣ) (Ω : M →+ M →+ ℤ) (P : (I → ℕ) →+ M)
local instance : Ring (Torus v Ω) := Torus.instRing v Ω
local instance : AddCommMonoid (Torus v Ω) := (Torus.instRing v Ω).toAddCommMonoid
local instance : AddGroup (Torus v Ω) := (Torus.instRing v Ω).toAddGroup

def pushCoeff (f : (I→ℕ) → R) (n : ℕ) : Torus v Ω :=
  ∑d : Slice w n,Torus.monomial v Ω (P d.val) (f d.val)
def push (f : (I→ℕ) → R) : PowerSeries (Torus v Ω) := mk (pushCoeff w v Ω P f)

def convolution (f g : (I→ℕ) → R) (d : I→ℕ) : R :=
  ∑s : DimensionSplit d,f s.left*g s.right*↑(v^(Ω (P s.left) (P s.right)))

lemma monomial_sum {A : Type*} (s : Finset A) (m : M) (f : A → R) :
    Torus.monomial v Ω m (∑i∈s,f i)=∑i∈s,Torus.monomial v Ω m (f i) := by
  exact map_sum (Finsupp.singleAddHom m) f s

lemma torus_sum_mul {A : Type*} (s : Finset A) (f : A → Torus v Ω) (g : Torus v Ω) :
    (∑i∈s,f i)*g=∑i∈s,f i*g := by
  classical
  induction s using Finset.induction_on with
  | empty => simp only [Finset.sum_empty,Torus.zero_mul]
  | @insert a s ha ih => simp only [Finset.sum_insert ha,Torus.add_mul,ih]

lemma torus_mul_sum {A : Type*} (s : Finset A) (f : A → Torus v Ω) (g : Torus v Ω) :
    g*(∑i∈s,f i)=∑i∈s,g*f i := by
  classical
  induction s using Finset.induction_on with
  | empty => simp only [Finset.sum_empty,Torus.mul_zero]
  | @insert a s ha ih => simp only [Finset.sum_insert ha,Torus.mul_add,ih]

lemma pushCoeff_convolution (f g : (I→ℕ) → R) (n : ℕ) :
    pushCoeff w v Ω P (convolution v Ω P f g) n=
      ∑k : Fin (n+1),pushCoeff w v Ω P f k.val*pushCoeff w v Ω P g (n-k.val) := by
  classical
  simp only [pushCoeff,convolution,monomial_sum,torus_sum_mul,torus_mul_sum,
    Torus.monomial_mul_monomial]
  have H:=sum_split w n (fun d e=>Torus.monomial v Ω (P d+P e)
    (f d*g e*↑(v^(Ω (P d) (P e)))))
  convert H using 1
  · apply Finset.sum_congr rfl
    intro d hd
    apply Finset.sum_congr rfl
    intro s hs
    rw [←map_add,DimensionSplit.left_add_right]
  · apply Finset.sum_congr rfl
    intro k hk
    exact Finset.sum_comm

lemma push_convolution (f g : (I→ℕ) → R) :
    push w v Ω P (convolution v Ω P f g)=push w v Ω P f*push w v Ω P g := by
  apply PowerSeries.ext
  intro n
  simp only [push,coeff_mk,coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk,←Fin.sum_univ_eq_sum_range]
  exact pushCoeff_convolution w v Ω P f g n

end
end ElementaryPositivity.WeightedTorusSeries

end

end OAI
