import Mathlib
import OAI.Combinatorics.SumProduct.Alignment.RationalLattice12
import OAI.Combinatorics.SumProduct.Alignment.RationalLattice13
import OAI.Geometry.NilpotentCharts.Main

namespace OAI

section
section
noncomputable section
open _root_.Polynomial _root_.OAI.Polynomial
open scoped BigOperators
end
 
end

section
 

noncomputable section
open scoped BigOperators
namespace WeightedPolynomial
open MvPolynomial
variable {σ : Type*}

def Bounded (w : σ → ℕ) (d : ℕ) (p : MvPolynomial σ ℝ) : Prop :=
  ∀ m,p.coeff m≠0 → Finsupp.weight w m ≤ d

def rayTable (w : σ → ℕ) : MvPolynomial σ ℝ →+* Polynomial (MvPolynomial σ ℝ) :=
  eval₂Hom (Polynomial.C.comp C)
    (fun i=>Polynomial.C (X i)*Polynomial.X^(w i))

lemma rayTable_monomial (w : σ → ℕ) (m : σ →₀ ℕ) (a : ℝ) :
    rayTable w (monomial m a)=Polynomial.monomial (Finsupp.weight w m) (monomial m a) := by
  change eval₂ (Polynomial.C.comp C) _ _=_
  rw [eval₂_monomial]
  simp only [RingHom.comp_apply,mul_pow,← pow_mul,Finsupp.prod_mul]
  have hC : m.prod (fun i e=>(Polynomial.C (X i))^e)=
      Polynomial.C (m.prod (fun i e=>(X i : MvPolynomial σ ℝ)^e)) := by
    simp only [Finsupp.prod,map_prod,map_pow]
  have hX : m.prod (fun i e=>(Polynomial.X : Polynomial (MvPolynomial σ ℝ))^(w i*e))=
      Polynomial.X^(Finsupp.weight w m) := by
    simp only [Finsupp.prod,Finset.prod_pow_eq_pow_sum,Finsupp.weight_apply,Finsupp.sum,
      smul_eq_mul]
    congr 1
    apply Finset.sum_congr rfl
    intro i hi
    exact Nat.mul_comm _ _
  rw [hC,hX,← mul_assoc,← map_mul,← monomial_eq,Polynomial.C_mul_X_pow_eq_monomial]

lemma coeff_rayTable (w : σ → ℕ) (p : MvPolynomial σ ℝ) (k : ℕ) (m : σ →₀ ℕ) :
    ((rayTable w p).coeff k).coeff m=if Finsupp.weight w m=k then p.coeff m else 0 := by
  classical
  induction p using MvPolynomial.induction_on' with
  | monomial l a =>
    rw [rayTable_monomial]
    simp only [Polynomial.coeff_monomial,apply_ite,MvPolynomial.coeff_monomial,
      AddMonoidAlgebra.coeff_zero]
    by_cases hl : l=m
    · subst l; split_ifs <;> simp_all
    · split_ifs <;> simp [hl]
  | add p q hp hq =>
    simp only [map_add,Polynomial.coeff_add,AddMonoidAlgebra.coeff_add,Finsupp.add_apply,hp,hq]
    split_ifs <;> simp

def ray (w : σ → ℕ) (x : σ → ℝ) (p : MvPolynomial σ ℝ) : Polynomial ℝ :=
  (rayTable w p).map (eval x)

def scale (w : σ → ℕ) (t : ℝ) (x : σ → ℝ) (i : σ) : ℝ := t^(w i)*x i

lemma ray_C (w : σ → ℕ) (x : σ → ℝ) (a : ℝ) :
    ray w x (C a)=Polynomial.C a := by simp [ray,rayTable]
lemma ray_X (w : σ → ℕ) (x : σ → ℝ) (i : σ) :
    ray w x (X i)=Polynomial.C (x i)*Polynomial.X^(w i) := by simp [ray,rayTable]
lemma ray_mul (w : σ → ℕ) (x : σ → ℝ) (p q : MvPolynomial σ ℝ) :
    ray w x (p*q)=ray w x p*ray w x q := by simp only [ray,map_mul,Polynomial.map_mul]
lemma ray_add (w : σ → ℕ) (x : σ → ℝ) (p q : MvPolynomial σ ℝ) :
    ray w x (p+q)=ray w x p+ray w x q := by simp only [ray,map_add,Polynomial.map_add]

lemma ray_eval (w : σ → ℕ) (x : σ → ℝ) (p : MvPolynomial σ ℝ) (t : ℝ) :
    (ray w x p).eval t=eval (scale w t x) p := by
  induction p using MvPolynomial.induction_on with
  | C a => simp only [ray_C,Polynomial.eval_C,eval_C]
  | add p q hp hq => simp only [ray_add,Polynomial.eval_add,map_add,hp,hq]
  | mul_X p i hp =>
    rw [ray_mul,ray_X,Polynomial.eval_mul,Polynomial.eval_mul,Polynomial.eval_C,
      Polynomial.eval_pow,Polynomial.eval_X,hp,map_mul,eval_X]
    simp only [scale]
    ring

lemma bounded_iff_ray (w : σ → ℕ) (d : ℕ) (p : MvPolynomial σ ℝ) :
    Bounded w d p ↔ ∀ x,(ray w x p).natDegree ≤ d := by
  constructor
  · intro hp x
    apply Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
    intro k hk
    simp only [ray,Polynomial.coeff_map]
    have he : (rayTable w p).coeff k=0 := by
      ext m
      rw [coeff_rayTable]
      by_cases hm : Finsupp.weight w m=k
      · rw [ite_eq_left hm]
        by_contra hc
        have hh:=hp m hc
        omega
      · rw [ite_eq_right hm]
        rfl
    rw [he,map_zero]
  · intro hp m hm
    by_contra hd
    have he : (rayTable w p).coeff (Finsupp.weight w m)=0 := by
      apply MvPolynomial.funext
      intro x
      have h:=Polynomial.coeff_eq_zero_of_natDegree_lt
        (lt_of_le_of_lt (hp x) (Nat.lt_of_not_ge hd))
      simpa only [ray,Polynomial.coeff_map,map_zero] using h
    have hh:=congrArg (fun poly : MvPolynomial σ ℝ=>poly.coeff m) he
    simp only [coeff_rayTable,AddMonoidAlgebra.coeff_zero,Finsupp.zero_apply] at hh
    exact hm hh

end WeightedPolynomial
end
 
end

section
 

noncomputable section
open _root_.Polynomial _root_.OAI.Polynomial
open scoped BigOperators
namespace RationalLattice
open CubeFaces CubePolynomials MalcevCharacters WeightedPolynomial
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable {n : ℕ} (c : RealCoordinates G n) (hsk : SecondKind c)
variable (H : Filtration G) (w : Fin n → ℕ)
variable (hH : ∀ k (g : G),g∈H.level k ↔ ∀ i : Fin n,w i < k → c.coord g i=0)

include hsk hH in
omit [IsTopologicalGroup G] in
lemma scale_path_mem (x : Fin n → ℝ) :
    (fun t : ℝ=>c.coord.symm (scale w t x))∈polynomials H 0 := by
  let V : List (ℝ → G):=List.ofFn (fun i : Fin n=>fun t : ℝ=>axis c i ((monomial (w i) (x i)).eval t))
  have hV : V.prod∈polynomials H 0 := by
    apply (polynomials H 0).list_prod_mem
    intro f hf
    obtain ⟨i,rfl⟩:=List.mem_ofFn.mp hf
    exact axis_polynomial_mem c hsk H w hH i _ (natDegree_monomial_le _)
  have he : V.prod=(fun t : ℝ=>c.coord.symm (scale w t x)) := by
    funext t
    let ev : (ℝ → G) →* G := Pi.evalMonoidHom (fun _ : ℝ=>G) t
    have hh:=ev.map_list_prod V
    change V.prod t=(V.map (fun f=>f t)).prod at hh
    rw [hh]
    dsimp only [V]
    rw [List.map_ofFn]
    symm
    convert hsk.ordered (c.coord.symm (scale w t x)) using 1
    congr 2
    funext i
    simp [scale,mul_comm]
  rwa [he] at hV

include hsk hH in
omit [IsTopologicalGroup G] in
lemma coordinate_weighted {σ : Type*} (ws : σ → ℕ) (f : (σ → ℝ) → G)
    (hpoly : IsRealPolynomialMap c f)
    (hf : ∀ x,(fun t : ℝ=>f (scale ws t x))∈polynomials H 0) (i : Fin n) :
    ∃ p : MvPolynomial σ ℝ,Bounded ws (w i) p ∧ ∀ x,c.coord (f x) i=MvPolynomial.eval x p := by
  choose p hp using hpoly
  refine ⟨p i,?_,hp i⟩
  apply (bounded_iff_ray ws (w i) (p i)).mpr
  intro x
  exact coordinate_natDegree c hsk H w hH (fun t=>f (scale ws t x)) (hf x)
    (fun j=>ray ws x (p j)) (fun t j=>by rw [ray_eval,← hp]) i

include hsk hH in
 

theorem multiplication_weighted (i : Fin n) :
    ∃ p : MvPolynomial (Fin n ⊕ Fin n) ℝ,
      Bounded (Sum.elim w w) (w i) p ∧
      ∀ x,c.coord (c.coord.symm (fun j=>x (Sum.inl j))*c.coord.symm (fun j=>x (Sum.inr j))) i=
        MvPolynomial.eval x p := by
  apply coordinate_weighted c hsk H w hH (Sum.elim w w)
  · apply realPolynomialMap_mul
    · intro j
      simpa only [Homeomorph.apply_symm_apply] using RealPolynomialMap.coordinate (Sum.inl j)
    · intro j
      simpa only [Homeomorph.apply_symm_apply] using RealPolynomialMap.coordinate (Sum.inr j)
  · intro x
    exact (polynomials H 0).mul_mem
      (scale_path_mem c hsk H w hH (fun j=>x (Sum.inl j)))
      (scale_path_mem c hsk H w hH (fun j=>x (Sum.inr j)))

end RationalLattice
end
 
end

section
 

noncomputable section
open _root_.Polynomial _root_.OAI.Polynomial
namespace WeightedPolynomial
variable {σ : Type*}

def coeffPolynomial (p : Polynomial (MvPolynomial σ ℝ)) (m : σ →₀ ℕ) : Polynomial ℝ :=
  p.sum (fun k a=>monomial k (a.coeff m))

lemma coeffPolynomial_add (p q : Polynomial (MvPolynomial σ ℝ)) (m : σ →₀ ℕ) :
    coeffPolynomial (p+q) m=coeffPolynomial p m+coeffPolynomial q m := by
  apply Polynomial.sum_add_index
  · intro i; simp
  · intro i a b; simp

lemma coeffPolynomial_monomial (k : ℕ) (a : MvPolynomial σ ℝ) (m : σ →₀ ℕ) :
    coeffPolynomial (monomial k a) m=monomial k (a.coeff m) := by
  simp [coeffPolynomial,Polynomial.sum_monomial_index]

lemma coeff_coeffPolynomial (p : Polynomial (MvPolynomial σ ℝ)) (m : σ →₀ ℕ) (k : ℕ) :
    (coeffPolynomial p m).coeff k=(p.coeff k).coeff m := by
  induction p using Polynomial.induction_on' with
  | monomial l a =>
    rw [coeffPolynomial_monomial]
    simp only [coeff_monomial]
    split_ifs <;> simp
  | add p q hp hq =>
    simp only [coeffPolynomial_add,coeff_add,AddMonoidAlgebra.coeff_add,Finsupp.add_apply,hp,hq]

lemma eval_coeffPolynomial (p : Polynomial (MvPolynomial σ ℝ)) (m : σ →₀ ℕ) (t : ℝ) :
    (coeffPolynomial p m).eval t=(p.eval (MvPolynomial.C t)).coeff m := by
  induction p using Polynomial.induction_on' with
  | monomial k a =>
    rw [coeffPolynomial_monomial]
    simp only [eval_monomial,← map_pow,mul_comm a,MvPolynomial.coeff_C_mul,mul_comm (a.coeff m)]
  | add p q hp hq =>
    simp only [coeffPolynomial_add,eval_add,AddMonoidAlgebra.coeff_add,Finsupp.add_apply,hp,hq]

 

lemma bounded_coeff_of_nat_evals (w : σ → ℕ) (d : ℕ)
    (p : Polynomial (MvPolynomial σ ℝ))
    (hp : ∀ a : ℕ,Bounded w d (p.eval (MvPolynomial.C (a:ℝ)))) (k : ℕ) :
    Bounded w d (p.coeff k) := by
  intro m hm
  by_contra hd
  have he : coeffPolynomial p m=0 := by
    apply Polynomial.eq_of_eval_nat_eq
    intro a
    rw [eval_zero,eval_coeffPolynomial]
    by_contra ha
    exact hd (hp a m ha)
  have hh:=congrArg (fun q : Polynomial ℝ=>q.coeff k) he
  rw [coeff_coeffPolynomial,coeff_zero] at hh
  exact hm hh

end WeightedPolynomial
end
 
end

end

end OAI
