import Mathlib
import OAI.Combinatorics.SumProduct.Alignment.DenseBox01
import OAI.Geometry.NilpotentCharts.Main

namespace OAI

section
section
section
section
noncomputable section
end
end
 

 
section
noncomputable section
open scoped BigOperators
open _root_.Polynomial _root_.OAI.Polynomial
namespace CorrectedBoxLeibman
abbrev Grid := IntegerGridInterpolation.Grid

def realBasis (s : ℕ) (t : Fin (s+1)) : ℝ[X] :=
  Lagrange.basis Finset.univ (fun j : Fin (s+1) => (j.val:ℝ)) t

lemma nat_nodes_injective (s : ℕ) : Set.InjOn (fun j : Fin (s+1) => (j.val:ℝ))
    (↑(Finset.univ : Finset (Fin (s+1))) : Set (Fin (s+1))) := by
  intro a _ b _ h
  apply Fin.ext
  exact_mod_cast (show (a.val : ℝ) = (b.val : ℝ) from h)

lemma realBasis_degree (s : ℕ) (t : Fin (s+1)) : (realBasis s t).natDegree ≤ s := by
  simp only [realBasis,Lagrange.natDegree_basis (nat_nodes_injective s) (Finset.mem_univ t),
    Finset.card_univ,Fintype.card_fin,Nat.add_sub_cancel_right,le_refl]

lemma interpolate_real (s : ℕ) (P : ℝ[X]) (hP : P.natDegree ≤ s) (x : ℝ) :
    P.eval x = ∑ t : Fin (s+1), P.eval (t.val:ℝ)*(realBasis s t).eval x := by
  have hd : P.degree < (Finset.univ : Finset (Fin (s+1))).card := by
    apply lt_of_le_of_lt Polynomial.degree_le_natDegree
    simp only [Finset.card_univ, Fintype.card_fin, Nat.cast_lt]
    exact Nat.lt_succ_of_le hP
  have he := congrArg (fun P : ℝ[X] => P.eval x)
    (Lagrange.eq_interpolate (nat_nodes_injective s) hd)
  simpa only [Lagrange.interpolate_apply,eval_finsetSum,eval_mul,eval_C,realBasis] using he

 

def gridEval {v s : ℕ} (a : Grid v s→ℝ) (x : Fin v→ℝ) : ℝ :=
  ∑ e, a e*∏ i, x i^(e i).val

 
def LinePolynomial (v s : ℕ) (f : (Fin v→ℤ)→ℝ) : Prop :=
  ∀ x q : Fin v→ℤ, ∃ P : ℝ[X], P.natDegree ≤ s ∧
    ∀ z : ℤ, P.eval (z:ℝ)=f (fun i => x i+z*q i)

lemma tensor_interpolation (v s : ℕ) (f : (Fin v→ℤ)→ℝ) (hf : LinePolynomial v s f)
    (x : Fin v→ℤ) :
    f x = ∑ t : Grid v s, f (fun i => ((t i).val:ℤ))*
      ∏ i, (realBasis s (t i)).eval (x i:ℝ) := by
  classical
  induction v with
  | zero =>
    simp only [Fintype.prod_empty, mul_one, Fintype.sum_unique]
    congr 1
    ext i
    exact Fin.elim0 i
  | succ v ih =>
    let b : Fin (v+1)→ℤ := Fin.cons 0 (fun i => x i.succ)
    let q : Fin (v+1)→ℤ := Fin.cons 1 (fun _ => 0)
    obtain ⟨P,hP,he⟩ := hf b q
    have hline (z : ℤ) : P.eval (z:ℝ)=f (Fin.cons z (fun i => x i.succ)) := by
      rw [he]
      congr 1
      ext i
      refine Fin.cases ?_ (fun j => ?_) i <;> simp [b,q]
    have hhead : f x=∑ t : Fin (s+1), f (Fin.cons (t.val:ℤ) (fun i => x i.succ))*
        (realBasis s t).eval (x 0:ℝ) := by
      have ht := interpolate_real s P hP (x 0:ℝ)
      rw [hline] at ht
      simp_rw [← Int.cast_natCast (R:=ℝ),hline] at ht
      have hx : Fin.cons (x 0) (fun i => x i.succ)=x := by
        ext i
        exact Fin.cases rfl (fun _ => rfl) i
      rw [hx] at ht
      exact ht
    rw [hhead]
    have htail (t : Fin (s+1)) : LinePolynomial v s (fun y => f (Fin.cons (t.val:ℤ) y)) := by
      intro y z
      obtain ⟨Q,hQ,hQe⟩ := hf (Fin.cons (t.val:ℤ) y) (Fin.cons 0 z)
      refine ⟨Q,hQ,?_⟩
      intro a
      rw [hQe]
      congr 1
      ext i
      refine Fin.cases ?_ (fun j => ?_) i <;> simp
    simp_rw [ih _ (htail _) (fun i => x i.succ),Finset.sum_mul]
    rw [← Fintype.sum_prod_type' ]
    apply Fintype.sum_equiv (Fin.consEquiv (fun _ : Fin (v+1) => Fin (s+1)))
    intro p
    simp only [Fin.consEquiv_apply,Fin.prod_univ_succ,Fin.cons_zero,Fin.cons_succ]
    have heq : (fun i => (((Fin.cons p.1 p.2 : Fin (v+1)→Fin (s+1)) i).val:ℤ))=
        Fin.cons (p.1.val:ℤ) (fun i => ((p.2 i).val:ℤ)) := by
      ext i
      exact Fin.cases rfl (fun _ => rfl) i
    rw [heq]
    ring

 

theorem exists_grid_expansion (v s : ℕ) (f : (Fin v→ℤ)→ℝ) (hf : LinePolynomial v s f) :
    ∃ a : Grid v s→ℝ, ∀ x : Fin v→ℤ, gridEval a (fun i => (x i:ℝ))=f x := by
  classical
  let a : Grid v s→ℝ := fun e => ∑ t : Grid v s, f (fun i => ((t i).val:ℤ))*
    ∏ i, (realBasis s (t i)).coeff (e i).val
  refine ⟨a,?_⟩
  intro x
  rw [tensor_interpolation v s f hf x]
  have hexp (t : Fin (s+1)) (y : ℝ) :
      (realBasis s t).eval y=∑ j : Fin (s+1), (realBasis s t).coeff j.val*y^j.val := by
    rw [Polynomial.eval_eq_sum_range' (Nat.lt_succ_of_le (realBasis_degree s t))]
    exact (Fin.sum_univ_eq_sum_range _ _).symm
  simp_rw [hexp]
  simp_rw [Fintype.prod_sum]
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro e _
  dsimp only [a]
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro t _
  rw [Finset.prod_mul_distrib]
  ring

 

theorem character_grid_expansion {G : Type*} [Group G] (H : CubeFaces.Filtration G)
    (s : ℕ) (hs : H.level (s+1)=⊥) {v : ℕ} {f : (Fin v→ℤ)→G}
    (hf : LeibmanSquare.Polynomial H 0 f) (χ : G→*Multiplicative ℝ) :
    ∃ a : Grid v s→ℝ, ∀ x : Fin v→ℤ,
      gridEval a (fun i => (x i:ℝ))=(χ (f x)).toAdd := by
  apply exists_grid_expansion
  intro x q
  exact LeibmanSquare.character_polynomial H s hs
    (LeibmanSquare.polynomial_integer_line H hf x q) χ

end CorrectedBoxLeibman
end
end
 

 
section
noncomputable section
open scoped BigOperators
open _root_.Polynomial _root_.OAI.Polynomial
namespace CorrectedBoxLeibman
 

def lineCoefficient {v s : ℕ} (f : (Fin v→ℤ)→ℝ) (q : Fin v→ℤ) (j : ℕ)
    (x : Fin v→ℤ) : ℝ :=
  ∑ t : Fin (s+1), f (fun i => x i+(t.val:ℤ)*q i)*(realBasis s t).coeff j

lemma lineCoefficient_eq {v s : ℕ} {f : (Fin v→ℤ)→ℝ} (x q : Fin v→ℤ)
    (P : ℝ[X]) (hP : P.natDegree ≤ s)
    (he : ∀ z : ℤ, P.eval (z:ℝ)=f (fun i => x i+z*q i)) (j : ℕ) :
    lineCoefficient (s:=s) f q j x=P.coeff j := by
  have hd : P.degree < (Finset.univ : Finset (Fin (s+1))).card := by
    apply lt_of_le_of_lt Polynomial.degree_le_natDegree
    simp only [Finset.card_univ,Fintype.card_fin,Nat.cast_lt]
    exact Nat.lt_succ_of_le hP
  have hh := congrArg (fun Q : ℝ[X] => Q.coeff j)
    (Lagrange.eq_interpolate (nat_nodes_injective s) hd)
  simp only [Lagrange.interpolate_apply,finsetSum_coeff,coeff_C_mul] at hh
  symm
  change P.coeff j=∑ t : Fin (s+1), _
  convert hh using 1
  apply Finset.sum_congr rfl
  intro t _
  rw [← Int.cast_natCast (R:=ℝ),he]
  rfl

lemma lineCoefficient_polynomial {v s : ℕ} {f : (Fin v→ℤ)→ℝ}
    (hf : LinePolynomial v s f) (q : Fin v→ℤ) (j : ℕ) :
    LinePolynomial v s (lineCoefficient (s:=s) f q j) := by
  classical
  intro x z
  have hp (t : Fin (s+1)) := hf (fun i => x i+(t.val:ℤ)*q i) z
  choose P hP he using hp
  refine ⟨∑ t : Fin (s+1), C ((realBasis s t).coeff j)*P t,?_,?_⟩
  · apply natDegree_sum_le_of_forall_le
    intro t _
    exact (natDegree_C_mul_le _ _).trans (hP t)
  · intro a
    simp only [eval_finsetSum,eval_mul,eval_C,lineCoefficient]
    apply Finset.sum_congr rfl
    intro t _
    rw [he]
    have hh : (fun i => x i+(t.val:ℤ)*q i+a*z i)=
        (fun i => x i+a*z i+(t.val:ℤ)*q i) := by ext i; ring
    rw [hh,mul_comm]

lemma gridEval_zero {v s : ℕ} (a : Grid v s→ℝ) : gridEval a 0=a 0 := by
  classical
  rw [gridEval,Finset.sum_eq_single 0]
  · simp
  · intro e _ he
    obtain ⟨i,hi⟩ := Function.ne_iff.mp he
    have hp : ∏ j, (0:ℝ)^(e j).val=0 := by
      apply Finset.prod_eq_zero (Finset.mem_univ i)
      apply zero_pow
      intro h
      apply hi
      exact Fin.ext h
    simp only [Pi.zero_apply,hp,mul_zero]
  · simp

 

theorem dense_line_constant (v s : ℕ) (δ : ℝ) (hδ : 0<δ) :
    ∃ C N₀ : ℕ, 0<C ∧ 0<N₀ ∧ ∃ ε₀ : ℝ, 0<ε₀ ∧
    ∀ N : ℕ, N₀≤N → ∀ ε : ℝ, 0≤ε → ε≤ε₀ →
    ∀ f : (Fin v→ℤ)→ℝ, LinePolynomial v s f → ∀ q : Fin v→ℤ, ∀ j : ℕ,
    ∀ S : Set (Fin v→ℕ),
      (∀ x∈S, TriangularLatticeRecovery.circleNorm
        (lineCoefficient (s:=s) f q j (fun i => (x i:ℤ)))≤ε) →
      δ*(N:ℝ)^v≤(BoxCounting.count v N S:ℝ) →
      ∃ r : ℕ, 0<r ∧ r≤C ∧ TriangularLatticeRecovery.circleNorm
        ((r:ℝ)*lineCoefficient (s:=s) f q j 0)≤(C:ℝ)*ε := by
  classical
  obtain ⟨C,N₀,hC,hN₀,ε₀,hε₀,hinv⟩ := DenseBoxComplete.lattice_inverse_all v s δ hδ
  refine ⟨C,N₀,hC,hN₀,ε₀,hε₀,?_⟩
  intro N hN ε hε hεsmall f hf q j S hgood hcount
  obtain ⟨a,ha⟩ := exists_grid_expansion v s (lineCoefficient (s:=s) f q j)
    (lineCoefficient_polynomial hf q j)
  have hae (x : Fin v→ℕ) : DenseBoxModularPolynomial.eval a x=
      lineCoefficient (s:=s) f q j (fun i => (x i:ℤ)) := by
    simpa only [DenseBoxModularPolynomial.eval,gridEval,Int.cast_natCast] using ha (fun i => (x i:ℤ))
  have hnear (x : Fin v→ℕ) (hx : x∈S) : ∃ z : ℤ,
      |DenseBoxModularPolynomial.eval a x-z|≤ε := by
    refine ⟨round (DenseBoxModularPolynomial.eval a x),?_⟩
    have h := hgood x hx
    rw [TriangularLatticeRecovery.circleNorm,UnitAddCircle.norm_eq,← hae] at h
    exact h
  obtain ⟨r,hr,hrC,hrb⟩ := hinv N hN ε hε hεsmall S a hnear hcount
  have hz : a 0=lineCoefficient (s:=s) f q j 0 := by
    have hh := ha (0 : Fin v→ℤ)
    have hzero : (fun i : Fin v => ((0 : Fin v→ℤ) i:ℝ))=0 := by ext i; simp
    rwa [hzero,gridEval_zero] at hh
  refine ⟨r,hr,hrC,?_⟩
  have hh := hrb 0
  simpa only [PolynomialLineCoefficients.totalDegree,Pi.zero_apply,Fin.val_zero,
    Finset.sum_const_zero,pow_zero,mul_one,hz] using hh

end CorrectedBoxLeibman
end
end
 

 

end
end
end

end OAI
