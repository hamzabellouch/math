import Mathlib
import OAI.Algebra.FiniteTensor.ClosedSpecialization
import OAI.Algebra.FiniteTensor.CoefficientDescent
import OAI.Algebra.FiniteTensor.KernelRelations

namespace OAI

/-! Finite-type algebraic coefficient descent and the algebraic tensor contradiction. -/

noncomputable section
open scoped BigOperators

namespace PD4Tensor.Spreading
open scoped BigOperators
variable {K σ : Type*} [Field K] [Finite σ]

def truncSeries (n : ℕ) (f : MvPowerSeries σ K) : MvPowerSeries σ K :=
  (MvPowerSeries.truncTotal n f : MvPolynomial σ K)

 theorem coeff_truncSeries (n : ℕ) (f : MvPowerSeries σ K) (d : σ →₀ ℕ) :
    MvPowerSeries.coeff d (truncSeries n f)=
      if d.degree<n then MvPowerSeries.coeff d f else 0 := by
  exact MvPowerSeries.coeff_truncTotal_eq_ite _

 theorem order_truncSeries_sub (n : ℕ) (f : MvPowerSeries σ K) :
    (n : ℕ∞)≤(truncSeries n f-f).order := by
  apply MvPowerSeries.nat_le_order
  intro d hd
  simp only [map_sub,coeff_truncSeries,ite_eq_left hd,sub_self]

 theorem homogeneous_truncSeries (n : ℕ) (f : MvPowerSeries σ K) :
    MvPowerSeries.homogeneousComponent n (truncSeries n f)=0 := by
  ext d
  simp only [MvPowerSeries.coeff_homogeneousComponent,coeff_truncSeries,map_zero]
  split_ifs <;> simp_all

 

theorem homogeneous_root_equation (P : Polynomial (MvPowerSeries σ K))
    (f : MvPowerSeries σ K) (hf : P.eval f=0) (r n : ℕ) (hrn : r<n)
    (hD : (r : ℕ∞)≤(P.derivative.eval f).order) :
    MvPowerSeries.homogeneousComponent r (P.derivative.eval f)*
        MvPowerSeries.homogeneousComponent n f =
      -MvPowerSeries.homogeneousComponent (r+n) (P.eval (truncSeries n f)) := by
  let h := truncSeries n f-f
  obtain ⟨c,hc⟩ := Polynomial.exists_mul_sq_add_linear_part_eq_eval_add P f h
  have hn : (n : ℕ∞)≤h.order := order_truncSeries_sub n f
  have hrem : MvPowerSeries.homogeneousComponent (r+n) (c*h^2)=0 := by
    apply MvPowerSeries.homogeneousComponent_of_lt_order_eq_zero
    calc
      ((r+n : ℕ) : ℕ∞) < ((n+n : ℕ) : ℕ∞) := by exact_mod_cast Nat.add_lt_add_right hrn n
      _ ≤ h.order+h.order := by simpa only [Nat.cast_add] using add_le_add hn hn
      _ ≤ (h^2).order := by simpa only [two_nsmul] using MvPowerSeries.le_order_pow (f:=h) 2
      _ ≤ c.order+(h^2).order := le_add_of_nonneg_left zero_le
      _ ≤ (c*h^2).order := MvPowerSeries.le_order_mul
  have hh := congrArg (MvPowerSeries.homogeneousComponent (r+n)) hc
  rw [show f+h=truncSeries n f by dsimp [h]; ring,hf,map_add,map_add,hrem,
    map_zero,add_zero,zero_add] at hh
  rw [MvPowerSeries.homogeneousComponent_mul_of_le_order hD hn] at hh
  have hh' : MvPowerSeries.homogeneousComponent n h=
      -MvPowerSeries.homogeneousComponent n f := by
    simp only [h,map_sub,homogeneous_truncSeries,zero_sub]
  rw [hh',mul_neg] at hh
  exact neg_eq_iff_eq_neg.mp hh

end PD4Tensor.Spreading

namespace PD4Tensor.Spreading
open scoped BigOperators
open Finsupp
variable {K σ : Type*} [Field K]

 theorem eval_mem_seriesOver (A : Subring K) (P : Polynomial (MvPowerSeries σ K))
    (hP : ∀ i,P.coeff i ∈seriesOver A) (f : MvPowerSeries σ K)
    (hf : f∈seriesOver A) : P.eval f∈seriesOver A := by
  rw [Polynomial.eval_eq_sum,Polynomial.sum]
  exact (seriesOver A).sum_mem (fun i _ => (seriesOver A).mul_mem (hP i) ((seriesOver A).pow_mem hf i))

 theorem homogeneous_mem_seriesOver (A : Subring K) (f : MvPowerSeries σ K)
    (hf : f∈seriesOver A) (n : ℕ) : MvPowerSeries.homogeneousComponent n f∈seriesOver A := by
  rw [mem_seriesOver] at hf ⊢
  intro d
  rw [MvPowerSeries.coeff_homogeneousComponent]
  split_ifs
  · exact hf d
  · exact A.zero_mem

variable [Finite σ] [LinearOrder σ] [WellFoundedGT σ]

theorem coefficients_root_mem (A : Subring K) (P : Polynomial (MvPowerSeries σ K))
    (f : MvPowerSeries σ K) (hf : P.eval f=0) (r : ℕ)
    (hDr : (r : ℕ∞)≤(P.derivative.eval f).order)
    (a : σ →₀ ℕ)
    (ha : MvPowerSeries.coeff a (MvPowerSeries.homogeneousComponent r (P.derivative.eval f))≠0)
    (hmin : ∀ u,toLex u<toLex a →
      MvPowerSeries.coeff u (MvPowerSeries.homogeneousComponent r (P.derivative.eval f))=0)
    (hP : ∀ i,P.coeff i∈seriesOver A)
    (hD : MvPowerSeries.homogeneousComponent r (P.derivative.eval f)∈seriesOver A)
    (hinv : (MvPowerSeries.coeff a (MvPowerSeries.homogeneousComponent r (P.derivative.eval f)))⁻¹∈A)
    (hlow : ∀ b,b.degree≤r → MvPowerSeries.coeff b f∈A) :
    f∈seriesOver A := by
  rw [mem_seriesOver]
  suffices hall : ∀ n,∀ b : σ →₀ ℕ,b.degree=n → MvPowerSeries.coeff b f∈A by
    intro b
    exact hall b.degree b rfl
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro b hb
    by_cases hn : n≤r
    · exact hlow b (hb ▸ hn)
    have hrn : r<n := lt_of_not_ge hn
    have ht : truncSeries n f∈seriesOver A := by
      rw [mem_seriesOver]
      intro d
      rw [coeff_truncSeries]
      split_ifs with hd
      · exact ih d.degree hd d rfl
      · exact A.zero_mem
    have heval := eval_mem_seriesOver A P hP (truncSeries n f) ht
    have hmul : MvPowerSeries.homogeneousComponent r (P.derivative.eval f)*
        MvPowerSeries.homogeneousComponent n f∈seriesOver A := by
      rw [homogeneous_root_equation P f hf r n hrn hDr]
      exact (seriesOver A).neg_mem (homogeneous_mem_seriesOver A _ heval _)
    have hout := coefficients_of_product A _ (MvPowerSeries.homogeneousComponent n f) a ha hmin
      ((mem_seriesOver A _).mp hD) hinv ((mem_seriesOver A _).mp hmul) b
    simpa only [MvPowerSeries.coeff_homogeneousComponent,hb,ite_true] using hout

end PD4Tensor.Spreading

namespace PD4Tensor.Spreading
open scoped BigOperators
open Finsupp
variable {K σ : Type*} [Field K] [CharZero K]
  [Finite σ] [LinearOrder σ] [WellFoundedGT σ]

 

theorem algebraic_series_finiteType (f : MvPowerSeries σ K)
    (hf : IsAlgebraic (MvPolynomial σ K) f) :
    ∃ A : Subalgebra ℤ K, Algebra.FiniteType ℤ A ∧
      ∀ d,MvPowerSeries.coeff d f∈A := by
  classical
  have hi : Function.Injective (algebraMap (MvPolynomial σ K) (MvPowerSeries σ K)) := by
    intro x y h
    apply MvPolynomial.coe_injective σ K
    simpa only [MvPowerSeries.algebraMap_apply',Algebra.algebraMap_self,
      MvPowerSeries.map_id,RingHom.id_apply] using h
  obtain ⟨P,_,hPf,hPd⟩ := exists_relation_derivative_ne_zero hi f hf
  let Q := P.map (algebraMap (MvPolynomial σ K) (MvPowerSeries σ K))
  have hQf : Q.eval f=0 := by
    simpa only [Q,Polynomial.eval_map,←Polynomial.aeval_def] using hPf
  have hQd : Q.derivative.eval f≠0 := by
    simpa only [Q,Polynomial.derivative_map,Polynomial.eval_map,←Polynomial.aeval_def] using hPd
  let D := Q.derivative.eval f
  let r := D.order.toNat
  have hr : (r : ℕ∞)=D.order := MvPowerSeries.ne_zero_iff_order_finite.mp hQd
  let H := MvPowerSeries.homogeneousComponent r D
  have hH : H≠0 := MvPowerSeries.homogeneousComponent_of_order hr
  have hn : {b : Lex (σ →₀ ℕ) | MvPowerSeries.coeff (ofLex b) H≠0}.Nonempty := by
    by_contra hn
    apply hH
    ext d
    have hh : MvPowerSeries.coeff d H=0 := by
      by_contra hd
      exact hn ⟨toLex d,hd⟩
    simpa only [map_zero] using hh
  obtain ⟨a,ha,hminimal⟩ := (wellFounded_lt :
    WellFounded ((· < ·) : Lex (σ →₀ ℕ) → _ → Prop)).has_min _ hn
  let sp : Finset K := P.support.biUnion (fun i => (P.coeff i).coeffs)
  let sl : Finset K := (finite_of_degree_le r).toFinset.image (fun d => MvPowerSeries.coeff d f)
  let sd : Finset K := (finite_of_degree_le r).toFinset.image (fun d => MvPowerSeries.coeff d H)
  let s : Finset K := sp ∪ sl ∪ sd ∪ {(MvPowerSeries.coeff (ofLex a) H)⁻¹}
  let A := Algebra.adjoin ℤ (s : Set K)
  have hgen {x : K} (hx : x∈s) : x∈A.toSubring := Algebra.subset_adjoin hx
  refine ⟨A,Algebra.FiniteType.adjoin_of_finite s.finite_toSet,?_⟩
  have hout : f∈seriesOver A.toSubring := by
    apply coefficients_root_mem A.toSubring Q f hQf r (le_of_eq hr) (ofLex a) ha
    · intro u hu
      by_contra h
      exact hminimal (toLex u) h (by simpa only [toLex_ofLex] using hu)
    · intro i
      rw [mem_seriesOver]
      intro d
      simp only [Q,Polynomial.coeff_map,MvPowerSeries.algebraMap_apply',
        Algebra.algebraMap_self,MvPowerSeries.map_id,RingHom.id_apply,MvPolynomial.coeff_coe]
      by_cases hc : (P.coeff i).coeff d=0
      · rw [hc]
        exact A.zero_mem
      · apply hgen
        have hp : P.coeff i≠0 := by intro h; exact hc (by simp [h])
        have hh : (P.coeff i).coeff d∈sp :=
          Finset.mem_biUnion.mpr ⟨i,Polynomial.mem_support_iff.mpr hp,
            MvPolynomial.coeff_mem_coeffs d hc⟩
        exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ hh))
    · rw [mem_seriesOver]
      intro d
      change MvPowerSeries.coeff d H∈A.toSubring
      by_cases hd : d.degree=r
      · apply hgen
        have hh : MvPowerSeries.coeff d H∈sd :=
          Finset.mem_image.mpr ⟨d,(finite_of_degree_le r).mem_toFinset.mpr (le_of_eq hd),rfl⟩
        exact Finset.mem_union_left _ (Finset.mem_union_right _ hh)
      · have hh : MvPowerSeries.coeff d H=0 := by
          simp only [H,MvPowerSeries.coeff_homogeneousComponent,ite_eq_right hd]
        rw [hh]
        exact A.zero_mem
    · exact hgen (Finset.mem_union_right _ (Finset.mem_singleton_self _))
    · intro d hd
      apply hgen
      have hh : MvPowerSeries.coeff d f∈sl :=
        Finset.mem_image.mpr ⟨d,(finite_of_degree_le r).mem_toFinset.mpr hd,rfl⟩
      exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ hh))
  exact (mem_seriesOver A.toSubring f).mp hout

end PD4Tensor.Spreading

namespace PD4Tensor.Spreading
variable {K ι : Type*} [Field K] [CharZero K] [Fintype ι]

 

theorem algebraic_family_finiteType (n : ι → ℕ)
    (f : ∀ i,MvPowerSeries (Fin (n i)) K)
    (hf : ∀ i,IsAlgebraic (MvPolynomial (Fin (n i)) K) (f i)) (extra : Finset K) :
    ∃ A : Subalgebra ℤ K, Algebra.FiniteType ℤ A ∧
      (∀ x∈extra,x∈A) ∧ ∀ i d,MvPowerSeries.coeff d (f i)∈A := by
  classical
  choose B hB hcoef using fun i => algebraic_series_finiteType (f i) (hf i)
  have hfg : ∀ i,(B i).FG := fun i => (Subalgebra.fg_iff_finiteType (B i)).mpr (hB i)
  choose gens hgens using hfg
  let s := Finset.univ.biUnion gens ∪ extra
  let A := Algebra.adjoin ℤ (s : Set K)
  have hBA : ∀ i,B i≤A := by
    intro i
    rw [←hgens i]
    apply Algebra.adjoin_mono
    intro x hx
    exact Finset.mem_union_left _ (Finset.mem_biUnion.mpr ⟨i,Finset.mem_univ i,hx⟩)
  refine ⟨A,Algebra.FiniteType.adjoin_of_finite s.finite_toSet,?_,?_⟩
  · intro x hx
    exact Algebra.subset_adjoin (Finset.mem_union_right _ hx)
  · intro i d
    exact hBA i (hcoef i d)

end PD4Tensor.Spreading

namespace PD4Tensor.Spreading
noncomputable section
open scoped BigOperators
variable {K : Type*} [Field K] [CharZero K] {l m d c : ℕ} {n : Fin l → ℕ}
  {e : ((i : Fin l) × Fin (n i)) ≃ Fin d ⊕ Fin c} {active : Fin m ↪ Fin l}

 

structure AlgebraicData (M : TensorModel K (fun i=>Fin (n i)) m d c e active)
    (W : TensorPrimitives K (fun i=>Fin (n i)) m M) : Prop where
  F : ∀ i,IsAlgebraic (MvPolynomial (Fin (n i)) K) (M.F i)
  b : ∀ i,IsAlgebraic (MvPolynomial (Fin (n (active i))) K) (M.b i)
  H : ∀ v q,IsAlgebraic (MvPolynomial (Fin d) K) (boxSeries K m q (M.H v))
  G : ∀ v,IsAlgebraic (MvPolynomial (Fin c) K) (M.G v)
  left : ∀ t v q,IsAlgebraic (MvPolynomial (Fin d) K) (boxSeries K m q (W.left t v))
  right : ∀ t v,IsAlgebraic (MvPolynomial (Fin c) K) (W.right t v)

 

theorem algebraic_data_descends (M : TensorModel K (fun i=>Fin (n i)) m d c e active)
    (W : TensorPrimitives K (fun i=>Fin (n i)) m M) (h : AlgebraicData M W) :
    ∃ A : Subalgebra ℤ K, Algebra.FiniteType ℤ A.toSubring ∧ IsUnit (2 : A.toSubring) ∧
      Nonempty (TensorModel A.toSubring (fun i=>Fin (n i)) m d c e active) := by
  classical
  let V := (i : Fin l) × Fin (n i)
  let I := Fin l ⊕ Fin m ⊕ (V × Box m) ⊕ V ⊕ (Triple m × V × Box m) ⊕ (Triple m × V)
  let size : I → ℕ := Sum.elim n (Sum.elim (fun i=>n (active i))
    (Sum.elim (fun _=>d) (Sum.elim (fun _=>c) (Sum.elim (fun _=>d) (fun _=>c)))))
  let f : ∀ i:I,MvPowerSeries (Fin (size i)) K := fun i=>
    match i with
    | .inl i => M.F i
    | .inr (.inl i) => M.b i
    | .inr (.inr (.inl (v,q))) => boxSeries K m q (M.H v)
    | .inr (.inr (.inr (.inl v))) => M.G v
    | .inr (.inr (.inr (.inr (.inl (t,v,q))))) => boxSeries K m q (W.left t v)
    | .inr (.inr (.inr (.inr (.inr (t,v))))) => W.right t v
  have hf : ∀ i,IsAlgebraic (MvPolynomial (Fin (size i)) K) (f i) := by
    rintro (i|i)
    · exact h.F i
    rcases i with i|i
    · exact h.b i
    rcases i with i|i
    · exact h.H i.1 i.2
    rcases i with i|i
    · exact h.G i
    rcases i with i|i
    · exact h.left i.1 i.2.1 i.2.2
    · exact h.right i.1 i.2
  let det := (tangent K (fun i=>Fin (n i)) m e M.H M.G).det
  obtain ⟨A,hA,hex,hcoef⟩ := algebraic_family_finiteType size f hf {(2:K)⁻¹,det⁻¹}
  have h2inv : (2:K)⁻¹∈A := hex _ (Finset.mem_insert_self _ _)
  have hdetinv : det⁻¹∈A := hex _ (Finset.mem_insert_of_mem (Finset.mem_singleton_self _))
  have hc : CoefficientsIn A.toSubring M W := {
    F := fun i b=>hcoef (.inl i) b
    b := fun i a=>hcoef (.inr (.inl i)) a
    H := fun v q b=>hcoef (.inr (.inr (.inl (v,q)))) b
    G := fun v b=>hcoef (.inr (.inr (.inr (.inl v)))) b
    left := fun t v q b=>hcoef (.inr (.inr (.inr (.inr (.inl (t,v,q)))))) b
    right := fun t v b=>hcoef (.inr (.inr (.inr (.inr (.inr (t,v)))))) b
    det_inv := hdetinv }
  refine ⟨A,hA,?_,⟨descendTensorModel A.toSubring M W hc⟩⟩
  apply isUnit_iff_exists_inv.mpr
  refine ⟨⟨(2:K)⁻¹,h2inv⟩,?_⟩
  apply Subtype.val_injective
  change (2:K)*(2:K)⁻¹=1
  exact mul_inv_cancel₀ (by norm_num)

end
end PD4Tensor.Spreading

namespace PD4Tensor.Spreading
noncomputable section
variable {K : Type*} [Field K] [CharZero K] {l m d c : ℕ} {n : Fin l → ℕ}
  {e : ((i : Fin l) × Fin (n i)) ≃ Fin d ⊕ Fin c} {active : Fin m ↪ Fin l}

 

theorem no_algebraic_tensor_model (hm : 5 ≤ m)
    (M : TensorModel K (fun i=>Fin (n i)) m d c e active)
    (W : TensorPrimitives K (fun i=>Fin (n i)) m M) (h : AlgebraicData M W) : False := by
  obtain ⟨A,hA,h2,⟨M'⟩⟩ := algebraic_data_descends M W h
  let : Algebra.FiniteType ℤ A.toSubring := hA
  exact (no_tensor_model_finiteType (fun i=>Fin (n i)) A.toSubring h2 e hm active).false M'

end
end PD4Tensor.Spreading
end

end OAI
