import Mathlib
import OAI.Combinatorics.SumProduct.Alignment.FejerDetection01
import OAI.Geometry.NilpotentCharts.Main

namespace OAI

section
section
section
section
open _root_.Polynomial _root_.OAI.Polynomial Finset
open scoped BigOperators
namespace DensePolynomialInterpolation
open _root_.Polynomial _root_.OAI.Polynomial Finset
noncomputable section

def uniformBound (q : ℕ) (α : ℝ) : ℝ := (q+1) * (2*(q+1)/α)^q

lemma nodes_injective {q N : ℕ} {α : ℝ} (hN : 0 < N) (hα : 0 < α)
    (v : Fin (q+1) → ℤ)
    (hsep : ∀ i j, i ≠ j → α * N / (2 * (q+1)) ≤ |(v i : ℝ) - v j|) :
    Function.Injective (fun i => (v i : ℝ)) := by
  intro i j hij
  by_contra hne
  have h := hsep i j hne
  dsimp only at hij
  rw [hij, sub_self, abs_zero] at h
  have : 0 < α * N / (2 * (q+1)) := by positivity
  linarith

lemma interpolation_error {q N : ℕ} {α : ℝ} (hN : 0 < N) (hα : 0 < α)
    (v : Fin (q+1) → ℤ) (hv : ∀ i, (v i : ℝ) ∈ Set.Icc 0 (N : ℝ))
    (hsep : ∀ i j, i ≠ j → α * N / (2 * (q+1)) ≤ |(v i : ℝ) - v j|)
    (T : ℝ[X]) (hT : T.natDegree ≤ q) (r : Fin (q+1) → ℝ)
    {ε : ℝ} (hε : 0 ≤ ε) (hr : ∀ i, |r i - T.eval (v i : ℝ)| ≤ ε)
    {x : ℝ} (hx : x ∈ Set.Icc 0 (N : ℝ)) :
    |(Lagrange.interpolate univ (fun i => (v i : ℝ)) r).eval x - T.eval x| ≤
      uniformBound q α * ε := by
  have hdeg : T.degree < ((univ : Finset (Fin (q+1))).card : WithBot ℕ) := by
    simp only [card_univ, Fintype.card_fin]
    exact lt_of_le_of_lt (degree_le_natDegree.trans
      (show (T.natDegree : WithBot ℕ) ≤ (q : WithBot ℕ) by exact_mod_cast hT))
      (by exact_mod_cast Nat.lt_succ_self q)
  have h := LagrangeBounds.interpolate_error univ (fun i => (v i : ℝ))
    (nodes_injective hN hα v hsep).injOn
    (by positivity : (0 : ℝ) < α * N / (2 * (q+1))) hε
    (fun i _ => hv i) (fun i _ j _ hji => hsep i j hji.symm) hx T hdeg r (fun i _ => hr i)
  have heq : ((N : ℝ) - 0) / (α * N / (2 * (q+1))) = 2 * (q+1) / α := by
    have hn : (N : ℝ) ≠ 0 := by positivity
    field_simp
    simp
  rw [heq] at h
  simpa only [uniformBound, card_univ, Fintype.card_fin, Nat.cast_add, Nat.cast_one,
    Nat.add_sub_cancel] using h

 
def normalizedNode (d : ℕ) (i : Fin (d+1)) : ℝ := i.val / (d+1)

lemma normalizedNode_injective (d : ℕ) : Function.Injective (normalizedNode d) := by
  intro i j hij
  apply Fin.ext
  have hden : (d:ℝ)+1 ≠ 0 := by positivity
  have h : (i.val:ℝ) = j.val := (div_left_inj' hden).mp hij
  exact_mod_cast h

lemma normalizedNode_mem (d : ℕ) (i : Fin (d+1)) :
    normalizedNode d i ∈ Set.Icc (0:ℝ) 1 := by
  constructor
  · dsimp [normalizedNode]; positivity
  · dsimp [normalizedNode]
    apply (div_le_one (by positivity : (0:ℝ) < d+1)).mpr
    exact_mod_cast i.isLt.le

def coefficientConstant (d : ℕ) : ℝ := 1 +
  ∑ j ∈ range (d+1), ∑ i : Fin (d+1),
    |(Lagrange.basis univ (normalizedNode d) i).coeff j|

lemma coefficientConstant_pos (d : ℕ) : 0 < coefficientConstant d := by
  have h : 0 ≤ ∑ j ∈ range (d+1), ∑ i : Fin (d+1),
      |(Lagrange.basis univ (normalizedNode d) i).coeff j| :=
    sum_nonneg (fun _ _ => sum_nonneg (fun _ _ => abs_nonneg _))
  dsimp [coefficientConstant]
  linarith

lemma coefficient_bound_unit (d : ℕ) (p : ℝ[X]) (hp : p.natDegree ≤ d)
    (ε : ℝ) (hε : 0 ≤ ε) (hv : ∀ x ∈ Set.Icc (0:ℝ) 1, |p.eval x| ≤ ε)
    (j : ℕ) (hj : j ≤ d) : |p.coeff j| ≤ coefficientConstant d * ε := by
  have hdeg : p.degree < ((univ : Finset (Fin (d+1))).card : WithBot ℕ) := by
    simp only [card_univ,Fintype.card_fin]
    exact lt_of_le_of_lt (degree_le_natDegree.trans (show (p.natDegree : WithBot ℕ) ≤ (d : WithBot ℕ) by exact_mod_cast hp))
      (by exact_mod_cast Nat.lt_succ_self d)
  have he := Lagrange.eq_interpolate (normalizedNode_injective d).injOn hdeg
  conv_lhs => rw [he]
  rw [Lagrange.interpolate_apply,finsetSum_coeff]
  calc
    _ ≤ ∑ i : Fin (d+1), ε * |(Lagrange.basis univ (normalizedNode d) i).coeff j| := by
      apply (abs_sum_le_sum_abs _ _).trans
      apply sum_le_sum
      intro i _
      rw [coeff_C_mul,abs_mul]
      exact mul_le_mul_of_nonneg_right (hv _ (normalizedNode_mem d i)) (abs_nonneg _)
    _ = (∑ i : Fin (d+1), |(Lagrange.basis univ (normalizedNode d) i).coeff j|)*ε := by
      rw [← mul_sum,mul_comm]
    _ ≤ coefficientConstant d * ε := by
      refine mul_le_mul_of_nonneg_right ?_ hε
      have h : (∑ i : Fin (d+1), |(Lagrange.basis univ (normalizedNode d) i).coeff j|) ≤
          ∑ k ∈ range (d+1), ∑ i : Fin (d+1),
            |(Lagrange.basis univ (normalizedNode d) i).coeff k| :=
        single_le_sum (fun (k : ℕ) (_ : k ∈ range (d+1)) =>
          sum_nonneg (fun (i:Fin (d+1)) _ =>
            abs_nonneg ((Lagrange.basis univ (normalizedNode d) i).coeff k)))
          (mem_range.mpr (Nat.lt_succ_of_le hj))
      exact h.trans (le_add_of_nonneg_left zero_le_one)

lemma coefficient_bound_span (d : ℕ) (p : ℝ[X]) (hp : p.natDegree ≤ d)
    (N ε : ℝ) (hN : 0 < N) (hε : 0 ≤ ε)
    (hv : ∀ x ∈ Set.Icc 0 N, |p.eval x| ≤ ε) (j : ℕ) (hj : j ≤ d) :
    |p.coeff j| ≤ coefficientConstant d * ε / N^j := by
  let P := p.comp (C N * X)
  have hP : P.natDegree ≤ d := by
    have hdeg : (C N * X : ℝ[X]).natDegree = 1 := natDegree_C_mul_X N hN.ne'
    exact (natDegree_comp_le.trans (by rw [hdeg,Nat.mul_one])).trans hp
  have h := coefficient_bound_unit d P hP ε hε (by
    intro x hx
    simp only [P,eval_comp,eval_mul,eval_C,eval_X]
    apply hv
    constructor
    · exact mul_nonneg hN.le hx.1
    · nlinarith [hx.2]) j hj
  have hcoef : P.coeff j = p.coeff j * N^j := by
    simp only [P,comp_C_mul_X_coeff]
  rw [hcoef,abs_mul,abs_of_nonneg (pow_nonneg hN.le j)] at h
  exact (le_div_iff₀ (pow_pos hN j)).mpr h

 
theorem dense_coefficient_bound (d N : ℕ) (hN : 0 < N) (α ε : ℝ)
    (hα : 0 < α) (hε : 0 ≤ ε) (E : Finset ℤ)
    (hlarge : 2*(d+1) ≤ E.card) (hdens : α*N ≤ (E.card:ℝ))
    (hEN : ∀ n ∈ E, (n:ℝ) ∈ Set.Icc 0 (N:ℝ))
    (p : ℝ[X]) (hp : p.natDegree ≤ d)
    (hsmall : ∀ n ∈ E, |p.eval (n:ℝ)| ≤ ε)
    (j : ℕ) (hj : j ≤ d) :
    |p.coeff j| ≤ coefficientConstant d * uniformBound d α * ε / (N:ℝ)^j := by
  obtain ⟨v,hv,hsep⟩ := DenseIntegerNodes.separated_of_density E d hlarge hdens
  have hub : 0 ≤ uniformBound d α := by dsimp [uniformBound]; positivity
  have hsup : ∀ x ∈ Set.Icc 0 (N:ℝ), |p.eval x| ≤ uniformBound d α * ε := by
    intro x hx
    have h := interpolation_error hN hα v (fun i => hEN _ (hv i))
      hsep p hp (fun _ => 0) hε (by intro i; simpa using hsmall _ (hv i)) hx
    simpa [Lagrange.interpolate_apply] using h
  have h := coefficient_bound_span d p hp N _ (Nat.cast_pos.mpr hN)
    (mul_nonneg hub hε) hsup j hj
  simpa only [mul_assoc] using h

 

theorem bounded_lattice_coefficients (d N B : ℕ) (hN : 0 < N) (δ ε : ℝ)
    (hδ : 0 < δ) (hε : 0 ≤ ε) (hεone : ε ≤ 1)
    (hlarge : (2*(d+1):ℝ) ≤ δ*N/(2*B+3))
    (S : Finset ℤ) (hdens : δ*N ≤ (S.card:ℝ))
    (hSN : ∀ n ∈ S, (n:ℝ) ∈ Set.Icc 0 (N:ℝ))
    (p : ℝ[X]) (hp : p.natDegree ≤ d)
    (hbound : ∀ n ∈ S, |p.eval (n:ℝ)| ≤ B)
    (hgood : ∀ n ∈ S, ∃ z : ℤ, |p.eval (n:ℝ)-z| ≤ ε)
    (j : ℕ) (hj : 0 < j) (hjd : j ≤ d) :
    |p.coeff j| ≤ coefficientConstant d * uniformBound d (δ/(2*B+3)) * ε / (N:ℝ)^j := by
  classical
  choose z hz using (fun n : S => hgood n.val n.property)
  let Z : ℤ → ℤ := fun n => if hn : n ∈ S then z ⟨n,hn⟩ else 0
  have hZ : ∀ n ∈ S, |p.eval (n:ℝ)-(Z n:ℝ)| ≤ ε := by
    intro n hn
    simpa only [Z,dite_eq_left hn] using hz ⟨n,hn⟩
  let T : Finset ℤ := Icc (-(B+1):ℤ) (B+1)
  have hT : T.Nonempty := by refine ⟨0, ?_⟩; simp only [T,mem_Icc]; constructor <;> omega
  have hTcard : (T.card:ℝ) = 2*B+3 := by
    simp only [T,Int.card_Icc]
    have he : ((B:ℤ)+1+1 - -((B:ℤ)+1)) = (2*B+3:ℕ) := by push_cast; ring
    rw [he,Int.toNat_natCast]
    push_cast
    ring
  have hZT : ∀ n ∈ S, Z n ∈ T := by
    intro n hn
    have hh := abs_sub_le (Z n:ℝ) (p.eval (n:ℝ)) 0
    rw [sub_zero,sub_zero,abs_sub_comm] at hh
    have hb : |(Z n:ℝ)| ≤ (B:ℝ)+1 := by linarith [hZ n hn,hbound n hn]
    have hb' := abs_le.mp hb
    have hlo : (-(B+1):ℤ) ≤ Z n := by exact_mod_cast hb'.1
    have hhi : Z n ≤ (B+1:ℤ) := by exact_mod_cast hb'.2
    exact mem_Icc.mpr ⟨hlo,hhi⟩
  have hcard : T.card • (δ*N/(2*B+3)) ≤ (S.card:ℝ) := by
    rw [nsmul_eq_mul,hTcard]
    have hb : (2*(B:ℝ)+3) ≠ 0 := by positivity
    rw [mul_div_cancel₀ _ hb]
    exact hdens
  obtain ⟨k,hk,hfiber⟩ := exists_le_card_fiber_of_nsmul_le_card_of_maps_to hZT hT hcard
  let E := S.filter (fun n => Z n=k)
  have hElarge : 2*(d+1) ≤ E.card := by
    exact_mod_cast hlarge.trans hfiber
  have hEden : (δ/(2*B+3)) * N ≤ (E.card:ℝ) := by
    simpa only [div_mul_eq_mul_div] using hfiber
  have hα : 0 < δ/(2*B+3) := by positivity
  have hdeg : (p-C (k:ℝ)).natDegree ≤ d :=
    (natDegree_sub_le _ _).trans (max_le hp (by simp))
  have h := dense_coefficient_bound d N hN (δ/(2*B+3)) ε hα hε E hElarge
    hEden (fun n hn => hSN n (mem_filter.mp hn).1) (p-C (k:ℝ)) hdeg (by
      intro n hn
      obtain ⟨hn,hZk⟩ := mem_filter.mp hn
      simpa only [eval_sub,eval_C,hZk] using hZ n hn) j hjd
  simpa only [coeff_sub,coeff_C,ite_eq_right (Nat.ne_of_gt hj),sub_zero] using h

end
end DensePolynomialInterpolation

 
namespace PolynomialIntegralResidual
open _root_.Polynomial _root_.OAI.Polynomial Finset
open scoped BigOperators
noncomputable section

def integerPart (d : ℕ) (m : ℕ → ℤ) : ℤ[X] :=
  ∑ j ∈ range (d+1), monomial j (m j)

lemma integerPart_coeff (d : ℕ) (m : ℕ → ℤ) (j : ℕ) (hj : j ≤ d) :
    (integerPart d m).coeff j = m j := by
  simp [integerPart,finsetSum_coeff,coeff_monomial,mem_range.mpr (Nat.lt_succ_of_le hj)]

lemma integerPart_degree (d : ℕ) (m : ℕ → ℤ) : (integerPart d m).natDegree ≤ d := by
  apply natDegree_sum_le_of_forall_le
  intro j hj
  exact (natDegree_monomial_le _).trans (Nat.le_of_lt_succ (mem_range.mp hj))

lemma integerPart_eval (d : ℕ) (m : ℕ → ℤ) (n : ℤ) :
    ((integerPart d m).map (Int.castRingHom ℝ)).eval (n:ℝ) =
      ((integerPart d m).eval n : ℤ) := by
  rw [eval_map]
  exact eval₂_at_apply (Int.castRingHom ℝ) n

 

lemma eval_bound (d N A : ℕ) (hN : 0 < N) (p : ℝ[X]) (hp : p.natDegree ≤ d)
    (hzero : |p.coeff 0| ≤ 1)
    (hcoeff : ∀ j : ℕ, 0 < j → j ≤ d → |p.coeff j| ≤ (A:ℝ)/(N:ℝ)^j)
    (x : ℝ) (hx : x ∈ Set.Icc 0 (N:ℝ)) :
    |p.eval x| ≤ ((d+1)*(A+1):ℕ) := by
  rw [eval_eq_sum_range' (Nat.lt_succ_of_le hp)]
  calc
    _ ≤ ∑ j ∈ range (d+1), ((A:ℝ)+1) := by
      apply (abs_sum_le_sum_abs _ _).trans
      apply sum_le_sum
      intro j hj
      by_cases hz : j=0
      · subst j
        simp only [pow_zero,mul_one]
        exact hzero.trans (by have := Nat.cast_nonneg (α := ℝ) A; linarith)
      · have hjpos : 0 < j := Nat.pos_of_ne_zero hz
        have hd : j ≤ d := Nat.le_of_lt_succ (mem_range.mp hj)
        have h := (le_div_iff₀ (pow_pos (Nat.cast_pos.mpr hN) j)).mp (hcoeff j hjpos hd)
        rw [abs_mul,abs_of_nonneg (pow_nonneg hx.1 j)]
        have hh := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hx.1 hx.2 j)
          (abs_nonneg (p.coeff j))
        have ha := Nat.cast_nonneg (α := ℝ) A
        linarith
    _ = _ := by simp only [sum_const,card_range,nsmul_eq_mul,Nat.cast_mul,
      Nat.cast_add,Nat.cast_one]

 

theorem residual (d N A : ℕ) (hN : 0 < N) (p : ℝ[X]) (hp : p.natDegree ≤ d)
    (q : ℤ) (m : ℕ → ℤ)
    (hm : ∀ j : ℕ, 0 < j → j ≤ d →
      |(q:ℝ)*p.coeff j - m j| ≤ (A:ℝ)/(N:ℝ)^j) :
    ∃ u : ℤ[X], ∃ r : ℝ[X],
      r = C (q:ℝ)*p - u.map (Int.castRingHom ℝ) ∧ r.natDegree ≤ d ∧
      (∀ j : ℕ, 0 < j → j ≤ d → r.coeff j = (q:ℝ)*p.coeff j-m j) ∧
      (∀ x ∈ Set.Icc (0:ℝ) (N:ℝ), |r.eval x| ≤ ((d+1)*(A+1):ℕ)) := by
  let m' : ℕ → ℤ := fun j => if j=0 then ⌊(q:ℝ)*p.coeff 0⌋ else m j
  let u := integerPart d m'
  let r := C (q:ℝ)*p - u.map (Int.castRingHom ℝ)
  have hdeg : r.natDegree ≤ d := by
    apply (natDegree_sub_le _ _).trans
    apply max_le
    · exact (natDegree_mul_le.trans (by simp)).trans hp
    · exact natDegree_map_le.trans (integerPart_degree d m')
  have hcoef (j : ℕ) (hjd : j ≤ d) : r.coeff j = (q:ℝ)*p.coeff j - m' j := by
    dsimp only [r,u]
    rw [coeff_sub,coeff_C_mul,coeff_map,integerPart_coeff d m' j hjd]
    rfl
  have hcoeff (j : ℕ) (hj : 0 < j) (hjd : j ≤ d) :
      r.coeff j = (q:ℝ)*p.coeff j - m j := by
    rw [hcoef j hjd]
    simp only [m',ite_eq_right (Nat.ne_of_gt hj)]
  refine ⟨u,r,rfl,hdeg,hcoeff,?_⟩
  intro x hx
  apply eval_bound d N A hN r hdeg ?_ (fun j hj hjd => by rw [hcoeff j hj hjd]; exact hm j hj hjd) x hx
  rw [hcoef 0 (Nat.zero_le _)]
  simp only [m',ite_eq_left rfl]
  rw [abs_of_nonneg (sub_nonneg.mpr (Int.floor_le _))]
  linarith [Int.lt_floor_add_one ((q:ℝ)*p.coeff 0)]

 
lemma residual_near_integer (p r : ℝ[X]) (u : ℤ[X]) (q n z : ℤ) (ε : ℝ)
    (hr : r = C (q:ℝ)*p - u.map (Int.castRingHom ℝ))
    (hz : |p.eval (n:ℝ)-z| ≤ ε) :
    ∃ z' : ℤ, |r.eval (n:ℝ)-z'| ≤ |(q:ℝ)| * ε := by
  refine ⟨q*z-u.eval n,?_⟩
  have he : r.eval (n:ℝ) - ((q*z-u.eval n:ℤ):ℝ) = (q:ℝ)*(p.eval (n:ℝ)-z) := by
    rw [hr,eval_sub,eval_mul,eval_C,eval_map]
    have hu : eval₂ (Int.castRingHom ℝ) (n:ℝ) u = ((u.eval n:ℤ):ℝ) :=
      eval₂_at_apply (Int.castRingHom ℝ) n
    rw [hu]
    push_cast
    ring
  rw [he,abs_mul]
  exact mul_le_mul_of_nonneg_left hz (abs_nonneg _)

end
end PolynomialIntegralResidual

end
end
end
end

end OAI
