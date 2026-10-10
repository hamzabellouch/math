import OAI.Combinatorics.PerfectMatching.DyadicEntropy

namespace OAI

section

namespace BinaryMatching
noncomputable section
open Finset
variable {n : ℕ}

lemma sum_pairs (f : Fin n → Fin n → ℝ) :
    (∑ e : Pair n, f e.val.1 e.val.2)=∑ i,∑ j,if i < j then f i j else 0 := by
  let s : Finset (Fin n × Fin n) := univ.filter (fun ij => ij.1 < ij.2)
  have hs : ∀ ij : Fin n × Fin n,ij∈s ↔ ij.1 < ij.2 := by simp [s]
  rw [←sum_subtype s hs (fun ij => f ij.1 ij.2)]
  rw [show s=univ.filter (fun ij => ij.1 < ij.2) from rfl,sum_filter,Fintype.sum_prod_type]

lemma sum_skip (g : Fin n → ℝ) (v : Fin n) :
    (∑ j,if j=v then 0 else g j)=(∑ j,g j)-g v := by
  have hh : (∑ j,g j)=(∑ j,if j=v then 0 else g j)+g v := by
    calc
      _ = ∑ j, ((if j=v then 0 else g j)+(if j=v then g j else 0)) := by
        apply sum_congr rfl; intro j _; split_ifs <;> simp
      _ = _ := by rw [sum_add_distrib]; simp
  linarith

lemma degree_from_symm (f : Fin n → Fin n → ℝ) (hf : ∀ i j,f i j=f j i) (v : Fin n) :
    (completeGraph n).degree (fun e => f e.val.1 e.val.2) v =
      ∑ j,if j=v then 0 else f v j := by
  change (∑ e : Pair n,if e.val.1=v ∨ e.val.2=v then f e.val.1 e.val.2 else 0)=_
  rw [sum_pairs (fun i j => if i=v ∨ j=v then f i j else 0)]
  have he (i j : Fin n) :
      (if i < j then (if i=v ∨ j=v then f i j else 0) else 0) =
      (if i=v then (if i < j then f i j else 0) else 0)+
      (if j=v then (if i < j then f i j else 0) else 0) := by
    by_cases hiv : i=v <;> by_cases hjv : j=v <;> by_cases hij : i < j <;> simp_all
  simp_rw [he,sum_add_distrib]
  have hleft : (∑ i,∑ j,if i=v then (if i < j then f i j else 0) else 0)=
      ∑ j,if v < j then f v j else 0 := by
    simp [Finset.sum_ite_irrel]
  have hright : (∑ i,∑ j,if j=v then (if i < j then f i j else 0) else 0)=
      ∑ j,if j < v then f v j else 0 := by
    simp only [sum_ite_eq',mem_univ,ite_true]
    apply sum_congr rfl; intro j _; rw [hf j v]
  rw [hleft,hright,←sum_add_distrib]
  apply sum_congr rfl; intro j _
  rcases lt_trichotomy j v with h|h|h
  · simp [h, ne_of_lt h, not_lt_of_ge h.le]
  · subst j; simp
  · simp [h, ne_of_gt h, not_lt_of_ge h.le]

lemma degree_constant (b : ℝ) (v : Fin n) :
    (completeGraph n).degree (fun _ => b) v=((n:ℝ)-1)*b := by
  rw [degree_from_symm (fun _ _ => b) (fun _ _ => rfl),sum_skip]
  simp; ring

lemma degree_vertex_add (d : Fin n → ℝ) (v : Fin n) :
    (completeGraph n).degree (fun e => d e.val.1+d e.val.2) v =
      ((n:ℝ)-2)*d v+∑ j,d j := by
  rw [degree_from_symm (fun i j => d i+d j) (fun _ _ => add_comm _ _),sum_skip]
  simp only [sum_add_distrib,sum_const,nsmul_eq_mul,card_univ,Fintype.card_fin]
  ring

lemma cut_from_symm (f : Fin n → Fin n → ℝ) (hf : ∀ i j,f i j=f j i)
    (S : Finset (Fin n)) :
    (completeGraph n).cutMass (fun e => f e.val.1 e.val.2) S =
      ∑ i∈S,∑ j∈Sᶜ,f i j := by
  unfold MatchingEntropy.LooplessGraph.cutMass MatchingEntropy.LooplessGraph.cut
  rw [sum_filter]
  change (∑ e : Pair n,if (e.val.1∈S ∧ e.val.2∉S) ∨ (e.val.1∉S ∧ e.val.2∈S)
    then f e.val.1 e.val.2 else 0)=_
  rw [sum_pairs (fun i j => if (i∈S ∧ j∉S) ∨ (i∉S ∧ j∈S) then f i j else 0)]
  have he (i j : Fin n) :
      (if i < j then (if (i∈S ∧ j∉S) ∨ (i∉S ∧ j∈S) then f i j else 0) else 0) =
        (if i < j ∧ i∈S ∧ j∉S then f i j else 0)+
        (if i < j ∧ i∉S ∧ j∈S then f i j else 0) := by
    by_cases hij : i < j <;> by_cases hi : i∈S <;> by_cases hj : j∈S <;> simp [hij,hi,hj]
  simp_rw [he,sum_add_distrib]
  have hswap : (∑ i,∑ j,if i < j ∧ i∉S ∧ j∈S then f i j else 0)=
      ∑ i,∑ j,if j < i ∧ i∈S ∧ j∉S then f i j else 0 := by
    rw [sum_comm]
    apply sum_congr rfl; intro i _
    apply sum_congr rfl; intro j _
    rw [hf j i]
    by_cases hij : j < i <;> by_cases hi : i∈S <;> by_cases hj : j∈S <;> simp [hij,hi,hj]
  rw [hswap,←sum_add_distrib]
  simp_rw [←sum_add_distrib]
  have hterm (i j : Fin n) :
      (if i < j ∧ i∈S ∧ j∉S then f i j else 0)+
        (if j < i ∧ i∈S ∧ j∉S then f i j else 0)=
        if i∈S ∧ j∉S then f i j else 0 := by
    rcases lt_trichotomy i j with h|h|h
    · simp [h,not_lt_of_ge h.le]
    · subst j; simp
    · simp [h,not_lt_of_ge h.le]
  simp_rw [hterm]
  have hS : S=univ.filter (fun i => i∈S) := by ext i; simp
  have hSc : Sᶜ=univ.filter (fun j => j∉S) := by ext j; simp
  conv_rhs => rw [hS]; rw [sum_filter]
  simp only [ite_and]
  apply sum_congr rfl; intro i _
  by_cases hi : i∈S
  · simp only [hi,ite_true]
    rw [←hS,hSc,sum_filter]
  · simp only [hi,ite_false,sum_const_zero]

lemma cut_constant (b : ℝ) (S : Finset (Fin n)) :
    (completeGraph n).cutMass (fun _ => b) S=(S.card:ℝ)*(Sᶜ.card:ℝ)*b := by
  rw [cut_from_symm (fun _ _ => b) (fun _ _ => rfl)]
  simp [mul_assoc]

lemma q_le_square : Fintype.card (Pair n) ≤ n^2 := by
  calc
    _ ≤ Fintype.card (Fin n × Fin n) := Fintype.card_subtype_le _
    _ = n^2 := by simp [pow_two]

end
end BinaryMatching
end

end OAI
