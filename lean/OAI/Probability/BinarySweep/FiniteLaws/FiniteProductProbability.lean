import Mathlib

namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace BinaryCoordinateSweeps.Sparse
variable {I Ω : Type*} [Fintype I] [DecidableEq I] [Fintype Ω]

def productWeight (p : Ω → ℝ) (x : I → Ω) : ℝ := ∏ i, p (x i)

def productProbability (p : Ω → ℝ) (E : (I → Ω) → Prop) : ℝ :=
  ∑ x, productWeight p x * (if E x then 1 else 0)

omit [DecidableEq I] [Fintype Ω] in
lemma productWeight_nonneg {p : Ω → ℝ} (hp : ∀ u, 0 ≤ p u) (x : I → Ω) :
    0 ≤ productWeight p x := Finset.prod_nonneg (fun i _ => hp (x i))

lemma productWeight_sum (p : Ω → ℝ) (hp : ∑ u, p u = 1) :
    ∑ x : I → Ω, productWeight p x = 1 := by
  unfold productWeight
  rw [← Fintype.prod_sum]
  simp [hp]

omit [DecidableEq I] in
lemma indicator_prod (P : I → Prop) :
    (∏ i, (if P i then (1:ℝ) else 0)) = if ∀ i, P i then 1 else 0 := by
  classical
  by_cases h : ∀ i, P i
  · simp [h]
  · obtain ⟨i,hi⟩ := not_forall.mp h
    rw [ite_eq_right h]
    exact Finset.prod_eq_zero (Finset.mem_univ i) (ite_eq_right hi)

omit [DecidableEq I] [Fintype Ω] in
lemma productWeight_split (p : Ω → ℝ) (T : I → Prop) [DecidablePred T]
    (u : {i // T i} → Ω) (v : {i // ¬ T i} → Ω) :
    productWeight p ((Equiv.piEquivPiSubtypeProd T (fun _ => Ω)).symm (u,v)) =
      productWeight p u * productWeight p v := by
  unfold productWeight
  rw [← Fintype.prod_subtype_mul_prod_subtype T]
  congr 1
  · apply Finset.prod_congr rfl
    intro i _
    simp [Equiv.piEquivPiSubtypeProd_symm_apply,i.property]
  · apply Finset.prod_congr rfl
    intro i _
    simp [Equiv.piEquivPiSubtypeProd_symm_apply,i.property]

lemma productProbability_nonneg {p : Ω → ℝ} (hp : ∀ u, 0 ≤ p u)
    (E : (I → Ω) → Prop) : 0 ≤ productProbability p E := by
  apply Finset.sum_nonneg
  intro x _
  exact mul_nonneg (productWeight_nonneg hp x) (by split_ifs <;> norm_num)

lemma productProbability_mono {p : Ω → ℝ} (hp : ∀ u, 0 ≤ p u)
    {E F : (I → Ω) → Prop} (h : ∀ x, E x → F x) :
    productProbability p E ≤ productProbability p F := by
  apply Finset.sum_le_sum
  intro x _
  apply mul_le_mul_of_nonneg_left _ (productWeight_nonneg hp x)
  by_cases hx : E x
  · simp [hx,h x hx]
  · simp [hx]; split_ifs <;> norm_num

lemma productProbability_union_le {J : Type*} [Fintype J] {p : Ω → ℝ}
    (hp : ∀ u, 0 ≤ p u) (E : J → (I → Ω) → Prop) :
    productProbability p (fun x => ∃ j, E j x) ≤ ∑ j, productProbability p (E j) := by
  unfold productProbability
  rw [Finset.sum_comm]
  apply Finset.sum_le_sum
  intro x _
  rw [← Finset.mul_sum]
  apply mul_le_mul_of_nonneg_left _ (productWeight_nonneg hp x)
  by_cases h : ∃ j, E j x
  · obtain ⟨j,hj⟩ := h
    rw [ite_eq_left ⟨j,hj⟩]
    exact (show (1:ℝ) ≤ if E j x then 1 else 0 by simp [hj]).trans
      (Finset.single_le_sum (f:=fun i:J => if E i x then (1:ℝ) else 0) (fun i _ => by split_ifs <;> norm_num) (Finset.mem_univ j))
  · rw [ite_eq_right h]
    exact Finset.sum_nonneg (fun i _ => by split_ifs <;> norm_num)

theorem depthOne_probability_le {H : Type*} [Fintype H]
    (p : Ω → ℝ) (hp : ∀ u, 0 ≤ p u) (hp1 : ∑ u, p u = 1)
    (R : Ω → Ω → Prop) (ω : ℝ) (_hω : 0 ≤ ω)
    (hR : ∀ v, (∑ u, p u * (if R u v then 1 else 0)) ≤ ω)
    (T : Finset I) (f : T → {i // i ∉ T} ⊕ H) (roots : H → Ω) :
    productProbability p (fun x : I → Ω => ∀ i : T, R (x i) ((f i).elim (fun j : {i // i ∉ T} => x j.val) roots)) ≤
      ω^T.card := by
  classical
  let : Fintype T := Subtype.fintype (fun i => i ∈ T)
  let e := Equiv.piEquivPiSubtypeProd (fun i => i ∈ T) (fun _ => Ω)
  unfold productProbability
  rw [← e.symm.sum_comp]
  rw [Fintype.sum_prod_type,Finset.sum_comm]
  have he (u : T → Ω) (v : {i // i ∉ T} → Ω) (i : T) :
      R (e.symm (u,v) i) ((f i).elim (fun j : {i // i ∉ T} => e.symm (u,v) j.val) roots) ↔
        R (u i) ((f i).elim v roots) := by
    cases hf : f i with
    | inl j => simp [e,Equiv.piEquivPiSubtypeProd_symm_apply,i.property,j.property]
    | inr h => simp [e,Equiv.piEquivPiSubtypeProd_symm_apply,i.property]
  change (∑ v : {i // i ∉ T} → Ω, ∑ u : T → Ω,
    productWeight p (e.symm (u,v)) * _) ≤ _
  have hsplit (u : T → Ω) (v : {i // i ∉ T} → Ω) :
      productWeight p (e.symm (u,v)) = productWeight p u * productWeight p v := by
    exact productWeight_split p (fun i => i ∈ T) u v
  simp_rw [hsplit]
  have ht (v : {i // i ∉ T} → Ω) :
      (∑ u : T → Ω, productWeight p u *
        (if ∀ i : T, R (e.symm (u,v) i) ((f i).elim (fun j : {i // i ∉ T} => e.symm (u,v) j.val) roots)
          then 1 else 0)) ≤ ω^T.card := by
    simp_rw [he,← indicator_prod,productWeight,← Finset.prod_mul_distrib]
    rw [← Fintype.prod_sum (fun (i : T) (u : Ω) => p u * (if R u ((f i).elim v roots) then 1 else 0))]
    simpa using Finset.prod_le_prod₀ (s:=Finset.univ) (fun i _ => Finset.sum_nonneg (fun u _ =>
      mul_nonneg (hp u) (by split_ifs <;> norm_num))) (fun i _ => hR ((f i).elim v roots))
  calc
    _ = ∑ v : {i // i ∉ T} → Ω, productWeight p v *
        (∑ u : T → Ω, productWeight p u *
          (if ∀ i : T, R (e.symm (u,v) i) ((f i).elim (fun j : {i // i ∉ T} => e.symm (u,v) j.val) roots)
            then 1 else 0)) := by
      apply Finset.sum_congr rfl
      intro v _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro u _
      rw [mul_assoc, mul_left_comm]
      congr 2
      simp only [he]
    _ ≤ ∑ v : {i // i ∉ T} → Ω, productWeight p v * ω^T.card :=
      Finset.sum_le_sum (fun v _ => mul_le_mul_of_nonneg_left (ht v) (productWeight_nonneg hp v))
    _ = ω^T.card := by rw [← Finset.sum_mul,productWeight_sum p hp1,one_mul]

end BinaryCoordinateSweeps.Sparse

end

end OAI
