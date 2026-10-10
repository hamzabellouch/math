import OAI.InformationTheory.AmplitudeDamping.SequentialDecoder

namespace OAI

noncomputable section

universe u_1 u_2 u_3

section
open scoped BigOperators
namespace GAD
variable {α : Type u_1} [Fintype α]

theorem iid_coordinate (q : α → ℝ) (hs : ∑ a, q a=1) (f : α → ℝ) (n : ℕ) (i : Fin n) :
    (∑ x : Fin n → α, iidWeight q n x*f (x i))=∑ a, q a*f a := by
  induction n with
  | zero => exact Fin.elim0 i
  | succ n ih =>
      rw [iid_split_sum]
      refine Fin.cases ?_ (fun i ↦ ?_) i
      · simp only [Fin.cons_zero,mul_assoc,← Finset.mul_sum,← Finset.sum_mul,
          iidWeight_total q hs n,one_mul]
      · simp only [Fin.cons_succ,mul_assoc,← Finset.mul_sum,ih,← Finset.sum_mul,hs,one_mul]

theorem iid_pair (q : α → ℝ) (hs : ∑ a, q a=1) (f : α → α → ℝ)
    (n : ℕ) (i j : Fin n) (hij : i ≠ j) :
    (∑ x : Fin n → α, iidWeight q n x*f (x i) (x j))=∑ a, ∑ b, q a*q b*f a b := by
  induction n with
  | zero => exact Fin.elim0 i
  | succ n ih =>
      rw [iid_split_sum]
      revert hij
      refine Fin.cases ?_ (fun i ↦ ?_) i
      · refine Fin.cases ?_ (fun j hij ↦ ?_) j
        · intro h; exact (h rfl).elim
        · simp only [Fin.cons_zero,Fin.cons_succ,mul_assoc,← Finset.mul_sum,
            iid_coordinate q hs]
      · refine Fin.cases ?_ (fun j hij ↦ ?_) j
        · intro _
          simp only [Fin.cons_zero,Fin.cons_succ,mul_assoc,← Finset.mul_sum]
          have he (b : α) := iid_coordinate q hs (fun a ↦ f a b) n i
          simp only [he,Finset.mul_sum]
          rw [Finset.sum_comm]
          apply Finset.sum_congr rfl
          intro a _
          apply Finset.sum_congr rfl
          intro b _
          ring
        · have hij' : i ≠ j := by intro h; exact hij (congrArg Fin.succ h)
          simp only [Fin.cons_succ,mul_assoc,← Finset.mul_sum,ih i j hij',
            ← Finset.sum_mul,hs,one_mul]

/-- A finite average cannot be strictly below every sampled value. -/
theorem exists_le_weighted_average (q : α → ℝ) (hq : ∀ a, 0 ≤ q a)
    (hs : ∑ a, q a=1) (f : α → ℝ) : ∃ a, f a ≤ ∑ b, q b*f b := by
  by_contra! h
  obtain ⟨a,ha⟩ : ∃ a, 0 < q a := by
    by_contra! hz
    have hzero : ∀ a, q a=0 := fun a ↦ le_antisymm (hz a) (hq a)
    simp only [hzero,Finset.sum_const_zero] at hs
    norm_num at hs
  have hh : (∑ b, q b*(∑ c, q c*f c)) < ∑ b, q b*f b := by
    apply Finset.sum_lt_sum
    · intro b _; exact mul_le_mul_of_nonneg_left (h b).le (hq b)
    · exact ⟨a,Finset.mem_univ a,mul_lt_mul_of_pos_left (h a) ha⟩
  rw [← Finset.sum_mul,hs,one_mul] at hh
  exact lt_irrefl _ hh

end GAD

end

open scoped BigOperators ComplexOrder MatrixOrder
open Matrix
namespace GAD
variable {ι : Type u_2} {α : Type u_3} [Fintype ι] [Fintype α] [DecidableEq ι]

theorem packing_cross_bound (q : α → ℝ) (hq : ∀ a, 0 ≤ q a) (hs : ∑ a, q a=1)
    (A Q : α → Matrix ι ι ℂ) (hQ : ∀ a, IsProjection (Q a))
    (P : Matrix ι ι ℂ) (hP : IsProjection P) {c r : ℝ} (hc : 0 ≤ c)
    (hr : ∀ a, (Q a).trace.re ≤ r)
    (hp : (c • P-P*(∑ a, q a • A a)*P).PosSemidef) :
    (∑ a, ∑ b, q a*q b*(Q b*(P*A a*P)).trace.re) ≤ c*r := by
  have hm (b : α) : (∑ a, q a*(Q b*(P*A a*P)).trace.re)=
      (Q b*(P*(∑ a, q a • A a)*P)).trace.re := by
    simp only [Matrix.mul_sum,Matrix.sum_mul,Matrix.mul_smul,Matrix.smul_mul,Matrix.trace_sum,
      Matrix.trace_smul,Complex.re_sum,Complex.real_smul,Complex.mul_re,Complex.ofReal_re,
      Complex.ofReal_im,zero_mul,sub_zero]
  have hb (b : α) : (∑ a, q a*(Q b*(P*A a*P)).trace.re) ≤ c*r := by
    rw [hm]
    have h1 := trace_product_mono (hQ b).posSemidef hp
    simp only [Matrix.mul_smul,Matrix.trace_smul,Complex.real_smul,Complex.mul_re,
      Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero] at h1
    have h2 := trace_product_mono (hQ b).posSemidef hP.complement.posSemidef
    simp only [Matrix.mul_one] at h2
    have h3 := mul_le_mul_of_nonneg_left (h2.trans (hr b)) hc
    exact h1.trans h3
  calc
    _ = ∑ b, q b*(∑ a, q a*(Q b*(P*A a*P)).trace.re) := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro b _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro a _; ring
    _ ≤ ∑ b, q b*(c*r) := Finset.sum_le_sum (fun b _ ↦ mul_le_mul_of_nonneg_left (hb b) (hq b))
    _ = _ := by rw [← Finset.sum_mul,hs,one_mul]

/-- Finite iid quantum packing, using an explicit sequential collective POVM. -/
theorem exists_packed_measurement (q : α → ℝ) (hq : ∀ a, 0 ≤ q a) (hs : ∑ a, q a=1)
    (A Q : α → Matrix ι ι ℂ) (hA : ∀ a, IsState (A a)) (hQ : ∀ a, IsProjection (Q a))
    (P : Matrix ι ι ℂ) (hP : IsProjection P) {a b c r : ℝ} (hc : 0 ≤ c) (hr0 : 0 ≤ r)
    (hga : (∑ x, q x*(1-(P*A x).trace.re)) ≤ a)
    (hcb : (∑ x, q x*(1-(Q x*A x).trace.re)) ≤ b)
    (hr : ∀ x, (Q x).trace.re ≤ r)
    (hcp : (c • P-P*(∑ x, q x • A x)*P).PosSemidef)
    (M : ℕ) (hM : 0 < M) :
    ∃ (x : Fin M → α) (D : Fin M → Matrix ι ι ℂ),
      (∀ m, (D m).PosSemidef) ∧ (∑ m, D m=1) ∧
      1-(∑ m, (D m*A (x m)).trace.re)/(M:ℝ) ≤ 9*a+8*b+4*(M:ℝ)*c*r := by
  classical
  let ga : α → ℝ := fun x ↦ 1-(P*A x).trace.re
  let cb : α → ℝ := fun x ↦ 1-(Q x*A x).trace.re
  let cr : α → α → ℝ := fun x y ↦ (Q y*(P*A x*P)).trace.re
  let cost : (Fin M → α) → Fin M → ℝ := fun x m ↦
    9*ga (x m)+8*cb (x m)+4*∑ j : Fin M, if j=m then 0 else cr (x m) (x j)
  let B : (Fin M → α) → ℝ := fun x ↦ (∑ m, cost x m)/(M:ℝ)
  have hcross := packing_cross_bound q hq hs A Q hQ P hP hc hr hcp
  have hcross' (m j : Fin M) :
      (∑ x : Fin M → α, iidWeight q M x*(if j=m then 0 else cr (x m) (x j))) ≤ c*r := by
    by_cases hj : j=m
    · simp only [hj,ite_true,mul_zero,Finset.sum_const_zero]
      exact mul_nonneg hc hr0
    · simp only [ite_eq_right hj]
      rw [iid_pair q hs cr M m j (Ne.symm hj)]
      exact hcross
  have hcost (m : Fin M) : (∑ x, iidWeight q M x*cost x m) ≤ 9*a+8*b+4*(M:ℝ)*c*r := by
    have h1 := iid_coordinate q hs ga M m
    have h2 := iid_coordinate q hs cb M m
    have h3 : (∑ x, iidWeight q M x*(∑ j : Fin M, if j=m then 0 else cr (x m) (x j))) ≤ (M:ℝ)*c*r := by
      simp only [Finset.mul_sum]
      rw [Finset.sum_comm]
      calc
        _ ≤ ∑ _j : Fin M, c*r := Finset.sum_le_sum (fun j _ ↦ hcross' m j)
        _ = _ := by simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]; ring
    dsimp only [cost]
    have hex : (∑ x, iidWeight q M x*(9*ga (x m)+8*cb (x m)+4*∑ j : Fin M, if j=m then 0 else cr (x m) (x j))) =
        9*(∑ x, iidWeight q M x*ga (x m))+8*(∑ x, iidWeight q M x*cb (x m))+
          4*(∑ x, iidWeight q M x*(∑ j : Fin M, if j=m then 0 else cr (x m) (x j))) := by
      have hscl (d : ℝ) (f : (Fin M → α) → ℝ) :
          (∑ x, iidWeight q M x*(d*f x))=d*∑ x, iidWeight q M x*f x := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro x _; ring
      simp only [mul_add,Finset.sum_add_distrib,hscl]
    rw [hex,h1,h2]
    change (∑ x, q x*ga x) ≤ a at hga
    change (∑ x, q x*cb x) ≤ b at hcb
    linarith
  have hB : (∑ x, iidWeight q M x*B x) ≤ 9*a+8*b+4*(M:ℝ)*c*r := by
    have hMp : 0 < (M:ℝ) := by exact_mod_cast hM
    simp only [B,← mul_div_assoc,Finset.mul_sum,← Finset.sum_div]
    rw [Finset.sum_comm]
    apply (div_le_iff₀ hMp).mpr
    have hh := Finset.sum_le_sum (s := Finset.univ) (fun m _ ↦ hcost m)
    simpa only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,mul_comm] using hh
  obtain ⟨x,hx⟩ := exists_le_weighted_average (iidWeight q M) (iidWeight_nonneg q hq M)
    (iidWeight_total q hs M) B
  obtain ⟨D,hD,hDs,herr⟩ := sequential_decoder_bound hM P hP (fun m ↦ Q (x m)) (fun m ↦ A (x m))
    (fun m ↦ hQ (x m)) (fun m ↦ hA (x m))
  refine ⟨x,D,hD,hDs,?_⟩
  have hh := Finset.sum_le_sum (s := Finset.univ) (fun m _ ↦ herr m)
  change (∑ m, (1-(D m*A (x m)).trace.re)) ≤ ∑ m, cost x m at hh
  have hMt : (M:ℝ) ≠ 0 := by exact_mod_cast hM.ne'
  have hi : 1-(∑ m, (D m*A (x m)).trace.re)/(M:ℝ) ≤ B x := by
    change _ ≤ (∑ m, cost x m)/(M:ℝ)
    rw [show (1:ℝ)=(M:ℝ)/(M:ℝ) from (div_self hMt).symm,← sub_div]
    apply div_le_div_of_nonneg_right _ (by positivity)
    simpa only [Finset.sum_sub_distrib,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,mul_one] using hh
  exact hi.trans (hx.trans hB)

end GAD

end

end OAI
