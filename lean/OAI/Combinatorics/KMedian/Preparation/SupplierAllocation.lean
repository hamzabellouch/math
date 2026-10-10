import Mathlib

namespace OAI

section
section
namespace MetricKMedian.Preparation
open Finset
variable {I T E : Type} [Fintype I] [DecidableEq I]
  [Fintype T] [DecidableEq T] [Fintype E]

def supplierOutside (σ : E → I ⊕ T) (q : E → ℝ) (i : I) : ℝ :=
  ∑ e, if σ e=Sum.inl i then q e else 0

def supplierBundle (σ : E → I ⊕ T) (q : E → ℝ) (t : T) : ℝ :=
  ∑ e, if σ e=Sum.inr t then q e else 0

theorem supplier_partition (σ : E → I ⊕ T) (q : E → ℝ) :
    (∑ i, supplierOutside σ q i)+(∑ t, supplierBundle σ q t)=∑ e, q e := by
  simp only [supplierOutside,supplierBundle]
  rw [sum_comm, sum_comm (s := (univ : Finset T)), ← sum_add_distrib]
  apply sum_congr rfl
  intro e _
  cases h : σ e with
  | inl i => simp only [Sum.inl.injEq,Sum.inl_ne_inr,ite_false,sum_const_zero,add_zero,
      sum_ite_eq,mem_univ,ite_true]
  | inr t => simp only [Sum.inr.injEq,Sum.inr_ne_inl,ite_false,sum_const_zero,zero_add,
      sum_ite_eq,mem_univ,ite_true]

theorem supplier_charge (σ : E → I ⊕ T) (q : E → ℝ) (b : I → ℝ) (c : T → ℝ) :
    (∑ i, supplierOutside σ q i*b i)+(∑ t, supplierBundle σ q t*c t)=
      ∑ e, q e*(Sum.elim b c (σ e)) := by
  simp only [supplierOutside,supplierBundle,sum_mul]
  rw [sum_comm, sum_comm (s := (univ : Finset T)), ← sum_add_distrib]
  apply sum_congr rfl
  intro e _
  cases h : σ e with
  | inl i => simp only [Sum.inl.injEq,Sum.inl_ne_inr,ite_false,zero_mul,sum_const_zero,
      add_zero,ite_mul,sum_ite_eq,mem_univ,ite_true,Sum.elim_inl]
  | inr t => simp only [Sum.inr.injEq,Sum.inr_ne_inl,ite_false,zero_mul,sum_const_zero,
      zero_add,ite_mul,sum_ite_eq,mem_univ,ite_true,Sum.elim_inr]

theorem allocate_suppliers (σ : E → I ⊕ T) (q : E → ℝ) (s : T)
    (u : I → ℝ) (Y : T → I → ℝ) (p : T → ℝ) (d : I → ℝ) (R : E → ℝ)
    (hY : ∀ t i, 0 ≤ Y t i) (hp : ∀ t, ∑ i, Y t i=p t)
    (hhalf : ∀ t, (1/2:ℝ) ≤ p t) (hq : ∀ e, 0 ≤ q e)
    (htotal : (∑ e, q e)=1-p s)
    (hout : ∀ i, supplierOutside σ q i ≤ u i)
    (hself : supplierBundle σ q s=0)
    (hR : ∀ e, 0 < q e → match σ e with
      | .inl i => d i ≤ R e
      | .inr t => ∀ i, 0 < Y t i → d i ≤ R e) :
    ∃ r : I ⊕ (T × I) → ℝ,
      (∀ a, 0 ≤ r a ∧ r a ≤ Sum.elim u (fun ti => Y ti.1 ti.2) a) ∧
      (∑ a, r a)=1 ∧
      (∑ a, r a*(Sum.elim d (fun ti => d ti.2) a)) ≤
        (∑ i, Y s i*d i)+(∑ e, q e*R e) := by
  classical
  let U := supplierOutside σ q
  let B := supplierBundle σ q
  have hu0 : ∀ i, 0 ≤ U i := fun i => sum_nonneg (fun e _ => by
    split_ifs; exact hq e; exact le_rfl)
  have hb0 : ∀ t, 0 ≤ B t := fun t => sum_nonneg (fun e _ => by
    split_ifs; exact hq e; exact le_rfl)
  have hpp : ∀ t, 0 < p t := fun t => lt_of_lt_of_le (by norm_num) (hhalf t)
  have hbcap : ∀ t, B t ≤ p t := by
    intro t
    calc
      B t ≤ ∑ e, q e := sum_le_sum (fun e _ => by
        split_ifs; exact le_rfl; exact hq e)
      _ = 1-p s := htotal
      _ ≤ 1/2 := by linarith only [hhalf s]
      _ ≤ p t := hhalf t
  let r : I ⊕ (T × I) → ℝ := Sum.elim U
    (fun ti => (if ti.1=s then Y ti.1 ti.2 else 0)+(B ti.1/p ti.1)*Y ti.1 ti.2)
  have hr : ∀ a, 0 ≤ r a ∧ r a ≤ Sum.elim u (fun ti => Y ti.1 ti.2) a := by
    rintro (i | ⟨t,i⟩)
    · exact ⟨hu0 i,hout i⟩
    · change 0 ≤ (if t=s then Y t i else 0)+(B t/p t)*Y t i ∧
        (if t=s then Y t i else 0)+(B t/p t)*Y t i ≤ Y t i
      have hf0 : 0 ≤ B t/p t := div_nonneg (hb0 t) (hpp t).le
      have hf1 : B t/p t ≤ 1 := (div_le_one (hpp t)).mpr (hbcap t)
      by_cases ht : t=s
      · subst t
        simp only [ite_true,B,hself,zero_div,zero_mul,add_zero]
        exact ⟨hY s i,le_rfl⟩
      · simp only [ite_eq_right ht,zero_add]
        exact ⟨mul_nonneg hf0 (hY t i),mul_le_of_le_one_left (hY t i) hf1⟩
  have hmass : (∑ a, r a)=1 := by
    simp only [r,Fintype.sum_sum_type,Fintype.sum_prod_type,Sum.elim_inl,Sum.elim_inr,
      sum_add_distrib,← mul_sum,hp]
    simp only [sum_ite_irrel,sum_const_zero,hp,sum_ite_eq',mem_univ,ite_true]
    have hcancel : ∀ t, B t/p t*p t=B t := fun t => div_mul_cancel₀ _ (hpp t).ne'
    simp only [hcancel]
    have ht := supplier_partition σ q
    rw [htotal] at ht
    dsimp only [U,B]
    linarith only [ht]
  refine ⟨r,hr,hmass,?_⟩
  let c := fun t => (∑ i, Y t i*d i)/p t
  have hcost : (∑ a, r a*(Sum.elim d (fun ti => d ti.2) a))=
      (∑ i, Y s i*d i)+(∑ i, U i*d i)+(∑ t, B t*c t) := by
    simp only [r,Fintype.sum_sum_type,Fintype.sum_prod_type,Sum.elim_inl,Sum.elim_inr,
      add_mul,sum_add_distrib,ite_mul,zero_mul]
    simp only [sum_ite_irrel,sum_const_zero,sum_ite_eq',mem_univ,ite_true]
    have he : ∀ t, (∑ i, (B t/p t)*Y t i*d i)=B t*c t := by
      intro t
      simp only [c,mul_assoc,← mul_sum]
      ring
    simp only [he]
    ring
  rw [hcost,add_assoc]
  apply add_le_add le_rfl
  change (∑ i, supplierOutside σ q i*d i)+(∑ t, supplierBundle σ q t*c t) ≤ _
  rw [supplier_charge]
  apply sum_le_sum
  intro e _
  by_cases hqe : q e=0
  · simp only [hqe,zero_mul,le_refl]
  · have hqe' : 0 < q e := lt_of_le_of_ne (hq e) (Ne.symm hqe)
    apply mul_le_mul_of_nonneg_left _ (hq e)
    have hc := hR e hqe'
    cases he : σ e with
    | inl i => simpa only [he,Sum.elim_inl] using hc
    | inr t =>
      simp only [Sum.elim_inr]
      simp only [he] at hc
      apply (div_le_iff₀ (hpp t)).mpr
      rw [← hp t,mul_sum]
      apply sum_le_sum
      intro i _
      by_cases hi : Y t i=0
      · simp only [hi,zero_mul,mul_zero,le_refl]
      · exact (mul_le_mul_of_nonneg_left (hc i (lt_of_le_of_ne (hY t i) (Ne.symm hi)))
          (hY t i)).trans_eq (mul_comm _ _)

end MetricKMedian.Preparation
end
end

end OAI
