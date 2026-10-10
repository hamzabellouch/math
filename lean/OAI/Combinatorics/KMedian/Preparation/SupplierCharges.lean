import Mathlib
import OAI.Combinatorics.KMedian.Preparation.PreparationStars

namespace OAI

section
section
namespace MetricKMedian.Preparation.SupplierStars
open Finset
variable {I T : Type} [Fintype I] [DecidableEq I] [Fintype T] [DecidableEq T]

noncomputable def connectionCharge (P A : T → Finset I) (y d : I → ℝ)
    (L : T → ℝ) (κ β δ : ℝ) : Star I T → ℝ
  | .inl i => d i
  | .inr (.inl st) => κ*((∑ i ∈ A st.1 ∩ P st.2, y i*d i)/(∑ i ∈ A st.1 ∩ P st.2, y i))
  | .inr (.inr t) => (β+1+δ)*L t

omit [Fintype I] [DecidableEq I] [DecidableEq T] in
 theorem weighted_mean_charge (F : Finset I) (y d : I → ℝ) (κ : ℝ)
    (hy : ∀ i, 0 ≤ y i) :
    (∑ i ∈ F, y i)*(κ*((∑ i ∈ F, y i*d i)/(∑ i ∈ F, y i)))=κ*(∑ i ∈ F, y i*d i) := by
  by_cases hz : (∑ i ∈ F, y i)=0
  · have hc : (∑ i ∈ F, y i*d i)=0 := by
      apply sum_eq_zero
      intro i hi
      have hle := single_le_sum (fun j _ => hy j) hi
      have h0 : y i=0 := le_antisymm (hle.trans_eq hz) (hy i)
      rw [h0,zero_mul]
    simp only [hz,hc,mul_zero,zero_div]
  · field_simp

omit [Fintype I] [Fintype T] [DecidableEq T] in
 theorem connectionCharge_nonneg (P A : T → Finset I) (y d : I → ℝ)
    (L : T → ℝ) {κ β δ : ℝ} (hy : ∀ i, 0 ≤ y i) (hd : ∀ i, 0 ≤ d i)
    (hL : ∀ t, 0 ≤ L t) (hκ : 0 ≤ κ) (hβ : 0 ≤ β) (hδ : 0 ≤ δ) :
    ∀ e, 0 ≤ connectionCharge P A y d L κ β δ e := by
  rintro (i | (st | t))
  · exact hd i
  · exact mul_nonneg hκ (div_nonneg (sum_nonneg (fun i _ => mul_nonneg (hy i) (hd i)))
      (sum_nonneg (fun i _ => hy i)))
  · exact mul_nonneg (by linarith only [hβ,hδ]) (hL t)

theorem targeted_connection_charge (P A : T → Finset I) (y d : I → ℝ)
    (c L : T → ℝ) (γ κ β δ : ℝ) (hy : ∀ i, 0 ≤ y i) (s : T) :
    (∑ e, (if s ∈ targets A e then weight y P A c γ e else 0)*connectionCharge P A y d L κ β δ e)=
      (∑ i ∈ A s ∩ outside P, y i*d i)+
      κ*(∑ t, ∑ i ∈ A s ∩ P t, y i*d i)+(β+1+δ)*γ*c s*L s := by
  rw [Fintype.sum_sum_type,Fintype.sum_sum_type,Fintype.sum_prod_type]
  simp only [targets,weight,connectionCharge,mem_filter,mem_univ,true_and,mem_singleton]
  have ho : (∑ i, (if i ∈ A s then (if i ∈ outside P then y i else 0) else 0)*d i)=
      ∑ i ∈ A s ∩ outside P, y i*d i := by
    simp only [ite_mul,zero_mul,sum_ite_mem,univ_inter]
  have hb : (∑ u, ∑ t, (if s=u then ∑ i ∈ A u ∩ P t, y i else 0)*
      (κ*((∑ i ∈ A u ∩ P t, y i*d i)/(∑ i ∈ A u ∩ P t, y i))))=
      κ*(∑ t, ∑ i ∈ A s ∩ P t, y i*d i) := by
    simp only [ite_mul,zero_mul,weighted_mean_charge _ y d κ hy,
      sum_ite_irrel,sum_const_zero,sum_ite_eq,mem_univ,ite_true, mul_sum]
  have hx : (∑ t, (if s=t then γ*c t else 0)*((β+1+δ)*L t))=(β+1+δ)*γ*c s*L s := by
    simp only [ite_mul,zero_mul,sum_ite_eq,mem_univ,ite_true]
    ring
  rw [ho,hb,hx]
  ring

theorem old_charge_bound (F : Finset I) (P A : T → Finset I) (y d : I → ℝ)
    (p c L : T → ℝ) {γ κ β δ p₀ : ℝ} (hy : ∀ i, 0 ≤ y i) (hd : ∀ i, 0 ≤ d i)
    (hP : Pairwise (fun s t => Disjoint (P s) (P t))) (s : T)
    (hsub : P s ⊆ F) (hA : A s=F \ P s) (hp₀ : 0 < p₀) (hp : p₀ ≤ p s) (hκ : 1 ≤ κ) :
    (∑ i ∈ P s, y i*d i)/p s+
      (∑ e, (if s ∈ targets A e then weight y P A c γ e else 0)*connectionCharge P A y d L κ β δ e) ≤
      max (1/p₀) κ*(∑ i ∈ F, y i*d i)+(β+1+δ)*γ*c s*L s := by
  rw [targeted_connection_charge P A y d c L γ κ β δ hy s]
  let z := fun i => y i*d i
  have hz : ∀ i, 0 ≤ z i := fun i => mul_nonneg (hy i) (hd i)
  have hpart := mass_partition z P hP (A s)
  have hfull : (∑ i ∈ P s, z i)+(∑ i ∈ A s, z i)=∑ i ∈ F, z i := by
    rw [hA,add_comm,sum_sdiff hsub]
  have hmul : (∑ i ∈ P s, z i)/p s ≤ max (1/p₀) κ*(∑ i ∈ P s, z i) := by
    calc
      _ ≤ (∑ i ∈ P s, z i)/p₀ := div_le_div_of_nonneg_left (sum_nonneg (fun i _ => hz i)) hp₀ hp
      _ = (1/p₀)*(∑ i ∈ P s, z i) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (le_max_left _ _) (sum_nonneg (fun i _ => hz i))
  have hout : (∑ i ∈ A s ∩ outside P, z i) ≤ max (1/p₀) κ*(∑ i ∈ A s ∩ outside P, z i) :=
    le_mul_of_one_le_left (sum_nonneg (fun i _ => hz i)) (hκ.trans (le_max_right _ _))
  have hb : κ*(∑ t, ∑ i ∈ A s ∩ P t, z i) ≤ max (1/p₀) κ*(∑ t, ∑ i ∈ A s ∩ P t, z i) :=
    mul_le_mul_of_nonneg_right (le_max_right _ _) (sum_nonneg (fun t _ => sum_nonneg (fun i _ => hz i)))
  change (∑ i ∈ P s, z i)/p s+((∑ i ∈ A s ∩ outside P, z i)+κ*(∑ t, ∑ i ∈ A s ∩ P t, z i)+_)
    ≤ max (1/p₀) κ*(∑ i ∈ F, z i)+_
  calc
    _ ≤ max (1/p₀) κ*(∑ i ∈ P s, z i)+
        (max (1/p₀) κ*(∑ i ∈ A s ∩ outside P, z i)+
          max (1/p₀) κ*(∑ t, ∑ i ∈ A s ∩ P t, z i)+(β+1+δ)*γ*c s*L s) :=
      add_le_add hmul (add_le_add (add_le_add hout hb) le_rfl)
    _ = max (1/p₀) κ*((∑ i ∈ P s, z i)+((∑ i ∈ A s ∩ outside P, z i)+
          (∑ t, ∑ i ∈ A s ∩ P t, z i)))+(β+1+δ)*γ*c s*L s := by ring
    _ = _ := by rw [hpart,hfull]

end MetricKMedian.Preparation.SupplierStars
end
end

end OAI
