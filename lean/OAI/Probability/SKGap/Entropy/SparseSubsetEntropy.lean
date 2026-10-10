import Mathlib
import OAI.Probability.SKGap.Model

namespace OAI

section
noncomputable section
namespace SKGap
open MeasureTheory Real Set Filter
open scoped BigOperators Topology
variable {ι : Type*} [Fintype ι]

def smallSupports (α : ℝ) : Finset (Finset ι) := by
  classical
  exact Finset.univ.powerset.filter (fun S=>(S.card:ℝ) ≤ α*(Fintype.card ι:ℝ))

lemma powerset_exponential_sum (l : ℝ) :
    (∑ S ∈ (Finset.univ : Finset ι).powerset,exp (-l*(S.card:ℝ)))=
      (1+exp (-l))^(Fintype.card ι) := by
  classical
  have he := Finset.prod_one_add (s:=Finset.univ) (f:=fun _ : ι=>exp (-l))
  simp only [Finset.prod_const,Finset.card_univ] at he
  rw [he]
  apply Finset.sum_congr rfl
  intro S _
  rw [← exp_nat_mul]
  congr 1
  ring

lemma smallSupports_card_bound {l α : ℝ} (hl : 0 ≤ l) :
    ((smallSupports (ι:=ι) α).card:ℝ) ≤
      exp ((Fintype.card ι:ℝ)*(l*α+log (1+exp (-l)))) := by
  classical
  have hlo : ((smallSupports (ι:=ι) α).card:ℝ)*exp (-l*α*(Fintype.card ι:ℝ)) ≤
      ∑ S ∈ (smallSupports (ι:=ι) α),exp (-l*(S.card:ℝ)) := by
    rw [← nsmul_eq_mul,← Finset.sum_const]
    apply Finset.sum_le_sum
    intro S hS
    apply exp_le_exp.mpr
    have hc := (Finset.mem_filter.mp hS).2
    nlinarith only [mul_le_mul_of_nonneg_left hc hl]
  have hhi : (∑ S ∈ (smallSupports (ι:=ι) α),exp (-l*(S.card:ℝ))) ≤
      ∑ S ∈ (Finset.univ : Finset ι).powerset,exp (-l*(S.card:ℝ)) :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      (fun _ _ _=>(exp_pos _).le)
  have hp : (1+exp (-l))^(Fintype.card ι)=
      exp ((Fintype.card ι:ℝ)*log (1+exp (-l))) := by
    rw [exp_nat_mul,exp_log (by positivity)]
  rw [powerset_exponential_sum,hp] at hhi
  have hh := hlo.trans hhi
  apply (mul_le_mul_iff_left₀ (exp_pos (-l*α*(Fintype.card ι:ℝ)))).mp
  calc
    _ ≤ exp ((Fintype.card ι:ℝ)*log (1+exp (-l))) := hh
    _ = _ := by rw [← exp_add];congr 1;ring

lemma exists_small_support_exponent {δ : ℝ} (hδ : 0 < δ) :
    ∃ l α : ℝ,0 < l ∧ 0 < α ∧ α < 1/2 ∧ l*α+log (1+exp (-l)) < δ := by
  have ht : Tendsto (fun x : ℝ=>log (1+exp (-x))) atTop (𝓝 0) := by
    have h := (tendsto_const_nhds.add tendsto_exp_neg_atTop_nhds_zero).log (by norm_num : (1:ℝ)+0 ≠ 0)
    simpa only [add_zero,log_one] using h
  have hev := ht.eventually (gt_mem_nhds (by linarith : (0:ℝ) < δ/2))
  obtain ⟨l,hl,hsmall⟩ := ((eventually_gt_atTop (0:ℝ)).and hev).exists
  let α := min (1/4:ℝ) (δ/(4*(l+1)))
  have ha : 0 < α := lt_min (by norm_num) (by positivity)
  have ha' : α ≤ δ/(4*(l+1)) := min_le_right _ _
  have hn : l*α < δ/2 := by
    have hum : α*(4*(l+1)) ≤ δ := (le_div_iff₀ (by positivity)).mp ha'
    nlinarith only [hum,hl,ha,hδ,mul_pos hl ha]
  exact ⟨l,α,hl,ha,(min_le_left _ _).trans_lt (by norm_num),by linarith only [hn,hsmall]⟩

theorem sparse_union_bound {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsFiniteMeasure μ]
    (E : Finset ι→Set Ω) {l α C q : ℝ} (hl : 0 ≤ l) (hC : 0 ≤ C)
    (hE : ∀ S∈smallSupports (ι:=ι) α,μ.real (E S) ≤ C*exp (-(Fintype.card ι:ℝ)*q)) :
    μ.real (⋃ S∈smallSupports (ι:=ι) α,E S) ≤
      C*exp (-(Fintype.card ι:ℝ)*(q-(l*α+log (1+exp (-l))))) := by
  classical
  calc
    _ ≤ ∑ S ∈ smallSupports (ι:=ι) α,μ.real (E S) := measureReal_biUnion_finset_le _ _
    _ ≤ ∑ _S ∈ smallSupports (ι:=ι) α,C*exp (-(Fintype.card ι:ℝ)*q) :=
      Finset.sum_le_sum hE
    _ = ((smallSupports (ι:=ι) α).card:ℝ)*(C*exp (-(Fintype.card ι:ℝ)*q)) := by simp
    _ ≤ exp ((Fintype.card ι:ℝ)*(l*α+log (1+exp (-l))))*(C*exp (-(Fintype.card ι:ℝ)*q)) :=
      mul_le_mul_of_nonneg_right (smallSupports_card_bound hl) (by positivity)
    _ = _ := by rw [mul_left_comm,← exp_add];congr 2;ring
end SKGap

end
end

end OAI
