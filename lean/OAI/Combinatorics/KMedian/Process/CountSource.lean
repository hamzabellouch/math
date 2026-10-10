import Mathlib
import OAI.Combinatorics.KMedian.Process.SourceBalance
import OAI.Combinatorics.KMedian.Process.UnbalancedActions

namespace OAI

section
section
namespace MetricKMedian.SourceBalance
open Finset
variable {I : Type*} [Fintype I]

noncomputable def bias (m : I → ℝ) (p φ : ℝ) (i : I) : ℝ :=
  if 1 < m i then (1+φ)*p else p

omit [Fintype I] in
 theorem bias_lower (m : I → ℝ) {p φ : ℝ} (hp : 0 ≤ p) (hφ : 0 ≤ φ) (i : I) :
    p ≤ bias m p φ i := by
  unfold bias
  split_ifs <;> nlinarith only [mul_nonneg hp hφ]

omit [Fintype I] in
 theorem bias_upper (m : I → ℝ) {p φ : ℝ} (hp : 0 ≤ p) (hφ : 0 ≤ φ) (i : I) :
    bias m p φ i ≤ (1+φ)*p := by
  unfold bias
  split_ifs <;> nlinarith only [mul_nonneg hp hφ]

 theorem sum_biased_imbalance (m : I → ℝ) (p φ : ℝ) (hm : ∑ i, m i=Fintype.card I) :
    (∑ i, (1-m i)*bias m p φ i)=-p*φ*amount m := by
  have hpoint : ∀ i, (1-m i)*bias m p φ i=
      (1-m i)*p-φ*p*(if 1 < m i then m i-1 else 0) := by
    intro i
    unfold bias
    split_ifs <;> ring
  simp_rw [hpoint]
  rw [sum_sub_distrib, ← sum_mul, ← mul_sum]
  have hn : (∑ i, if 1 < m i then m i-1 else 0)=amount m := by
    simpa only [negative, sum_filter] using (amount_eq_negative m hm).symm
  rw [hn]
  have hz : (∑ i, (1-m i))=0 := by rw [sum_sub_distrib,hm]; simp
  rw [hz]
  ring

end MetricKMedian.SourceBalance

namespace MetricKMedian.FixedBatch
open Finset PhysicalPotential SourceBalance
variable {I : Type*} [Fintype I] [DecidableEq I]

theorem graph_mass_sum (G : I → Finset I) {Δ : ℕ} {g : ℝ}
    (hG : ∀ i, (G i).card=Δ) (hunit : g*(Δ:ℝ)=1) :
    (∑ h, mass g ((graphActions G).erase h))=(Fintype.card I:ℝ) := by
  have hc : ∀ h, mass g ((graphActions G).erase h)=∑ i, if h ∈ G i then g else 0 := by
    intro h
    rw [← sum_filter]
    simp only [mass, graphActions, sum_const, nsmul_eq_mul]
    exact mul_comm _ _
  simp_rw [hc]
  rw [sum_comm]
  have hi : ∀ i, (∑ h, if h ∈ G i then g else 0)=(1:ℝ) := by
    intro i
    rw [← sum_filter]
    simp only [filter_mem_eq_inter, univ_inter, sum_const, nsmul_eq_mul,hG]
    linarith only [hunit]
  simp_rw [hi]
  simp

 theorem masked_mass_sum (G : I → Finset I) (H : Finset I) (Δ : ℕ) {g : ℝ}
    (hg : 0 < g) (hunit : g*(Δ:ℝ)=1)
    (hH : ∀ h ∈ H, 1 < mass g ((graphActions G).erase h)) :
    (∑ e, mass g (countErase (heavyActions (graphActions G) H) Δ e))=
      ∑ h ∈ nonzero (fun h => mass g ((graphActions G).erase h)), mass g ((graphActions G).erase h) := by
  rw [← sum_fiberwise univ (heavyParent (graphActions G) H)]
  simp_rw [masked_mass_fiber G H Δ hg hunit hH]
  rw [nonzero, sum_filter]
  apply sum_congr rfl
  intro h _
  split_ifs <;> simp_all

 theorem masked_opening_sum_le (G : I → Finset I) (H : Finset I) (Δ : ℕ) {g : ℝ}
    (hg : 0 < g) (hunit : g*(Δ:ℝ)=1) :
    (∑ e, countOpening (heavyActions (graphActions G) H) Δ e) ≤
      ((nonzero (fun h => mass g ((graphActions G).erase h))).card:ℝ) := by
  rw [← sum_fiberwise univ (heavyParent (graphActions G) H)]
  simp_rw [masked_opening_fiber G H Δ hg hunit]
  rw [nonzero, ← sum_boole]
  apply sum_le_sum
  intro h _
  split_ifs <;> norm_num at *
  tauto

 theorem masked_total_bound (G : I → Finset I) (H : Finset I) {Δ : ℕ} {g : ℝ}
    (hg : 0 < g) (hunit : g*(Δ:ℝ)=1) (hG : ∀ i, (G i).card=Δ)
    (hH : ∀ h ∈ H, 1 < mass g ((graphActions G).erase h)) :
    (∑ e, (countOpening (heavyActions (graphActions G) H) Δ e+
      mass g (countErase (heavyActions (graphActions G) H) Δ e))) ≤
        4*amount (fun h => mass g ((graphActions G).erase h))/g := by
  let m := fun h => mass g ((graphActions G).erase h)
  have hm := graph_mass_sum G hG hunit
  have hn := nonzero_card m hm (fun h hh => grid_imbalance Δ _ hg hunit hh)
  have hs := masked_mass_sum G H Δ hg hunit hH
  rw [nonzero_mass m hm] at hs
  have ha := masked_opening_sum_le G H Δ hg hunit
  rw [sum_add_distrib, hs]
  apply (le_div_iff₀ hg).mpr
  have ha' := mul_le_mul_of_nonneg_right ha hg.le
  dsimp only [m] at hn hs
  nlinarith only [ha',hn]

 theorem masked_biased_linear_bound (G : I → Finset I) (H : Finset I) {Δ : ℕ} {g p φ : ℝ}
    (hg : 0 < g) (hunit : g*(Δ:ℝ)=1) (hG : ∀ i, (G i).card=Δ)
    (hp : 0 ≤ p) (hφ : 0 ≤ φ)
    (hH : ∀ h ∈ H, 1 < mass g ((graphActions G).erase h)) :
    (∑ e, (countOpening (heavyActions (graphActions G) H) Δ e-
      mass g (countErase (heavyActions (graphActions G) H) Δ e))*
        bias (fun h => mass g ((graphActions G).erase h)) p φ (heavyParent (graphActions G) H e)) ≤
    -p*φ*amount (fun h => mass g ((graphActions G).erase h)) := by
  let m := fun h => mass g ((graphActions G).erase h)
  rw [← sum_biased_imbalance m p φ (graph_mass_sum G hG hunit),
    ← sum_fiberwise univ (heavyParent (graphActions G) H)]
  apply sum_le_sum
  intro h _
  have heq : (∑ e ∈ univ.filter (fun e => heavyParent (graphActions G) H e=h),
      (countOpening (heavyActions (graphActions G) H) Δ e-
      mass g (countErase (heavyActions (graphActions G) H) Δ e))*
        bias m p φ (heavyParent (graphActions G) H e)) =
      ((if h ∉ H ∧ m h ≠ 1 then 1 else 0)-(if m h=1 then 0 else m h))*bias m p φ h := by
    calc
      _ = (∑ e ∈ univ.filter (fun e => heavyParent (graphActions G) H e=h),
          (countOpening (heavyActions (graphActions G) H) Δ e-
            mass g (countErase (heavyActions (graphActions G) H) Δ e)))*bias m p φ h := by
        rw [sum_mul]
        apply sum_congr rfl
        intro e he
        rw [(mem_filter.mp he).2]
      _ = _ := by rw [sum_sub_distrib, masked_opening_fiber G H Δ hg hunit,
        masked_mass_fiber G H Δ hg hunit hH]
  rw [heq]
  have hb : 0 ≤ bias m p φ h := hp.trans (bias_lower m hp hφ h)
  apply mul_le_mul_of_nonneg_right _ hb
  by_cases hm : m h=1
  · simp only [hm,ne_eq,not_true_eq_false,and_false,ite_false,ite_true,sub_self]
    norm_num
  · rw [ite_eq_right hm]
    by_cases hh : h ∈ H
    · rw [ite_eq_right (fun he => he.1 hh)]; linarith
    · rw [ite_eq_left ⟨hh,hm⟩]

end MetricKMedian.FixedBatch
end
end

end OAI
