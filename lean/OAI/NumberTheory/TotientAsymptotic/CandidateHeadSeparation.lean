import OAI.NumberTheory.TotientAsymptotic.TailProductBounds
import OAI.NumberTheory.TotientAsymptotic.HeadPrimeCount

namespace OAI

/-! The prime extension is larger than every prime in the capped tail. -/
noncomputable section
open scoped Topology
open Filter
namespace TotientAsymptotic

lemma capped_prime_le_sqrt : ∀ᶠ x : ℝ in atTop,∀ p : ℕ,p.Prime →
    Real.log (Real.log (p:ℝ)) ≤ (19/25:ℝ)*B x → (p:ℝ) ≤ x^(1/2:ℝ) := by
  filter_upwards [B_tendsto.eventually (eventually_ge_atTop ((25/6:ℝ)*Real.log 2)),
    eventually_gt_atTop (1:ℝ)] with x hB hx
  intro p hp hcap
  have hx0 : 0 < x := zero_lt_one.trans hx
  have hp0 : (0:ℝ) < p := by exact_mod_cast hp.pos
  have hp1 : (1:ℝ) < p := by exact_mod_cast hp.one_lt
  have hsmall : Real.exp (-(6/25:ℝ)*B x) ≤ 1/2 := by
    have he := Real.exp_le_exp.mpr (show -(6/25:ℝ)*B x ≤ -Real.log 2 by linarith only [hB])
    simpa only [Real.exp_neg,Real.exp_log (by norm_num : (0:ℝ)<2),one_div] using he
  have hfactor : Real.exp ((19/25:ℝ)*B x)=
      Real.exp (B x)*Real.exp (-(6/25:ℝ)*B x) := by
    rw [←Real.exp_add]
    congr 1
    ring
  have hbexp : Real.exp (B x)=Real.log x := Real.exp_log (Real.log_pos hx)
  have hlog : Real.log (p:ℝ) ≤ (1/2:ℝ)*Real.log x := by
    have he := Real.exp_le_exp.mpr hcap
    rw [Real.exp_log (Real.log_pos hp1),hfactor,hbexp] at he
    have hh := mul_le_mul_of_nonneg_left hsmall (Real.log_pos hx).le
    nlinarith only [he,hh]
  have he := Real.exp_le_exp.mpr hlog
  rw [Real.exp_log hp0] at he
  rw [Real.rpow_def_of_pos hx0]
  simpa only [mul_comm] using he

lemma head_interval_above_tail : ∀ᶠ x : ℝ in atTop,
    ∀ D : ℝ,1 ≤ D → Real.log D ≤ (Real.log x)^(4/5:ℝ) →
      ∀ n : ℕ,∀ p : Fin n → ℕ,(∀ i,(p i).Prime) →
        (∀ i,primePrefixCoord p i ≤ (19/25:ℝ)*B x) →
        ∀ q ∈ primeInterval (x/(2*D)) (x/D),q.Prime ∧ ∀ i,p i < q := by
  filter_upwards [capped_prime_le_sqrt,
    small_denominator_window (a:=1/2) (δ:=1/4) (by norm_num) (by norm_num) (by norm_num),
    eventually_gt_atTop (1:ℝ)] with x hcap hwindow hx
  intro D hD hlog n p hp hcoords q hq
  have hx0 : 0 < x := zero_lt_one.trans hx
  have hD0 : 0 < D := zero_lt_one.trans_le hD
  obtain ⟨hqprime,hql,_⟩ := mem_head_prime_interval hx0.le hD0 hq
  refine ⟨hqprime,?_⟩
  have hsize := hwindow D ((1/2:ℝ)*x) hD hlog le_rfl (by linarith only [hx0])
  have hroot : x^(1/2:ℝ) ≤ x/(2*D) := by
    convert hsize.1 using 1
    ring
  intro i
  exact_mod_cast (hcap (p i) (hp i) (hcoords i)).trans_lt (hroot.trans_lt hql)

end TotientAsymptotic

end

end OAI
