import OAI.NumberTheory.TotientAsymptotic.WeightedPrimeSet

namespace OAI

noncomputable section
open scoped Topology
open Filter
namespace TotientAsymptotic

lemma weighted_endpoint_bounds {x D A C : ℝ} {k : ℕ}
    (hx : 0 < x) (hD : 0 < D) (hDA : D ≤ A) (hC : 1 ≤ C) (hAC : A ≤ C*D)
    (hT : 1 ≤ x/D) (hk : 1 ≤ k) :
    (1/C)*x/D ≤ (k : ℝ)*x/A ∧
    (1/C)*x/D ≤ min (1+x/D) ((k+1 : ℝ)*x/A) ∧
    min (1+x/D) ((k+1 : ℝ)*x/A) ≤ 2*x/D := by
  have hA : 0 < A := hD.trans_le hDA
  have hC0 : 0 < C := zero_lt_one.trans_le hC
  have hb : (1/C)*x/D ≤ x/A := by
    have hh := div_le_div_of_nonneg_left hx.le hA hAC
    convert hh using 1
    ring
  have hkR : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hp : (1/C)*x/D ≤ x/D := by
    have hi : 1/C ≤ (1 : ℝ) := (div_le_one hC0).mpr hC
    calc
      (1/C)*x/D = (1/C)*(x/D) := by ring
      _ ≤ 1*(x/D) := mul_le_mul_of_nonneg_right hi (div_pos hx hD).le
      _ = x/D := one_mul _
  refine ⟨hb.trans ?_,le_min (hp.trans (by linarith)) (hb.trans ?_),?_⟩
  · exact div_le_div_of_nonneg_right (by nlinarith) hA.le
  · exact div_le_div_of_nonneg_right (by nlinarith) hA.le
  · apply (min_le_left _ _).trans
    rw [show 2*x/D=2*(x/D) by ring]
    linarith

/-- Ordinary PNT at two long-scale endpoints suffices, uniformly for all
allowed integers A,D. The estimate remains additive for empty intervals. -/
theorem weighted_prime_count (hpnt : PrimeNumberTheoremInput)
    {C ε : ℝ} (hC : 1 ≤ C) (hε : 0 < ε) :
    ∀ᶠ x : ℝ in atTop, ∀ k D A : ℕ, 1 ≤ k → 0 < D → D ≤ A →
      (A : ℝ) ≤ C*D → Real.log (D : ℝ) ≤ (Real.log x)^(4/5 : ℝ) →
      |((intervalHeads x k D A).card : ℝ)-
        (x/(D*Real.log x))*fk k ((A : ℝ)/D)| ≤ ε*(x/(D*Real.log x)) := by
  have hC0 : 0 < C := zero_lt_one.trans_le hC
  filter_upwards [prime_interval_uniform hpnt (a := 1/C) (by positivity)
      (b := 2) (by norm_num) (show 0 < ε/3 by positivity),
    lower_prime_cutoff_negligible (a := 1) (by norm_num) (show 0 < ε/3 by positivity),
    small_denominator_window (a := 1) (by norm_num) (δ := 1/4) (by norm_num) le_rfl,
    eventually_gt_atTop (Real.exp 1)] with x hint hcut hwindow hx
  intro k D A hk hD hDA hAC hlogD
  have he1 : (1 : ℝ) < Real.exp 1 := Real.one_lt_exp_iff.mpr (by norm_num)
  have hx1 : 1 < x := he1.trans hx
  have hx0 : 0 < x := zero_lt_one.trans hx1
  have hL : 0 < Real.log x := Real.log_pos hx1
  have hL1 : 1 ≤ Real.log x := (Real.le_log_iff_exp_le hx0).mpr hx.le
  have hD1 : (1 : ℝ) ≤ D := by exact_mod_cast hD
  have hD0 : (0 : ℝ) < D := by exact_mod_cast hD
  have hDA' : (D : ℝ) ≤ A := by exact_mod_cast hDA
  have hA0 : (0 : ℝ) < A := hD0.trans_le hDA'
  let l : ℝ := (k : ℝ)*x/A
  let u : ℝ := min (1+x/D) ((k+1 : ℝ)*x/A)
  have hT : 1 ≤ x/D := (Real.one_le_rpow hx1.le (by norm_num : (0 : ℝ)≤1/2)).trans
    (hwindow D x hD1 hlogD (by simp) le_rfl).1
  have hb := weighted_endpoint_bounds hx0 hD0 hDA' hC hAC hT hk
  have hi := hint D l u hD1 hlogD hb.1 hb.2.1 hb.2.2
  have hc := (finite_prime_cutoff_error hx0.le (primeInterval l u))
  rw [← intervalHeads_eq_cutoff hx0.le hD (hD.trans_le hDA)] at hc
  have hc' := hcut D x hD1 hlogD (by simp)
  have hg := shifted_interval_length (div_pos hx0 hD0) (div_pos hx0 hA0).le
    (div_pos hA0 hD0) (show x/(A : ℝ)=(x/D)/((A : ℝ)/D) by field_simp) k
  have hg' : |(u-min l u)-(x/D)*fk k ((A : ℝ)/D)| ≤ 1 := by
    simpa only [l,u,add_comm,mul_div_assoc] using hg
  have he : |(u-min l u)/Real.log x-(x/(D*Real.log x))*fk k ((A : ℝ)/D)| ≤ 1/Real.log x := by
    rw [show (u-min l u)/Real.log x-(x/(D*Real.log x))*fk k ((A : ℝ)/D)=
      ((u-min l u)-(x/D)*fk k ((A : ℝ)/D))/Real.log x by ring,abs_div,abs_of_pos hL]
    exact div_le_div_of_nonneg_right hg' hL.le
  have hsmall : 1/Real.log x ≤ (ε/3)*(x/(D*Real.log x)) := by
    exact ((div_le_one hL).mpr hL1).trans ((by linarith [Real.rpow_nonneg hx0.le (9/10 : ℝ)] : (1 : ℝ) ≤ x^(9/10 : ℝ)+1).trans hc')
  calc
    _ ≤ |((intervalHeads x k D A).card : ℝ)-(primeInterval l u).card|+
        |((primeInterval l u).card : ℝ)-(x/(D*Real.log x))*fk k ((A : ℝ)/D)| := abs_sub_le _ _ _
    _ ≤ (ε/3)*(x/(D*Real.log x))+
        (|(primeInterval l u).card-(u-min l u)/Real.log x|+
          |(u-min l u)/Real.log x-(x/(D*Real.log x))*fk k ((A : ℝ)/D)|) :=
      add_le_add (hc.trans hc') (abs_sub_le _ _ _)
    _ ≤ (ε/3)*(x/(D*Real.log x))+
        ((ε/3)*(x/(D*Real.log x))+(ε/3)*(x/(D*Real.log x))) := by
      apply add_le_add_right
      apply add_le_add _ (he.trans hsmall)
      convert hi using 1
      ring
    _ = ε*(x/(D*Real.log x)) := by ring

end TotientAsymptotic

end

end OAI
