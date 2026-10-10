import OAI.MathematicalPhysics.CriticalSK.HeatBath
import OAI.MathematicalPhysics.CriticalSK.SmallBall

namespace OAI

noncomputable section

open scoped BigOperators Topology NNReal ENNReal

namespace CriticalSK

open Set MeasureTheory Filter

lemma continuousGoodMass_le_one {n : ℕ} (W : Disorder n) (t : ℝ) : continuousGoodMass W t ≤ 1 := by
  rw [← gibbs_sum W]
  apply Finset.sum_le_sum
  intro x _
  split_ifs
  · rfl
  · exact gibbs_nonneg W x

lemma discreteGoodMass_le_one {n : ℕ} (W : Disorder n) (k : ℕ) : discreteGoodMass W k ≤ 1 := by
  rw [← gibbs_sum W]
  apply Finset.sum_le_sum
  intro x _
  split_ifs
  · rfl
  · exact gibbs_nonneg W x

lemma continuous_bad_subset {n : ℕ} (hn : 0 < n) (t : ℝ) (ht : 0 ≤ t)
    {a δ : ℝ} (ha : 0 < a) (_hδ : 0 < δ) (hinc : 2*t/a^2 < δ/8) :
    {W : Disorder n | δ ≤ |continuousGoodMass W t-1|} ⊆ smallBallObstruction n a (δ/8) := by
  intro W hW u hu
  have hb := continuous_good_mass_bound W hn t ht u a ha
  change 1-continuousGoodMass W t ≤ 4*(linearSmallBall W u a+(2*t*∑ i, (u i)^2)/a^2) at hb
  rw [← EuclideanSpace.real_norm_sq_eq,hu,one_pow,mul_one] at hb
  have he : |continuousGoodMass W t-1| = 1-continuousGoodMass W t := by
    rw [abs_of_nonpos (sub_nonpos.mpr (continuousGoodMass_le_one W t))]
    ring
  simp only [Set.mem_ofPred_eq,he] at hW
  linarith

lemma discrete_bad_subset {n : ℕ} (hn : 0 < n) (k : ℕ)
    {a δ : ℝ} (ha : 0 < a) (_hδ : 0 < δ) (hinc : ((2*k:ℝ)/n)/a^2 < δ/8) :
    {W : Disorder n | δ ≤ |discreteGoodMass W k-1|} ⊆ smallBallObstruction n a (δ/8) := by
  intro W hW u hu
  have hb := discrete_good_mass_bound W hn k u a ha
  change 1-discreteGoodMass W k ≤ 4*(linearSmallBall W u a+((2*k:ℝ)/n*∑ i, (u i)^2)/a^2) at hb
  rw [← EuclideanSpace.real_norm_sq_eq,hu,one_pow,mul_one] at hb
  have he : |discreteGoodMass W k-1| = 1-discreteGoodMass W k := by
    rw [abs_of_nonpos (sub_nonpos.mpr (discreteGoodMass_le_one W k))]
    ring
  simp only [Set.mem_ofPred_eq,he] at hW
  linarith

lemma realized_continuous_initial_states (t : ℕ → ℝ) (ht : ∀ n, 0 ≤ t n)
    (hscale : Tendsto (fun n => t n/(n:ℝ)^(2/3:ℝ)) atTop (𝓝 0))
    (δ : ℝ) (hδ : 0 < δ) :
    Tendsto (fun n => (disorderLaw n).real {W | δ ≤ |continuousGoodMass W (t n)-1|}) atTop (𝓝 0) := by
  apply (tendsto_add_atTop_iff_nat 4).mp
  apply tendsto_order.mpr
  constructor
  · intro a ha
    exact Filter.Eventually.of_forall (fun n => lt_of_lt_of_le ha measureReal_nonneg)
  · intro α hα
    obtain ⟨b,hb,hprob⟩ := natural_smallBall_tight (show 0 < δ/8 by positivity) hα
    have hinc : Tendsto (fun n : ℕ => 2*t (n+4)/(b*(n+4:ℝ)^(1/3:ℝ))^2) atTop (𝓝 0) := by
      have hh := (hscale.comp (tendsto_add_atTop_nat 4)).const_mul (2/b^2)
      convert hh using 1
      · ext n
        simp only [Function.comp_def,Nat.cast_add,Nat.cast_ofNat,mul_pow,third_power_square (by positivity : (0:ℝ) ≤ n+4)]
        simp only [div_eq_mul_inv,mul_inv_rev]
        ring
      · ring_nf
    filter_upwards [hprob,hinc.eventually (gt_mem_nhds (show 0 < δ/8 by positivity))] with n hn hi
    exact lt_of_le_of_lt (measureReal_mono (continuous_bad_subset (by omega : 0 < n+4)
      (t (n+4)) (ht _) (by positivity) hδ hi)) hn

lemma realized_discrete_initial_states (k : ℕ → ℕ)
    (hscale : Tendsto (fun n => (k n:ℝ)/(n:ℝ)^(5/3:ℝ)) atTop (𝓝 0))
    (δ : ℝ) (hδ : 0 < δ) :
    Tendsto (fun n => (disorderLaw n).real {W | δ ≤ |discreteGoodMass W (k n)-1|}) atTop (𝓝 0) := by
  apply (tendsto_add_atTop_iff_nat 4).mp
  apply tendsto_order.mpr
  constructor
  · intro a ha
    exact Filter.Eventually.of_forall (fun n => lt_of_lt_of_le ha measureReal_nonneg)
  · intro α hα
    obtain ⟨b,hb,hprob⟩ := natural_smallBall_tight (show 0 < δ/8 by positivity) hα
    have hinc : Tendsto (fun n : ℕ => ((2*k (n+4):ℝ)/(n+4:ℝ))/(b*(n+4:ℝ)^(1/3:ℝ))^2) atTop (𝓝 0) := by
      have hh := (hscale.comp (tendsto_add_atTop_nat 4)).const_mul (2/b^2)
      convert hh using 1
      · ext n
        simp only [Function.comp_def,Nat.cast_add,Nat.cast_ofNat,mul_pow,
          third_power_square (by positivity : (0:ℝ) ≤ n+4), fifth_third_power (by positivity : (0:ℝ) < n+4)]
        simp only [div_eq_mul_inv,mul_inv_rev]
        ring
      · ring_nf
    filter_upwards [hprob,hinc.eventually (gt_mem_nhds (show 0 < δ/8 by positivity))] with n hn hi
    exact lt_of_le_of_lt (measureReal_mono (discrete_bad_subset (by omega : 0 < n+4)
      (k (n+4)) (by positivity) hδ (by simpa only [Nat.cast_add,Nat.cast_ofNat] using hi))) hn

theorem realized_equilibrium_initial_states :
    (∀ t : ℕ → ℝ, (∀ n, 0 ≤ t n) →
      Tendsto (fun n => t n / (n : ℝ) ^ ((2 : ℝ) / 3)) atTop (𝓝 0) →
      ∀ δ : ℝ, 0 < δ →
        Tendsto (fun n => (disorderLaw n {W |
          δ ≤ |continuousGoodMass W (t n) - 1|}).toReal) atTop (𝓝 0)) ∧
    (∀ k : ℕ → ℕ,
      Tendsto (fun n => (k n : ℝ) / (n : ℝ) ^ ((5 : ℝ) / 3)) atTop (𝓝 0) →
      ∀ δ : ℝ, 0 < δ →
        Tendsto (fun n => (disorderLaw n {W |
          δ ≤ |discreteGoodMass W (k n) - 1|}).toReal) atTop (𝓝 0)) := by
  exact ⟨realized_continuous_initial_states,realized_discrete_initial_states⟩

end CriticalSK

end

end OAI
