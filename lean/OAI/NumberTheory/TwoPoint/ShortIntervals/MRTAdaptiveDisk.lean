import OAI.NumberTheory.TwoPoint.ShortIntervals.MRTCharacterZeroCount

namespace OAI

/-! A local analytic disk estimate with an explicit logarithmic growth budget.
The statement is independent of the physical radius, so it can be used on the
shrinking disks required by a Vinogradov--Korobov growth estimate. -/

namespace TwoPointCorrelations

open Complex Filter
open scoped BigOperators Classical Topology

noncomputable def mrtDiskZeros (f : ℂ → ℂ) : Set ℂ :=
  Erdos970.zerosetKfR (7 / 8) (by norm_num) f

lemma mrtDiskZeros_finite (f : ℂ → ℂ)
    (hf : ∀ z ∈ Metric.closedBall (0 : ℂ) 1, AnalyticAt ℂ f z)
    (h0 : f 0 = 1) : (mrtDiskZeros f).Finite := by
  apply Erdos970.lem_Contra_finiteKR (7 / 8) (by norm_num) (by norm_num) f hf
  exact ⟨0, by simp, by rw [h0]; exact one_ne_zero⟩

private lemma mrt_disk_factorization (f : ℂ → ℂ)
    (hf : ∀ z ∈ Metric.closedBall (0 : ℂ) 1, AnalyticAt ℂ f z)
    (h0 : f 0 = 1) :
    ∃ g : ℂ → ℂ → ℂ, ∀ ρ ∈ mrtDiskZeros f,
      AnalyticAt ℂ (g ρ) ρ ∧ g ρ ρ ≠ 0 ∧
        ∀ᶠ w in 𝓝 ρ, f w = (w - ρ) ^ (analyticOrderAt f ρ).toNat * g ρ w := by
  have hfactor : ∀ ρ : ℂ, ∃ g : ℂ → ℂ, AnalyticAt ℂ g ρ ∧ g ρ ≠ 0 ∧
      (ρ ∈ mrtDiskZeros f →
        ∀ᶠ w in 𝓝 ρ, f w = (w - ρ) ^ (analyticOrderAt f ρ).toNat * g w) := by
    intro ρ
    by_cases hρ : ρ ∈ mrtDiskZeros f
    · obtain ⟨g, hg, hgne, heq⟩ := Erdos970.lem_analytic_zero_factor
        (15 / 16) (7 / 8) (by norm_num) (by norm_num) (by norm_num) f hf
        (by rw [h0]; exact one_ne_zero) ρ hρ
      exact ⟨g, hg, hgne, fun _ => heq⟩
    · exact ⟨fun _ => 1, analyticAt_const, one_ne_zero, fun h => (hρ h).elim⟩
  exact ⟨fun ρ => Classical.choose (hfactor ρ), fun ρ hρ =>
    ⟨(Classical.choose_spec (hfactor ρ)).1,
      (Classical.choose_spec (hfactor ρ)).2.1,
      (Classical.choose_spec (hfactor ρ)).2.2 hρ⟩⟩

/-- Logarithmic derivative equals the actual finite zero sum with an error
linear in the logarithmic growth budget. -/
theorem mrt_disk_logderiv (f : ℂ → ℂ)
    (hf : ∀ z ∈ Metric.closedBall (0 : ℂ) 1, AnalyticAt ℂ f z)
    (h0 : f 0 = 1) {B : ℝ} (hB : 0 < B)
    (hbound : ∀ z ∈ Metric.closedBall (0 : ℂ) (15 / 16), ‖f z‖ ≤ Real.exp B)
    {z : ℂ} (hz : ‖z‖ ≤ 3 / 4) (hn : f z ≠ 0) :
    ‖deriv f z / f z -
      ∑ ρ ∈ (mrtDiskZeros_finite f hf h0).toFinset,
        (analyticOrderAt f ρ).toNat / (z - ρ)‖ ≤
      mrtCharacterLogDerivativeConstant * B := by
  obtain ⟨g, hg⟩ := mrt_disk_factorization f hf h0
  have hz' : z ∈ Metric.closedBall (0 : ℂ) (3 / 4 : ℝ) \
      Erdos970.zerosetKfR (7 / 8) (by norm_num) f :=
    ⟨by simpa using hz, fun h => hn h.2⟩
  have h := Erdos970.final_ineq1 (Real.exp B) (Real.one_lt_exp_iff.mpr hB)
    (3 / 4) (4 / 5) (15 / 16) (7 / 8)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    f hf h0 (mrtDiskZeros_finite f hf h0) hg hbound z hz'
  simpa only [mrtDiskZeros, Real.log_exp, mrtCharacterLogDerivativeConstant] using h

/-- The total multiplicity in the inner disk has the same logarithmic cost. -/
theorem mrt_disk_zero_count (f : ℂ → ℂ)
    (hf : ∀ z ∈ Metric.closedBall (0 : ℂ) 1, AnalyticAt ℂ f z)
    (h0 : f 0 = 1) {B : ℝ} (hB : 0 < B)
    (hbound : ∀ z ∈ Metric.closedBall (0 : ℂ) (15 / 16), ‖f z‖ ≤ Real.exp B) :
    (∑ ρ ∈ (mrtDiskZeros_finite f hf h0).toFinset,
      ((analyticOrderAt f ρ).toNat : ℝ)) ≤
      (1 / Real.log ((15 / 16 : ℝ) / (7 / 8))) * B := by
  obtain ⟨g, hg⟩ := mrt_disk_factorization f hf h0
  have h := Erdos970.lem_sum_m_rho_bound (Real.exp B) (15 / 16) (7 / 8)
    (Real.one_lt_exp_iff.mpr hB) (by norm_num) (by norm_num) (by norm_num) f hf
    (by rw [h0]; exact one_ne_zero) h0 (mrtDiskZeros_finite f hf h0) g (fun z hz => hbound z (by simpa using hz)) hg
  simpa only [mrtDiskZeros, Real.log_exp] using h

/-- A zero separation estimate completes the local norm bound. -/
theorem mrt_disk_logderiv_norm (f : ℂ → ℂ)
    (hf : ∀ z ∈ Metric.closedBall (0 : ℂ) 1, AnalyticAt ℂ f z)
    (h0 : f 0 = 1) {B : ℝ} (hB : 0 < B)
    (hbound : ∀ z ∈ Metric.closedBall (0 : ℂ) (15 / 16), ‖f z‖ ≤ Real.exp B)
    {z : ℂ} (hz : ‖z‖ ≤ 3 / 4) (hn : f z ≠ 0)
    {η : ℝ} (hη : 0 < η)
    (hd : ∀ ρ ∈ mrtDiskZeros f, η ≤ ‖z - ρ‖) :
    ‖deriv f z / f z‖ ≤
      (mrtCharacterLogDerivativeConstant +
        (1 / Real.log ((15 / 16 : ℝ) / (7 / 8))) / η) * B := by
  let S := (mrtDiskZeros_finite f hf h0).toFinset
  let m : ℂ → ℕ := fun ρ => (analyticOrderAt f ρ).toNat
  have hs : ‖∑ ρ ∈ S, (m ρ : ℂ) / (z - ρ)‖ ≤ (∑ ρ ∈ S, (m ρ : ℝ)) / η := by
    calc
      _ ≤ ∑ ρ ∈ S, ‖(m ρ : ℂ) / (z - ρ)‖ := norm_sum_le _ _
      _ ≤ ∑ ρ ∈ S, (m ρ : ℝ) / η := by
        apply Finset.sum_le_sum
        intro ρ hρ
        rw [norm_div, Complex.norm_natCast]
        exact div_le_div_of_nonneg_left (Nat.cast_nonneg _) hη
          (hd ρ ((mrtDiskZeros_finite f hf h0).mem_toFinset.mp hρ))
      _ = _ := by rw [Finset.sum_div]
  have hc := div_le_div_of_nonneg_right (mrt_disk_zero_count f hf h0 hB hbound) hη.le
  have he := mrt_disk_logderiv f hf h0 hB hbound hz hn
  have ht := norm_add_le
    (deriv f z / f z - ∑ ρ ∈ S, (m ρ : ℂ) / (z - ρ))
    (∑ ρ ∈ S, (m ρ : ℂ) / (z - ρ))
  rw [sub_add_cancel] at ht
  calc
    _ ≤ mrtCharacterLogDerivativeConstant * B +
        ((1 / Real.log ((15 / 16 : ℝ) / (7 / 8))) * B) / η :=
      ht.trans (add_le_add he (hs.trans hc))
    _ = _ := by ring

end TwoPointCorrelations

end OAI
