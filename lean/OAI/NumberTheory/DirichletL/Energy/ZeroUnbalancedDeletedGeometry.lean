import OAI.NumberTheory.DirichletL.Energy.ZeroReferenceGeometry

namespace OAI

noncomputable section
open scoped Classical BigOperators

namespace SevenEighths.CenteredMomentEnergyZeroUnbalancedDeletedGeometry
open HeckeFamily CenteredMomentEnergyState CenteredMomentEnergyBands
open CenteredMomentEnergyReferenceDivisors CenteredMomentEnergyZeroReferenceGeometry
local notation "O" => HeckeFamily.O

theorem actual_deleted_gates {Z Bmask bΦ : ℝ} (s : NaturalState Z Bmask bΦ)
    (hZ : 1 < Z) (hB : 0 ≤ Bmask) (Mcap L X₁ X₂ xi : ℝ)
    (hwidth : s.width ≤ Mcap) (hL : Mcap + Bmask + xi ≤ L)
    (hX₁ : 0 < X₁) (hX₂ : 0 < X₂) (hxi : 0 ≤ xi) (hxiM : xi ≤ s.width / 6)
    (hshort : Real.logb Z X₁ ≤ s.width / 4) (hlong : 1 ≤ X₂)
    (D₁ D₂ : Finset (Ideal O))
    (hD₁ : D₁ ∈ (CompletedGauss.primeSupport s.puncture).powerset)
    (hD₂ : D₂ ∈ (CompletedGauss.primeSupport s.puncture).powerset) :
    let short := Real.logb Z X₁ - Real.logb Z ((∏ P ∈ D₁, P).absNorm : ℝ)
    let along := Real.logb Z X₂ - Real.logb Z ((∏ P ∈ D₂, P).absNorm : ℝ)
    Z ^ short = X₁ / ((∏ P ∈ D₁, P).absNorm : ℝ) ∧
    Z ^ along = X₂ / ((∏ P ∈ D₂, P).absNorm : ℝ) ∧
    short ≤ s.width / 4 ∧ short ≤ L ∧ -Bmask ≤ along ∧
    s.width ≤ Mcap + Bmask + along ∧ max 0 (s.width - along + xi) ≤ L ∧
    ((along ≤ L ∧ length Z (Z ^ short) + length Z (Z ^ along) ≤ 5 * s.width / 6) ∨
      (0 < along ∧ max 0 (s.width - along + xi) + length Z (Z ^ short) ≤ 5 * s.width / 6)) := by
  dsimp only
  have hZ0 : 0 < Z := zero_lt_one.trans hZ
  obtain ⟨hn₁, _⟩ := divisor_norm s D₁ hD₁
  obtain ⟨hn₂, hc₂⟩ := divisor_norm s D₂ hD₂
  have hl₁ := Real.logb_nonneg hZ hn₁
  have hlonglog := Real.logb_nonneg hZ hlong
  have hu₂ : Real.logb Z ((∏ P ∈ D₂, P).absNorm : ℝ) ≤ Bmask :=
    (Real.logb_le_iff_le_rpow hZ (zero_lt_one.trans_le hn₂)).mpr hc₂
  have hM := s.width_nonneg
  have hL0 : 0 ≤ L := by linarith
  refine ⟨divided_scale_power Z X₁ _ hZ hX₁ (zero_lt_one.trans_le hn₁),
    divided_scale_power Z X₂ _ hZ hX₂ (zero_lt_one.trans_le hn₂),
    by linarith, by linarith, by linarith, by linarith,
    max_le hL0 (by linarith), ?_⟩
  have hlen (v : ℝ) : length Z (Z ^ v) = max 0 v := by
    rcases le_total 0 v with hv | hv
    · rw [length, max_eq_right (Real.one_le_rpow hZ.le hv),
        Real.logb_rpow hZ0 hZ.ne', max_eq_right hv]
    · rw [length, max_eq_left (Real.rpow_le_one_of_one_le_of_nonpos hZ.le hv),
        Real.logb_one, max_eq_left hv]
  simp only [hlen]
  rcases low_or_reflected s.width
    (Real.logb Z X₁ - Real.logb Z ((∏ P ∈ D₁, P).absNorm : ℝ))
    (Real.logb Z X₂ - Real.logb Z ((∏ P ∈ D₂, P).absNorm : ℝ))
    xi hM (by linarith) hxi hxiM with hd | hr
  · refine Or.inl ⟨?_, hd⟩
    have hh₁ := le_max_right (0 : ℝ)
      (Real.logb Z X₂ - Real.logb Z ((∏ P ∈ D₂, P).absNorm : ℝ))
    have hh₂ := le_max_left (0 : ℝ)
      (Real.logb Z X₁ - Real.logb Z ((∏ P ∈ D₁, P).absNorm : ℝ))
    linarith
  · exact Or.inr hr

end SevenEighths.CenteredMomentEnergyZeroUnbalancedDeletedGeometry

end

end OAI
