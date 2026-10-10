import OAI.MeasureTheory.Falconer.Recursion.UniformProfileContact
import OAI.MeasureTheory.Falconer.Estimates.RegularizationProperties
import OAI.MeasureTheory.Falconer.Recursion.UniformFrostmanProfiles

namespace OAI

/-! # Uniform contact intervals for every retained regularized Frostman class -/

namespace Falconer.Regularization
open Set MeasureTheory Filter
open scoped Topology NNReal ENNReal
variable {d : ℕ}

theorem source_classes_uniform_contact (hd : 0 < d) (Q : DyadicCube d) (hQ : 0 < Q.side)
    {s q t τ C : ℝ}
    (hs : 0 ≤ s) (hqt : q < t) (hts : t < s) (hτ : 0 < τ) (hC : 0 ≤ C) :
    ∃ lam γ : ℝ, 0 < lam ∧ 0 < γ ∧ lam ≤ τ*γ ∧ ∃ H N₀ : ℕ, 0 < H ∧
      (∀ N ≥ N₀, 0 < N ∧ 0 < N/H ∧ N/(N/H)+1 ≤ 2*H ∧
        ((N/H:ℕ):ℝ) ≤ lam*(N:ℝ) ∧ (2:ℝ)^(N/(N/H)+2) ≤ ((2:ℝ)^N)^lam) ∧
      ∀ N ≥ N₀, ∀ (μ : Measure (Space d)) [IsProbabilityMeasure μ],
        (∀ x : Space d, ∀ r > 0, μ (Metric.ball x r) ≤ ENNReal.ofReal (C*r^s)) →
      ∀ p ∈ regularizationLeaves Q μ N,
        regularizationLabel Q μ N (N/H) p ∈ regularizationIndex Q μ N (N/H)
          (ENNReal.ofReal (((2:ℝ)^N)^(-lam))) →
        RobustProfileContact (sourceUnitProfile Q μ N (N/H) p) q t τ γ := by
  obtain ⟨ε,γ,hε,hγ,hcontact⟩ := uniform_profile_contact (d:ℝ≥0) hqt hts hτ
  let lam : ℝ := min (ε/(2*((d:ℝ)+3))) (τ*γ)
  have hlam : 0 < lam := by dsimp [lam]; positivity
  have hsmalllam : ((d:ℝ)+3)*lam ≤ ε/2 := by
    calc
      _ ≤ ((d:ℝ)+3)*(ε/(2*((d:ℝ)+3))) :=
        mul_le_mul_of_nonneg_left (min_le_left _ _) (by positivity)
      _ = _ := by field_simp
  obtain ⟨H,N₁,hH,hcontrol,henvelope⟩ := uniform_frostman_profile_envelope hd Q hQ hC hlam
  have hsmall : ∀ᶠ N : ℕ in atTop, s/(N:ℝ) < ε/2 :=
    (tendsto_const_div_atTop_nhds_zero_nat s).eventually (eventually_lt_nhds (by linarith : (0:ℝ) < ε/2))
  obtain ⟨N₂,hN₂⟩ := eventually_atTop.mp hsmall
  refine ⟨lam,γ,hlam,hγ,min_le_right _ _,H,max N₁ (max N₂ H),hH,
    fun N hN => hcontrol N ((le_max_left _ _).trans hN),?_⟩
  intro N hN μ _ hball p hp hret
  have hHN : H ≤ N := (le_max_right _ _).trans ((le_max_right _ _).trans hN)
  have hNp : 0 < N := hH.trans_le hHN
  have hBN : 0 < N/H := Nat.div_pos hHN hH
  have hprop := sourceUnitProfile_properties Q μ hNp hBN p
  apply hcontact _ hprop.2.2.2.1 hprop.2.1
  intro u hu
  have hgrid := henvelope N ((le_max_left _ _).trans hN) μ hball p hp hret
  have hlow := sourceUnitProfile_lower_from_grid Q μ hNp hBN p hs hgrid hu
  have hsn := hN₂ N ((le_max_left _ _).trans ((le_max_right _ _).trans hN))
  linarith

end Falconer.Regularization

end OAI
