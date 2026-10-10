import OAI.MeasureTheory.Falconer.Shells.HighShellParentEnergy
import OAI.MeasureTheory.Falconer.Shells.HighShellProfileMass
import OAI.MeasureTheory.Falconer.Shells.HighShellMeasurable
import OAI.MeasureTheory.Falconer.Shells.HighShellErrorPower
import OAI.MeasureTheory.Falconer.Shells.ShellApproximationError

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory Filter
namespace PositiveDistanceData

theorem uniform_high_shell_parent_bound {sig lam eps T : ℝ}
    (hsig : 0 < sig) (heps : 0 < eps) :
    ∃ n N₀ : ℕ, ∀ d : PositiveDistanceData, ∀ (B : ℕ) (δ : ℝ),
    RegularizedProfileData d.Q d.ρ d.N B δ d.lam d.mass →
    N₀ ≤ d.N → d.sig = sig → d.lam = lam →
    0 < d.Q.side → d.StronglySeparated → 0 < d.q →
    d.sig*d.N ≤ (d.q:ℝ) → d.a+100*d.q < d.t → d.t ≤ d.N →
    d.X.length = d.a → d.Y.length = d.a →
    ∀ v : ℝ, (d.t:ℝ)-d.sig*d.N ≤ v → v ≤ d.t →
    ∀ Ψ : ℝ → ℝ, Measurable Ψ → (∀ x, 0 ≤ Ψ x) →
    (∀ x, Ψ x ≠ 0 → x ∈ Ioo (1/4:ℝ) 4) →
    ∀ W : ℝ, 0 ≤ W → (∀ x, Ψ x ≤ W) →
    (∀ x ∈ Icc (1/2:ℝ) 2, 1 ≤ Ψ x) →
    ∀ H : ℝ, 0 ≤ H →
    (∀ j ∈ Finset.range (n+1),
      ∀ b ∈ inverseLeibnizTerms j (pairMaskIndices d.inverseDescriptorList), ∀ ξ,
        (d.inversePhasedHF v Ψ b.2 ξ).toReal ≤ H) →
    (2:ℝ)^(-(d.a:ℝ)) *
      (∫ r in Icc ((2:ℝ)^(v-1)) ((2:ℝ)^(v+1)), ‖charFun d.weightedDistance r‖^2) ≤
        ((2:ℝ)^d.N)^eps*H+((2:ℝ)^d.N)^(-T) := by
  obtain ⟨n,N₁,h₁⟩ := uniform_high_shell_profile_error (lam := lam) (T := (T+3)/2) hsig
  obtain ⟨N₂,h₂⟩ := uniform_spatialLeibniz_sum_subpower 96 2004 (by norm_num) (by norm_num)
    (show 0 < eps/4 by linarith) n
  obtain ⟨N₃,h₃⟩ := fixed_constant_absorbed (half_pos heps) 4
  refine ⟨n,max 1 (max N₁ (max N₂ N₃)),?_⟩
  intro d B δ hd hN hsig' hlam hQ hsep hq hqs hw ht hX hY v hv hvt Ψ hΨ hpos hs W hW hΨW hone H hH0 hH
  let := hd.probability
  let := d.weightedDistance_isFinite hQ hsep
  have hN1 : N₁ ≤ d.N := (le_max_left _ _).trans ((le_max_right _ _).trans hN)
  have hN2 : N₂ ≤ d.N := (le_max_left _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans hN))
  have hN3 : N₃ ≤ d.N := (le_max_right _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans hN))
  let R : ℝ := (2:ℝ)^d.N
  let μ := volume.restrict (Icc ((2:ℝ)^(v-1)) ((2:ℝ)^(v+1)))
  let e := R^(-((T+3)/2))
  have herr : ∀ᵐ r ∂μ, ‖charFun d.weightedDistance r-d.normalizedHighShellF n v r‖ ≤ e := by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with r hr
    exact h₁ d B δ hd hN1 hsig' hlam hQ hsep hq hqs hw ht hX hY v r hv hr.1
  have hi : Integrable (fun r => ‖charFun d.weightedDistance r‖^2) μ :=
    integrable_norm_square_bounded μ _ measurable_charFun measureReal_nonneg
      (Eventually.of_forall (fun r => norm_charFun_le r))
  have hsq := (shell_square_approximation μ _ _ (d.normalizedHighShellF_measurable hQ hsep n v)
    hi (show 0 ≤ e by dsimp [e]; positivity) herr).2
  have hmain := d.normalizedHighShellF_parent_energy hQ hsep (by rw [hsig']; exact hsig.le)
    hq hqs hw hv n Ψ hΨ hpos hs hW hΨW hone hH0 hH
  let S := ∑ j ∈ Finset.range (n+1), spatialLeibnizCost 96 2004 (by norm_num) (by norm_num) j
    (fun k => d.mass k-(k:ℝ)/(d.N:ℝ)) d.N d.q d.a d.t
  have hS : S ≤ R^(eps/4) := h₂ d.N hN2 _ d.q d.a d.t hq
  have hS0 : 0 ≤ S := by
    apply Finset.sum_nonneg
    intro j hj
    apply mul_nonneg (spatialFourierCost_nonneg ..)
    apply mul_nonneg _ (by positivity)
    apply List.sum_nonneg
    intro x hx
    obtain ⟨b,hb,rfl⟩ := List.mem_map.mp hx
    positivity
  have hcost : 4*S^2 ≤ R^eps := by
    calc
      _ ≤ R^(eps/2)*(R^(eps/4))^2 :=
        mul_le_mul (h₃ d.N hN3) (pow_le_pow_left₀ hS0 hS 2) (sq_nonneg _) (by positivity)
      _ = _ := by
        rw [← Real.rpow_mul_natCast (show 0 ≤ R by dsimp [R]; positivity),
          ← Real.rpow_add (show 0 < R by dsimp [R]; positivity)]
        congr 1
        ring
  have herror := high_shell_error_power d.N d.a ((le_max_left _ _).trans hN)
    (hvt.trans (Nat.cast_le.mpr ht)) T
  calc
    _ ≤ (2:ℝ)^(-(d.a:ℝ)) * (2*(∫ r, ‖d.normalizedHighShellF n v r‖^2 ∂μ)+2*e^2*μ.real univ) :=
      mul_le_mul_of_nonneg_left hsq (by positivity)
    _ = 2*((2:ℝ)^(-(d.a:ℝ))*(∫ r, ‖d.normalizedHighShellF n v r‖^2 ∂μ))+
        (2:ℝ)^(-(d.a:ℝ))*(2*e^2*μ.real univ) := by ring
    _ ≤ 2*(2*S^2*H)+R^(-T) :=
      add_le_add (mul_le_mul_of_nonneg_left hmain (by norm_num)) herror
    _ ≤ R^eps*H+R^(-T) := by nlinarith [mul_le_mul_of_nonneg_right hcost hH0]

end PositiveDistanceData

end PlanarFalconer

end OAI
