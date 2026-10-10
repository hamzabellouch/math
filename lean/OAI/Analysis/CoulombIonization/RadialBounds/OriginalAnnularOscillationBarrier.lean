import Mathlib
import OAI.Analysis.CoulombIonization.Ionization.SpatialCapActualBarrier
import OAI.Analysis.CoulombIonization.FieldAnalysis.OriginalFieldOscillationBarrier

namespace OAI

noncomputable section

namespace CoulombAtom

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory Filter Set Metric
open scoped Topology

open CoulombAnalysis CoulombObservation CoulombBarrier

lemma inner_cap_ball_subset {u : ℝ} (hu : 0 < u) {y : Space}
    (hyl : 11*u/8 ≤ ‖y‖) (hyh : ‖y‖ ≤ 13*u/8) :
    closedBall y (u/16) ⊆ closedAnnularShell (5*u/4) (7*u/4) := by
  intro t ht
  have hd : ‖t-y‖ ≤ u/16 := by simpa only [mem_closedBall,dist_eq_norm] using ht
  have hupper := norm_sub_le t y
  have hlow : ‖y‖ ≤ ‖t-y‖+‖t‖ := by
    simpa only [norm_sub_rev] using norm_le_norm_sub_add y t
  have hhigh : ‖t‖ ≤ ‖t-y‖+‖y‖ := norm_le_norm_sub_add t y
  constructor <;> linarith

theorem exists_original_annular_oscillation_constant :
    ∃ C : ℝ, 0 < C ∧ ∀ {N K : ℕ} (F : fermionGraph N)
      (Z lam r : ℝ) (j : ℕ) {c₁ r₀ s : ℝ},
      0 < c₁ → 0 < r₀ → 0 < s → r₀ ≤ s →
      ∀ (z : Configuration N × (Fin K × (Fin N × Fin 3) → ℝ))
        (u B M : ℝ), 0 < u → 0 ≤ B → 0 ≤ M →
      (∀ t : Space, u ≤ ‖t‖ → ‖t‖ ≤ 2*u →
        originalQueryDensity F r j c₁ r₀ s z t ≤ M) →
      (∀ t : Space, 5*u/4 ≤ ‖t‖ → ‖t‖ ≤ 7*u/4 →
        originalQueryField F Z lam r j c₁ r₀ s z t ≤ B) →
      ∀ y x : Space, 11*u/8 ≤ ‖y‖ → ‖y‖ ≤ 13*u/8 → ‖x-y‖ ≤ u/96 →
        |‖x‖^4*originalQueryField F Z lam r j c₁ r₀ s z x-
          ‖y‖^4*originalQueryField F Z lam r j c₁ r₀ s z y| ≤
        C/u*‖x-y‖*(u^4*B+u^6*M+
          max (-(‖y‖^4*originalQueryField F Z lam r j c₁ r₀ s z y)) 0) := by
  obtain ⟨C,hC,hbound⟩ := exists_original_field_oscillation_constant
  refine ⟨256*C+32,by positivity,?_⟩
  intro N K F Z lam r j c₁ r₀ s hc hr₀ hs hrs z u B M hu hB hM hden hcap y x hyl hyh hx
  have hball := inner_cap_ball_subset hu hyl hyh
  have hyl' : u ≤ ‖y‖ := by linarith
  have hyh' : ‖y‖ ≤ 2*u := by linarith
  have hxh : ‖x‖ ≤ 2*u := by
    have ht := norm_le_norm_sub_add x y
    linarith
  have hf := hbound F Z lam r j hc hr₀ hs hrs z y (u/16) B M (by positivity)
    (by linarith) hB hM (fun t ht => ?_) (fun t ht => ?_) x (by linarith)
  · have hφ : originalQueryField F Z lam r j c₁ r₀ s z y ≤ B := hcap y (by linarith) (by linarith)
    have hosc : |originalQueryField F Z lam r j c₁ r₀ s z x-
        originalQueryField F Z lam r j c₁ r₀ s z y| ≤
        (16*C)/u*‖x-y‖*(B+M*u^2+max (-originalQueryField F Z lam r j c₁ r₀ s z y) 0) := by
      apply hf.trans
      have hsq : M*(u/16)^2 ≤ M*u^2 :=
        mul_le_mul_of_nonneg_left (by nlinarith [sq_nonneg u]) hM
      calc
        _ = (16*C)/u*‖x-y‖*(B+M*(u/16)^2+max (-originalQueryField F Z lam r j c₁ r₀ s z y) 0) := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    have hh := normalized_field_difference hu (by positivity : 0 ≤ 16*C) hB hM hxh hyl' hyh' hφ hosc
    convert hh using 1; ring
  · have ht' := hball (ball_subset_closedBall ht)
    exact hden t (by linarith [ht'.1]) (by linarith [ht'.2])
  · have ht' := hball ht
    exact hcap t ht'.1 ht'.2

open MeasureTheory Filter Set Metric
open scoped Topology

open CoulombAnalysis CoulombObservation CoulombBarrier

lemma original_capStatistic_unscaled {N K : ℕ} (F : fermionGraph N)
    (Z lam r : ℝ) (j : ℕ) {c₁ r₀ s : ℝ} (hc : 0 < c₁) (hr₀ : 0 < r₀)
    (hs : 0 < s) (hrs : r₀ ≤ s) (z : Configuration N × (Fin K × (Fin N × Fin 3) → ℝ))
    {u C : ℝ} (hu : 0 < u) (hC : 0 ≤ C)
    (hstat : capBandStatistic u C (originalQueryField F Z lam r j c₁ r₀ s z) ≤ 1) :
    ∀ y, 5*u/4 ≤ ‖y‖ → ‖y‖ ≤ 7*u/4 →
      originalQueryField F Z lam r j c₁ r₀ s z y ≤ 16*(C+1)/(u/100000)^4 := by
  intro y hyl hyh
  have hh := original_capBandStatistic_controls_field F Z lam r j hc hr₀ hs hrs z
    hu hC hstat y hyl hyh
  by_cases hf : originalQueryField F Z lam r j c₁ r₀ s z y ≤ 0
  · exact hf.trans (by positivity)
  · have hr : u/100000 ≤ localCellRadius y := by dsimp only [localCellRadius]; linarith
    have hp := mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by positivity) hr 4) (le_of_not_ge hf)
    apply (le_div_iff₀ (by positivity : 0 < (u/100000)^4)).mpr
    simpa only [mul_comm] using hp.trans hh

lemma normalized_density_power {u D w : ℝ} (hu : 0 < u) :
    u^6*(D*u^(-6-3*w)) = D*u^(-3*w) := by
  rw [mul_left_comm]
  congr 1
  rw [← Real.rpow_natCast u 6, ← Real.rpow_add hu]
  congr 1
  ring

theorem exists_original_scaled_oscillation_constant :
    ∃ A : ℝ, 0 < A ∧ ∀ {N K : ℕ} (F : fermionGraph N)
      (Z lam r : ℝ) (j : ℕ) {c₁ r₀ s : ℝ},
      0 < c₁ → 0 < r₀ → 0 < s → r₀ ≤ s →
      ∀ (z : Configuration N × (Fin K × (Fin N × Fin 3) → ℝ))
        (u C D : ℝ), 0 < u → 0 ≤ C → 0 ≤ D →
      capBandStatistic u C (originalQueryField F Z lam r j c₁ r₀ s z) ≤ 1 →
      (∀ t : Space, u ≤ ‖t‖ → ‖t‖ ≤ 2*u →
        originalQueryDensity F r j c₁ r₀ s z t ≤ D*u^(-6-3*masterExponent)) →
      ∀ y x : Space, 11*u/8 ≤ ‖y‖ → ‖y‖ ≤ 13*u/8 → ‖x-y‖ ≤ u/96 →
        |‖x‖^4*originalQueryField F Z lam r j c₁ r₀ s z x-
          ‖y‖^4*originalQueryField F Z lam r j c₁ r₀ s z y| ≤
        A/u*‖x-y‖*(16*(C+1)*100000^4+D*u^(-3*masterExponent)+
          max (-(‖y‖^4*originalQueryField F Z lam r j c₁ r₀ s z y)) 0) := by
  obtain ⟨A,hA,hbound⟩ := exists_original_annular_oscillation_constant
  refine ⟨A,hA,?_⟩
  intro N K F Z lam r j c₁ r₀ s hc hr₀ hs hrs z u C D hu hC hD hstat hden y x hyl hyh hxy
  have hh := hbound F Z lam r j hc hr₀ hs hrs z u (16*(C+1)/(u/100000)^4)
    (D*u^(-6-3*masterExponent)) hu (by positivity) (by positivity) hden
    (original_capStatistic_unscaled F Z lam r j hc hr₀ hs hrs z hu hC hstat) y x hyl hyh hxy
  have hp : u^4*(16*(C+1)/(u/100000)^4) = 16*(C+1)*100000^4 := by
    field_simp
  simpa only [hp,normalized_density_power hu] using hh

end CoulombAtom

end

end OAI
