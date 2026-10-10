import OAI.Probability.SLE.Multipoint.MultipointCutoffExhaustion
import OAI.Probability.SLE.Multipoint.MultipointActualPhases

namespace OAI

/-! On the literal event that every target radius is reached, every
factor is eventually completed before the localization cutoff. -/

noncomputable section
open Set Filter MeasureTheory
open scoped NNReal ENNReal

namespace SLEExactGauge.Multipoint

theorem eventually_all_completed_of_finite_radius_levels
    {Ω ι : Type*} [mΩ : MeasurableSpace Ω] [Fintype ι]
    (B : ℝ≥0 → Ω → ℝ) (hm : ∀ t, Measurable (B t))
    (hBc : ∀ ω, Continuous (fun t => B t ω))
    (κ A : ℝ) (hA : 0 ≤ A) (z : ι → ℂ) (u₀ u₂ : ι → ℝ)
    (γ : Ω → ℝ≥0 → ℂ) (G F : Ω → ℝ≥0 → ℂ → ℂ)
    (hw : ∀ ω, IsCapacityTwoWitness (fun t => Real.sqrt κ*B t ω)
      (γ ω) (G ω) (F ω))
    (S : ∀ n : ℕ, LocalizedState B hm κ (-(A+n+1)) (A+n+1) (A+n+1)
      ((n : ℝ≥0)+1) z
      (fun i => actualFactorStops γ G z u₀ u₂ ((n : ℝ≥0)+1) (i,2)) γ G)
    (ω : Ω) (hfinish : ∀ i, radiusLevelTime (γ ω) (G ω) (z i) (u₂ i) < ⊤) :
    ∀ᶠ n : ℕ in atTop,
      (∀ i, actualFactorStops γ G z u₀ u₂ ((n : ℝ≥0)+1) (i,2) ω ≤ (S n).χ ω) ∧
      phaseAt (actualFactorStops γ G z u₀ u₂ ((n : ℝ≥0)+1)) ((S n).χ ω) ω =
        fun _ => 3 := by
  classical
  have hex (i : ι) : ∃ t : ℝ≥0, z i ∈ survivingDomain (γ ω) t ∧
      radiusLevelTime (γ ω) (G ω) (z i) (u₂ i) = (t : ℝ≥0∞) := by
    obtain ⟨t,ht,hR⟩ := exists_live_level_of_radiusLevelTime_lt_top
      (γ ω) (G ω) (z i) (u₂ i) (hfinish i)
    exact ⟨t,ht,radiusLevelTime_eq_of_live_level
      (continuous_const.mul (hBc ω)) (hw ω) (z i) (u₂ i) t ht hR⟩
  choose σ hσlive hσeq using hex
  let T : ℝ≥0 := (∑ i, σ i)+1
  have hσT (i : ι) : σ i ≤ T := by
    exact (Finset.single_le_sum (fun j _ => (show 0 ≤ σ j from bot_le)) (Finset.mem_univ i)).trans
      (le_add_of_nonneg_right zero_le)
  have hlarge : ∀ᶠ n : ℕ in atTop, (T : ℝ) < (n : ℝ) :=
    (tendsto_natCast_atTop_atTop : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop).eventually
      (eventually_gt_atTop (T : ℝ))
  have hτ : ∀ᶠ n : ℕ in atTop,
      ∀ i, actualFactorStops γ G z u₀ u₂ ((n : ℝ≥0)+1) (i,2) ω = σ i := by
    filter_upwards [hlarge] with n hn i
    have hbound : σ i ≤ ((n : ℝ≥0)+1)+1 := by
      have hsT : (σ i : ℝ) ≤ (T : ℝ) := by exact_mod_cast hσT i
      exact_mod_cast (show (σ i : ℝ) ≤ ((n : ℝ)+1)+1 from by linarith)
    change cutoffStop (fun ω => radiusLevelTime (γ ω) (G ω) (z i)
      (factorRadiusLevel (u₀ i) (u₂ i) 2)) (((n : ℝ≥0)+1)+1) ω = σ i
    have hfactor : factorRadiusLevel (u₀ i) (u₂ i) 2 = u₂ i := by
      norm_num [factorRadiusLevel]
    simp only [hfactor]
    change (min (radiusLevelTime (γ ω) (G ω) (z i) (u₂ i) : WithTop ℝ≥0)
      ((((n : ℝ≥0)+1)+1 : ℝ≥0) : WithTop ℝ≥0)).untopD 0 = σ i
    have he : (radiusLevelTime (γ ω) (G ω) (z i) (u₂ i) : WithTop ℝ≥0) =
        (σ i : WithTop ℝ≥0) := hσeq i
    have hemin : min (radiusLevelTime (γ ω) (G ω) (z i) (u₂ i) : WithTop ℝ≥0)
        ((((n : ℝ≥0)+1)+1 : ℝ≥0) : WithTop ℝ≥0) = (σ i : WithTop ℝ≥0) :=
      (congrArg (fun q : WithTop ℝ≥0 => min q
        ((((n : ℝ≥0)+1)+1 : ℝ≥0) : WithTop ℝ≥0)) he).trans
          (min_eq_left (WithTop.coe_le_coe.mpr hbound))
    exact congrArg (WithTop.untopD 0) hemin
  have hχ := eventually_localization_after_completed B hm hBc κ A hA z
    (fun n i => actualFactorStops γ G z u₀ u₂ ((n : ℝ≥0)+1) (i,2))
    γ G F hw S ω σ T hσT hσlive hτ
  filter_upwards [hτ,hχ] with n hτn hχn
  have hdone (i : ι) :
      actualFactorStops γ G z u₀ u₂ ((n : ℝ≥0)+1) (i,2) ω ≤ (S n).χ ω := by
    rw [hτn i]
    exact (hσT i).trans hχn.le
  exact ⟨hdone,funext (fun i => by simp only [phaseAt,ite_eq_left (hdone i)])⟩

end SLEExactGauge.Multipoint

end

end OAI
