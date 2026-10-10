import OAI.NumberTheory.DukePrimeDegree.Entropy.RootInformationGrowth
import Mathlib.Dynamics.BirkhoffSum.QuasiMeasurePreserving

namespace OAI

/-!
# The actual root information coefficient lies in the unit interval

Truncation, finite Hopf bounds and monotone convergence turn the almost
sure linear small-ball bound into a finite mean bound. No entropy formula
or ergodic theorem is assumed.
-/

noncomputable section
open MeasureTheory Filter Set
open scoped Topology ENNReal

namespace DukePrimeDegree
open PrimeDegreePackets

variable (d : ℕ) {i j : Fin (d + 1)} (hij : i ≠ j)
  (μ : Measure (X (d + 1))) [IsProbabilityMeasure μ]
  (hA : ∀ u : LogCoordinates d, μ.map (fun x => rightAction x (diagonalFlow u)) = μ)

include hA

/-- The coefficient defined by the actual root leaf information is finite
and at most one. -/
theorem rootInformationMean_le_one : rootInformationMean hij μ 1 ≤ 1 := by
  let T : X (d + 1) → X (d + 1) := fun x => rightAction x (rootCanonicalFlow d j 1)
  have hT : MeasurePreserving T μ μ := rootCanonicalFlow_preserving d j 1 μ hA
  have hmeas := aemeasurable_rootInformation d hij μ hA 1
  let f : X (d + 1) → ℝ := fun x => max (hmeas.mk (rootInformation hij μ 1) x) 0
  have hfm : Measurable f := hmeas.measurable_mk.max measurable_const
  have hfnonneg (x) : 0 ≤ f x := le_max_right _ _
  have hfeq : f =ᵐ[μ] rootInformation hij μ 1 := by
    filter_upwards [hmeas.ae_eq_mk, ae_rootInformation_nonneg d hij μ hA zero_le_one] with x hx hn
    exact (congrArg (max · 0) hx).symm.trans (max_eq_left hn)
  let g (M : ℕ) (x : X (d + 1)) : ℝ := min (f x) M
  have hgm (M : ℕ) : Measurable (g M) := hfm.min measurable_const
  have hg0 (M : ℕ) (x) : 0 ≤ g M x := le_min (hfnonneg x) (Nat.cast_nonneg M)
  have hgint (M : ℕ) : Integrable (g M) μ :=
    integrable_of_le_of_le (hgm M).aestronglyMeasurable
      (Eventually.of_forall (hg0 M)) (Eventually.of_forall fun x => min_le_right (f x) (M : ℝ))
      (integrable_const 0) (integrable_const (M : ℝ))
  have hsum : ∀ᵐ x ∂μ, ∀ n : ℕ, birkhoffSum T f n x = rootInformation hij μ n x := by
    apply ae_all_iff.mpr
    intro n
    filter_upwards [hT.quasiMeasurePreserving.birkhoffSum_ae_eq_of_ae_eq hfeq n,
      ae_rootInformation_nat_sum d hij μ hA n] with x he hs
    exact he.trans hs.symm
  have hgmean (M : ℕ) : (∫ x, g M x ∂μ) ≤ 1 := by
    have hbound (c : ℝ) (hc : 1 < c) : (∫ x, g M x ∂μ) ≤ c := by
      apply integral_le_of_ae_birkhoffSum_lt hT (hgint M) (hgm M) c
      filter_upwards [hsum, ae_rootInformation_linear_bound d hij μ hA] with x hx hb
      obtain ⟨B, N, hN⟩ := hb
      obtain ⟨n, hn⟩ := exists_nat_gt (max (N : ℝ) (B / (c - 1)))
      have hnN : N ≤ n := by exact_mod_cast (le_max_left (N : ℝ) _).trans hn.le
      have hBn : B < (n : ℝ) * (c - 1) :=
        (div_lt_iff₀ (by linarith : 0 < c - 1)).mp ((le_max_right _ _).trans_lt hn)
      refine ⟨n, ?_⟩
      have hle : birkhoffSum T (g M) n x ≤ birkhoffSum T f n x := by
        apply Finset.sum_le_sum
        intro k _
        exact min_le_left _ _
      rw [hx n] at hle
      have hfin := (hle.trans (hN n hnN))
      nlinarith
    by_contra! h
    have hh := hbound (((∫ x, g M x ∂μ) + 1) / 2) (by linarith)
    linarith
  have hlin (M : ℕ) : (∫⁻ x, ENNReal.ofReal (g M x) ∂μ) ≤ 1 := by
    rw [← ofReal_integral_eq_lintegral_ofReal (hgint M) (Eventually.of_forall (hg0 M))]
    exact ENNReal.ofReal_le_one.mpr (hgmean M)
  have hlim : Tendsto (fun M : ℕ => ∫⁻ x, ENNReal.ofReal (g M x) ∂μ)
      atTop (𝓝 (∫⁻ x, ENNReal.ofReal (f x) ∂μ)) := by
    apply lintegral_tendsto_of_tendsto_of_monotone (fun M => (hgm M).ennreal_ofReal.aemeasurable)
    · exact Eventually.of_forall fun x a b hab => ENNReal.ofReal_le_ofReal
        (min_le_min_left (f x) (Nat.cast_le.mpr hab))
    · apply Eventually.of_forall
      intro x
      have heq : ∀ᶠ M : ℕ in atTop, g M x = f x := by
        obtain ⟨N, hN⟩ := exists_nat_gt (f x)
        filter_upwards [eventually_ge_atTop N] with M hM
        exact min_eq_left (hN.le.trans (Nat.cast_le.mpr hM))
      exact tendsto_const_nhds.congr' (heq.mono fun M hM => congrArg ENNReal.ofReal hM.symm)
  have hbound := le_of_tendsto hlim (Eventually.of_forall hlin)
  have he : (∫⁻ x, ENNReal.ofReal (f x) ∂μ) = rootInformationMean hij μ 1 :=
    lintegral_congr_ae (hfeq.mono fun x hx => congrArg ENNReal.ofReal hx)
  rwa [he] at hbound

end DukePrimeDegree

end

end OAI
