import OAI.Geometry.RCD.Sobolev.ContainingMassCutoffErrors

namespace OAI

/-! # L2 errors in a coefficient supported in the interior

The two weak gradients need bounds only on the support of the coefficient.
The original outer-ball normalization is retained.
-/

open Set Filter MeasureTheory
open scoped Topology
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]

theorem supported_coefficient_l2_gamma_error (μ : Measure X) (hQ : QuadraticCheegerEnergy μ)
    (Ω U : ℕ → Set X) [∀ k, IsFiniteMeasure (μ.restrict (U k))]
    (hU : ∀ k, MeasurableSet (U k)) (hsub : ∀ k, Ω k⊆U k) (hmass : ∀ k, 0<μ.real (U k))
    (r : ℕ → ℝ) (hr : ∀ k, 0≤r k)
    (f g : ℕ → SobolevSpace μ hQ) (z : ℕ → X → ℝ)
    {M L : ℝ} (hM : 0≤M) (hL : 0≤L)
    (hf : ∀ᶠ k in atTop, ∀ᵐ x ∂μ.restrict (Ω k), r k^2*localGamma μ hQ (f k) (f k) x≤M^2)
    (hg : ∀ᶠ k in atTop, ∀ᵐ x ∂μ.restrict (Ω k), r k^2*localGamma μ hQ (g k) (g k) x≤L^2)
    (hz_zero : ∀ᶠ k in atTop, ∀ᵐ x ∂μ.restrict (U k), x∉Ω k → z k x=0)
    (hz : ∀ k, MemLp (z k) 2 (μ.restrict (U k)))
    (hlim : Tendsto (fun k => (μ.real (U k))⁻¹*∫ x in U k, (z k x)^2 ∂μ) atTop (𝓝 0)) :
    Tendsto (fun k => r k^2*(μ.real (U k))⁻¹*
      ∫ x in U k, z k x*localGamma μ hQ (f k) (g k) x ∂μ) atTop (𝓝 0) := by
  let : ∀ k, IsFiniteMeasure (μ.restrict (Ω k)) := fun k =>
    ⟨(lt_of_le_of_lt (Measure.restrict_mono (hsub k) le_rfl univ)
      (measure_lt_top (μ.restrict (U k)) univ))⟩
  have hmass_le (k : ℕ) : μ.real (Ω k)≤μ.real (U k) :=
    ENNReal.toReal_mono (by
      simpa only [Measure.restrict_apply_univ] using (measure_lt_top (μ.restrict (U k)) univ).ne)
      (measure_mono (hsub k))
  have hinner : Tendsto (fun k => (μ.real (U k))⁻¹*∫ x in Ω k, (z k x)^2 ∂μ)
      atTop (𝓝 0) := by
    apply squeeze_zero (fun k => mul_nonneg (inv_nonneg.mpr (hmass k).le)
      (integral_nonneg fun _ => sq_nonneg _)) _ hlim
    intro k
    apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr (hmass k).le)
    exact setIntegral_mono_set (hz k).integrable_sq
      (Eventually.of_forall fun x => sq_nonneg _) (Eventually.of_forall (hsub k))
  have he := containing_mass_gamma_l2_error_tendsto μ hQ Ω (fun k => μ.real (U k))
    hmass hmass_le r hr f g z (fun _ _ => 1) hM hL zero_le_one hf hg
    (Eventually.of_forall fun _ => Eventually.of_forall fun _ => by norm_num)
    (fun k => (hz k).mono_measure (Measure.restrict_mono (hsub k) le_rfl))
    (fun _ => aestronglyMeasurable_const) hinner
  have hint : ∀ᶠ k in atTop,
      (∫ x in U k, z k x*localGamma μ hQ (f k) (g k) x ∂μ)=
      ∫ x in Ω k, z k x*localGamma μ hQ (f k) (g k) x ∂μ := by
    filter_upwards [hz_zero] with k hk
    apply setIntegral_eq_of_subset_of_ae_sdiff_eq_zero (hU k).nullMeasurableSet (hsub k)
    rw [ae_restrict_iff' (hU k)] at hk
    filter_upwards [hk] with x hx hxs
    rw [hx hxs.1 hxs.2,zero_mul]
  have he' : Tendsto (fun k => r k^2*(μ.real (U k))⁻¹*
      ∫ x in Ω k, z k x*localGamma μ hQ (f k) (g k) x ∂μ) atTop (𝓝 0) := by
    simpa only [one_mul] using he
  apply he'.congr'
  exact hint.mono fun k hk => congrArg (fun t : ℝ => r k^2*(μ.real (U k))⁻¹*t) hk.symm

end RegularPointCoordinates

end

end OAI
