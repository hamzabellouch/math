import OAI.NumberTheory.JointDickman.Amplification.FullSpatialComparison
import OAI.NumberTheory.JointDickman.Amplification.BoundedBoxFullModel

namespace OAI

/-! # Spatial comparison with bounded, varying box weights -/

namespace JointDickman
open Finset Filter
open scoped Topology SchwartzMap

theorem bounded_box_spatial_comparison
    (hSD : PublishedInputs.SquarefreeSelbergDelangeInput)
    (hSW : PublishedInputs.SquarefreeCharacterEstimateInput)
    (hM : PublishedInputs.PrimeReciprocalMertensInput)
    (hMP : PublishedInputs.PrimeProductMertensInput)
    {D : ℝ} (hD : 0 ≤ D)
    {a b t η : ℝ} (ha : 0 < a) (hab : a ≤ b) (ht : 0 < t) (hη : 0 < η)
    (w₁ w₂ w₁' w₂' : ℝ → ℝ) (w : 𝓢(ℝ,ℝ))
    {M₁ M₂ D₁ D₂ : ℝ} (hM₁ : 0 ≤ M₁) (hM₂ : 0 ≤ M₂) (hD₁ : 0 ≤ D₁) (hD₂ : 0 ≤ D₂)
    (hw₁ : ∀ x, HasDerivAt w₁ (w₁' x) x) (hw₂ : ∀ x, HasDerivAt w₂ (w₂' x) x)
    (hwb₁ : ∀ x, |w₁ x| ≤ M₁) (hwb₂ : ∀ x, |w₂ x| ≤ M₂)
    (hwd₁ : ∀ x, |w₁' x| ≤ D₁) (hwd₂ : ∀ x, |w₂' x| ≤ D₂)
    (hs₁ : ∀ x, x ≤ a ∨ b < x → w₁ x = 0)
    (hs₂ : ∀ x, x ≤ a ∨ b < x → w₂ x = 0) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ ε : ℕ → ℝ, Tendsto ε atTop (𝓝 0) ∧
      ∀ m : ℕ, 0 < m → ∀ᶠ B : ℕ in atTop,
      ∀ j : ℕ, [NeZero j] → ∀ Q : ℕ, 0 < Q → j*Q ≤ B →
      ∀ T : ℝ, 0 < T → η*T ≤ j → ∀ S : Finset ℤ,
      (∀ k ∈ S, (k : ℝ)*t ∈ Set.Icc ((9/10 : ℝ)*B) ((5/2 : ℝ)*B)) →
      ∀ d : ℤ → ℝ, (∀ k ∈ S, |d k| ≤ D) →
      ∀ g h : (auxiliaryPrimes B → Bool) → ℝ,
      (∀ x, |g x| ≤ 1) → (∀ x, |h x| ≤ 1) →
      T*‖geometricFullArcSum B j Q a b T t S d g h w₁ w₂ w-
        ((singularSeries j : ℂ)/j)*
          (cellMassBilinear m B (logCellSignedMass m B g) (logCellSignedMass m B h)
            (geometricWindowKernel m B t (Real.log a) (Real.log b) S
              (endpointSpatialWeight m B t (T/j) d w₁ w₂ w)) : ℂ)‖ ≤
        ε B+C*(T/j)*((j : ℝ)/j.totient)*singularSeriesTail (Q+1) := by
  obtain ⟨ε,hε,hfull⟩ := bounded_box_full_model_vanishing hSD hSW hM hMP hD
    ha hab ht hη w₁ w₂ w₁' w₂' w hM₁ hM₂ hD₁ hD₂ hw₁ hw₂ hwb₁ hwb₂ hwd₁ hwd₂ hs₁ hs₂
  have hlogs : Real.log a ≤ Real.log b := Real.log_le_log ha hab
  obtain ⟨C,hC,hseries⟩ := geometric_singularSeries_error hSD hSW hM hMP ht hlogs
    w₁ w₂ w hM₁ hM₂ hwb₁ hwb₂
  refine ⟨D*C,mul_nonneg hD hC,ε,hε,?_⟩
  intro m hm
  filter_upwards [hfull m hm,hseries m hm,eventually_ge_atTop 1]
    with B hf hs hB
  intro j _ Q hQ hscale T hT hlag S hbox d hdbound g h hg hh
  have hcut : j*Q ≤ auxiliaryCutoff B := by
    exact hscale.trans (le_self_pow₀ hB (by decide : (1000 : ℕ) ≠ 0))
  have hfirst := hf j Q hQ hscale T hT hlag S hbox (fun k => (d k : ℂ))
    (fun k hk => by simpa only [Complex.norm_real,Real.norm_eq_abs] using hdbound k hk) g h hg hh
  have hsecond := hs j Q hcut S (T/j) D hD d hdbound g h hg hh
  rw [geometric_full_spatial_error_split]
  calc
    _ ≤ T*‖geometricFullModelDifference m B j Q a b T t S (fun k => (d k : ℂ)) g h w₁ w₂ w‖+
        T*‖((B : ℂ)/j)*∑ k ∈ S, (d k : ℂ)*
          (sampledEndpointKernel m B j Q (geometricHistogramWindow m B t (Real.log a) (Real.log b) k)
              g h w₁ w₂ (Real.exp ((k : ℝ)*t)) (T/j) w-
            (singularSeries j : ℂ)*sampledEndpointLogKernel m B
              (geometricHistogramWindow m B t (Real.log a) (Real.log b) k)
              g h w₁ w₂ (Real.exp ((k : ℝ)*t)) (T/j) w)‖ := by
      exact (mul_le_mul_of_nonneg_left (norm_add_le _ _) hT.le).trans_eq (mul_add _ _ _)
    _ ≤ ε B+T*((D*C)*(((j : ℝ)/j.totient)/j)*singularSeriesTail (Q+1)) :=
      add_le_add hfirst (mul_le_mul_of_nonneg_left hsecond hT.le)
    _ = _ := by ring

end JointDickman

end OAI
