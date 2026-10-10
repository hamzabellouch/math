import OAI.NumberTheory.JointDickman.Amplification.BoundedBoxSpatial

namespace OAI

/-! # The retained-arc kernel has a fixed finite coarse approximation -/

namespace JointDickman
open Finset Filter
open scoped Topology SchwartzMap

theorem bounded_box_coarse_comparison
    (hSD : PublishedInputs.SquarefreeSelbergDelangeInput)
    (hSW : PublishedInputs.SquarefreeCharacterEstimateInput)
    (hM : PublishedInputs.PrimeReciprocalMertensInput)
    (hMP : PublishedInputs.PrimeProductMertensInput)
    {D : ℝ} (hD : 0 ≤ D)
    {a b t η : ℝ} (ha : 0 < a) (hab : a ≤ b) (ht : 0 < t) (hη : 0 < η)
    (w₁ w₂ w₁' w₂' : ℝ → ℝ) (w : 𝓢(ℝ,ℝ))
    {M₁ M₂ D₁ D₂ M₀ : ℝ} (hM₁ : 0 ≤ M₁) (hM₂ : 0 ≤ M₂) (hD₁ : 0 ≤ D₁) (hD₂ : 0 ≤ D₂)
    (hM₀ : 0 ≤ M₀)
    (hw₁ : ∀ x, HasDerivAt w₁ (w₁' x) x) (hw₂ : ∀ x, HasDerivAt w₂ (w₂' x) x)
    (hwb₁ : ∀ x, |w₁ x| ≤ M₁) (hwb₂ : ∀ x, |w₂ x| ≤ M₂)
    (hwd₁ : ∀ x, |w₁' x| ≤ D₁) (hwd₂ : ∀ x, |w₂' x| ≤ D₂)
    (hwb₀ : ∀ x, |w x| ≤ M₀)
    (hs₁ : ∀ x, x ≤ a ∨ b < x → w₁ x = 0)
    (hs₂ : ∀ x, x ≤ a ∨ b < x → w₂ x = 0)
 :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ ε : ℕ → ℝ, Tendsto ε atTop (𝓝 0) ∧
      ∀ δ : ℝ, 0 < δ → ∃ m : ℕ, 0 < m ∧ ∀ᶠ B : ℕ in atTop,
      ∀ j : ℕ, [NeZero j] → ∀ Q : ℕ, 0 < Q → j*Q ≤ B →
      ∀ T : ℝ, 0 < T → η*T ≤ j → ∀ S : Finset ℤ,
      (∀ k ∈ S, (k : ℝ)*t ∈ Set.Icc ((9/10 : ℝ)*B) ((5/2 : ℝ)*B)) →
      ∀ d : ℤ → ℝ, (∀ k ∈ S, |d k| ≤ D) →
      ∀ g h : (auxiliaryPrimes B → Bool) → ℝ,
      (∀ x, |g x| ≤ 1) → (∀ x, |h x| ≤ 1) →
      let K := geometricWindowKernel m B t (Real.log a) (Real.log b) S
        (endpointSpatialWeight m B t (T/j) d w₁ w₂ w)
      T*‖geometricFullArcSum B j Q a b T t S d g h w₁ w₂ w-
        ((singularSeries j : ℂ)/j)*
          (cellMassBilinear m B (coarseLogMass m B g) (coarseLogMass m B h) K : ℂ)‖ ≤
        ε B+C*(T/j)*((j : ℝ)/j.totient)*singularSeriesTail (Q+1)+δ*(T/j)*singularSeries j := by
  obtain ⟨C,hC,ε,hε,hfull⟩ := bounded_box_spatial_comparison hSD hSW hM hMP hD
    ha hab ht hη w₁ w₂ w₁' w₂' w hM₁ hM₂ hD₁ hD₂ hw₁ hw₂ hwb₁ hwb₂ hwd₁ hwd₂ hs₁ hs₂
  refine ⟨C,hC,ε,hε,?_⟩
  intro δ hδ
  let A := 2*(((1+Real.log b-Real.log a)/t+1)*(D*M₁*M₂*M₀))*(Real.log b-Real.log a+2)
  have hlogs : Real.log a ≤ Real.log b := Real.log_le_log ha hab
  have hwidth : 0 ≤ 1+Real.log b-Real.log a := by linarith
  have hwidth' : 0 ≤ Real.log b-Real.log a+2 := by linarith
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have he : 0 < δ/(A+1) := div_pos hδ (by linarith)
  obtain ⟨m,hm,hcoarse⟩ := geometricSpatialKernel_coarse hSD hSW hM hMP he ht hlogs
    hD hM₁ hM₂ hM₀ w₁ w₂ w hwb₁ hwb₂ hwb₀
  refine ⟨m,hm,?_⟩
  filter_upwards [hfull m hm,hcoarse,eventually_ge_atTop 1]
    with B hf hb hB
  intro j _ Q hQ hscale T hT hlag S hbox d hdbound g h hg hh
  dsimp only
  let K := geometricWindowKernel m B t (Real.log a) (Real.log b) S
    (endpointSpatialWeight m B t (T/j) d w₁ w₂ w)
  let R := cellMassBilinear m B (logCellSignedMass m B g) (logCellSignedMass m B h) K
  let Rc := cellMassBilinear m B (coarseLogMass m B g) (coarseLogMass m B h) K
  have hclose : |R-Rc| ≤ δ := by
    have hb' : |R-Rc| ≤ A*(δ/(A+1)) := hb S (T/j) d hdbound g h hg hh
    refine hb'.trans ?_
    have he' : A/(A+1) ≤ 1 := (div_le_one (by linarith)).mpr (by linarith)
    calc
      _ = δ*(A/(A+1)) := by ring
      _ ≤ δ*1 := mul_le_mul_of_nonneg_left he' hδ.le
      _ = δ := mul_one _
  have hSp : 0 ≤ singularSeries j := (singularSeries_bounds hMP j).1
  have hscalar : ‖((singularSeries j : ℂ)/j)*((R : ℂ)-(Rc : ℂ))‖ ≤
      (singularSeries j/(j : ℝ))*δ := by
    rw [norm_mul,norm_div,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hSp,
      Complex.norm_natCast,← Complex.ofReal_sub,Complex.norm_real,Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left hclose (by positivity)
  have hf' := hf j Q hQ hscale T hT hlag S hbox d hdbound g h hg hh
  calc
    _ ≤ T*‖geometricFullArcSum B j Q a b T t S d g h w₁ w₂ w-
        ((singularSeries j : ℂ)/j)*(R : ℂ)‖+
      T*‖((singularSeries j : ℂ)/j)*((R : ℂ)-(Rc : ℂ))‖ := by
      have htri := norm_sub_le_norm_sub_add_norm_sub
        (geometricFullArcSum B j Q a b T t S d g h w₁ w₂ w)
        (((singularSeries j : ℂ)/j)*(R : ℂ)) (((singularSeries j : ℂ)/j)*(Rc : ℂ))
      rw [← mul_sub] at htri
      exact (mul_le_mul_of_nonneg_left htri hT.le).trans_eq (mul_add _ _ _)
    _ ≤ (ε B+C*(T/j)*((j : ℝ)/j.totient)*singularSeriesTail (Q+1))+
        T*((singularSeries j/(j : ℝ))*δ) :=
      add_le_add hf' (mul_le_mul_of_nonneg_left hscalar hT.le)
    _ = _ := by ring

end JointDickman

end OAI
