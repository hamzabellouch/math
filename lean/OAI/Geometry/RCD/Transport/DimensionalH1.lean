import OAI.Geometry.RCD.Transport.DimensionalPotential
import OAI.Geometry.RCD.Heat.EntropyPowerRateContinuous

namespace OAI

/-! # The dimensional optimal potential for bounded compact Sobolev densities

The proved square-root probability recovery and a common-support potential
subsequence pass the exact finite-dimensional bound to the actual density.
-/

open Set Filter MeasureTheory Metric TopologicalSpace
open scoped Topology NNReal ENNReal
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
attribute [local instance] pathBorel pathBorelSpace

theorem NoncollapsedRCD.quantitative_H1_dimensional_subgradient
    (K : ℝ) (n : ℕ) (hn : 2 ≤ n) (hX : NoncollapsedRCD K n X)
    (hK : K ≤ 0) {N : ℝ} (hN : (n:ℝ) ≤ N)
    (ν₀ ν₁ : Measure X) [IsProbabilityMeasure ν₀] [IsProbabilityMeasure ν₁]
    {C : ℝ≥0∞} (hC : C ≠ ∞)
    (h0 : ν₀ ≤ C • hausdorff n X) (h1 : ν₁ ≤ C • hausdorff n X)
    (p : X) {R : ℝ} (hR : 0 ≤ R)
    (hs0 : ∀ᵐ x ∂ν₀, dist x p ≤ R) (hs1 : ∀ᵐ x ∂ν₁, dist x p ≤ R)
    (ρ : SobolevSpace (hausdorff n X) hX.quadratic)
    (M : ℝ≥0)
    (hρ : ∀ᵐ x ∂hausdorff n X, 0 ≤ SobolevSpace.toLp _ hX.quadratic ρ x ∧
      SobolevSpace.toLp _ hX.quadratic ρ x ≤ M)
    (hρS : ∀ᵐ x ∂hausdorff n X, SobolevSpace.toLp _ hX.quadratic ρ x ≠ 0 → dist p x ≤ R)
    (hρM : (∫x, SobolevSpace.toLp _ hX.quadratic ρ x ∂hausdorff n X) = 1)
    (hν : ν₀ = (hausdorff n X).withDensity
      (fun x => ENNReal.ofReal (SobolevSpace.toLp _ hX.quadratic ρ x))) :
    ∃ (u : SobolevSpace (hausdorff n X) hX.quadratic) (φ ψ : X → ℝ),
      LipschitzWith ⟨5*(2*(max R 0+1)),by positivity⟩ φ ∧
      LipschitzWith ⟨5*(2*(max R 0+1)),by positivity⟩ ψ ∧
      (∀ x, |φ x| ≤ 10*(2*(max R 0+1))^2) ∧ (∀ x, |ψ x| ≤ 10*(2*(max R 0+1))^2) ∧
      tsupport φ ⊆ closedBall p (6*(2*(max R 0+1))) ∧
      tsupport ψ ⊆ closedBall p (6*(2*(max R 0+1))) ∧
      HasCompactSupport φ ∧ HasCompactSupport ψ ∧
      (φ =ᵐ[hausdorff n X] SobolevSpace.toLp _ hX.quadratic u) ∧
      (∀ x y, φ x+ψ y ≤ dist x y^2/2) ∧
      (∫x, φ x ∂ν₀)+(∫x, ψ x ∂ν₁) = (wassersteinSq ν₀ ν₁).toReal/2 ∧
      -energyForm (hausdorff n X) hX.quadratic u ρ ≤
        entropyPowerRate N (-(K*(wassersteinSq ν₀ ν₁).toReal/N))
          (Real.exp (-boltzmannEntropy (hausdorff n X) ν₀/N))
          (Real.exp (-boltzmannEntropy (hausdorff n X) ν₁/N)) := by
  let : SeparableSpace X := hX.separable
  let : ProperSpace X := hX.proper K n hn
  let μ := hausdorff n X
  let : IsLocallyFiniteMeasure μ := locallyFinite_of_finiteOnBounded μ hX.finiteOnBounded
  obtain ⟨qs,hs,hq,hLip,hrep,hb,hsup,hm,hpt,hEnt⟩ :=
    SobolevSpace.quantitative_strong_probability_square_recovery μ hX.quadratic ρ M hρ p hρS hρM
  let B := 2*(max R 0+1)
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hRB : R ≤ B := by dsimp [B]; linarith [le_max_left R 0,le_max_right R 0]
  have hsc (i : ℕ) : HasCompactSupport (hs i) := by
    apply (isCompact_closedBall p B).of_isClosed_subset (isClosed_tsupport _) (closure_minimal _ isClosed_closedBall)
    intro x hx
    simpa only [mem_closedBall,dist_comm] using hsup i x hx
  let νs : ℕ → Measure X := fun i => μ.withDensity (fun x => ENNReal.ofReal (hs i x^2))
  let (i : ℕ) : IsProbabilityMeasure (νs i) :=
    squareDensity_probability μ (compactSquare_integrable μ (hLip i).choose_spec.continuous (hsc i)) (hm i)
  let D : ℝ≥0∞ := max C (ENNReal.ofReal (2*M))
  have hD : D ≠ ∞ := by
    simp only [D, ne_eq, max_eq_top, not_or]
    exact ⟨hC, ENNReal.ofReal_ne_top⟩
  have h0D : ν₀ ≤ D • μ := h0.trans (by gcongr; exact le_max_left _ _)
  have h1D : ν₁ ≤ D • μ := h1.trans (by gcongr; exact le_max_left _ _)
  have hDs (i : ℕ) : νs i ≤ D • μ := by
    calc
      _ ≤ μ.withDensity (fun _ => ENNReal.ofReal (2*M)) :=
        withDensity_mono (Eventually.of_forall fun x => ENNReal.ofReal_le_ofReal (hb i x).2)
      _ = ENNReal.ofReal (2*M) • μ := withDensity_const _
      _ ≤ D • μ := by gcongr; exact le_max_right _ _
  have hSqs (i : ℕ) (x : X) (hx : hs i x^2 ≠ 0) : x ∈ closedBall p B := by
    have hh : hs i x ≠ 0 := by intro hz; apply hx; rw [hz]; norm_num
    simpa only [mem_closedBall,dist_comm] using hsup i x hh
  have hSs (i : ℕ) : ∀ᵐ x ∂νs i, dist x p ≤ B := by
    apply (ae_withDensity_iff ((hLip i).choose_spec.continuous.measurable.pow_const 2).ennreal_ofReal).mpr
    filter_upwards with x hx
    apply hSqs i x
    intro hz
    exact hx (by rw [hz,ENNReal.ofReal_zero])
  have hνs (i : ℕ) : νs i = μ.withDensity (fun x => ENNReal.ofReal (SobolevSpace.toLp μ hX.quadratic (qs i) x)) := by
    apply withDensity_congr_ae
    exact (hrep i).symm.fun_comp ENNReal.ofReal
  have hcore (i : ℕ) := hX.sqrt_core_dimensional_potential hn hK hN (νs i) ν₁ hD
    (hDs i) h1D p hB (hSs i) (hs1.mono fun x hx => hx.trans hRB) (qs i)
    (hLip i).choose_spec (fun x => (hb i x).1)
    ((hLip i).choose_spec.continuous.integrable_of_hasCompactSupport (hsc i)) (hrep i) (hνs i)
  choose us φs ψs hφs hψs hφb hψb hφsup hψsup hφsc hψsc hus hads hduals hineqs using hcore
  let L : ℝ≥0 := ⟨5*B,by positivity⟩
  have hφabs (i : ℕ) (x : X) : |φs i x| ≤ 10*B^2 := by
    rw [abs_of_nonneg (hφb i x).1]
    exact (hφb i x).2
  have hψabs (i : ℕ) (x : X) : |ψs i x| ≤ 10*B^2 := by
    rw [abs_of_nonpos (hψb i x).2]
    linarith [(hψb i x).1]
  obtain ⟨u,φ,ψ,s,hsm,hφ,hψ,hφB,hψB,hφS,hψS,hu,hφlim,hψlim,hub,hul⟩ :=
    SobolevSpace.common_support_dual_subsequence μ hX.quadratic p (B+(5*B)) (10*B^2) L
      us φs ψs hφs hψs hφabs hψabs hφsup hψsup hus
  have had (x y : X) : φ x+ψ y ≤ dist x y^2/2 :=
    le_of_tendsto ((hφlim x).add (hψlim y)) (Eventually.of_forall fun i => hads (s i) x y)
  have heL := SobolevSpace.energyForm_tendsto_weak_strong μ hX.quadratic hub hul (hq.comp hsm.tendsto_atTop)
  have hρm : Measurable (SobolevSpace.toLp μ hX.quadratic ρ : X → ℝ) :=
    (Lp.stronglyMeasurable _).measurable
  have hpt' : ∀ᵐ x ∂μ, Tendsto (fun i => hs (s i) x^2) atTop (𝓝 (SobolevSpace.toLp μ hX.quadratic ρ x)) :=
    hpt.mono fun x hx => hx.comp hsm.tendsto_atTop
  have hcost := hX.bounded_density_dual_limit K n hn ν₀ ν₁ (fun i => νs (s i)) hD h0D h1D
    (fun i => hDs (s i)) p hB (hs0.mono fun x hx => hx.trans hRB) (hs1.mono fun x hx => hx.trans hRB)
    (fun i => hSs (s i))
    (fun i => (hLip (s i)).choose_spec.continuous.measurable.pow_const 2)
    (M := (2*M:ℝ)) (fun i x => ⟨sq_nonneg _,(hb (s i) x).2⟩) (fun i => hSqs (s i))
    hρm (hρ.mono fun x hx => hx.1) hpt' (fun i => rfl) hν
    (fun i => hφs (s i)) (fun i => hψs (s i)) (fun i => hφabs (s i)) (fun i => hψabs (s i))
    hφ hψ hφB hψB hφlim hψlim had (fun i => hduals (s i))
  have hEL : Tendsto (fun i => boltzmannEntropy μ (νs (s i))) atTop (𝓝 (boltzmannEntropy μ ν₀)) := by
    have he0 : boltzmannEntropy μ ν₀ = ∫x, SobolevSpace.toLp μ hX.quadratic ρ x*
        Real.log (SobolevSpace.toLp μ hX.quadratic ρ x) ∂μ := by
      rw [hν]
      exact realDensity_entropy μ hρm (hρ.mono fun x hx => hx.1)
    have hes (i : ℕ) : boltzmannEntropy μ (νs i) = ∫x, hs i x^2*Real.log (hs i x^2) ∂μ :=
      squareDensity_entropy μ (hLip i).choose_spec.continuous.measurable
    rw [he0]
    simp_rw [hes]
    exact hEnt.comp hsm.tendsto_atTop
  have hBS : B+(5*B) = 6*B := by ring
  refine ⟨u,φ,ψ,hφ,hψ,hφB,hψB,by simpa only [hBS] using hφS,by simpa only [hBS] using hψS,
    (isCompact_closedBall p _).of_isClosed_subset (isClosed_tsupport φ) hφS,
    (isCompact_closedBall p _).of_isClosed_subset (isClosed_tsupport ψ) hψS,
    hu,had,hcost.2,?_⟩
  have hnR : (2:ℝ) ≤ n := by exact_mod_cast hn
  have hN0 : 0 < N := by linarith
  have hnn (w : ℝ) (hw : 0 ≤ w) : 0 ≤ -(K*w/N) :=
    neg_nonneg.mpr (div_nonpos_of_nonpos_of_nonneg
      (mul_nonpos_of_nonpos_of_nonneg hK hw) hN0.le)
  have hrate := tendsto_entropyPowerRate (N := N)
    (b := fun _ : ℕ => Real.exp (-boltzmannEntropy μ ν₁/N))
    (fun i => hnn (wassersteinSq (νs (s i)) ν₁).toReal ENNReal.toReal_nonneg)
    (hnn (wassersteinSq ν₀ ν₁).toReal ENNReal.toReal_nonneg) (Real.exp_ne_zero _)
    ((hcost.1.const_mul K).div_const N).neg
    (Real.continuous_exp.tendsto _ |>.comp (hEL.neg.div_const N)) tendsto_const_nhds
  exact le_of_tendsto_of_tendsto heL.neg hrate (Eventually.of_forall fun i => hineqs (s i))


end RegularPointCoordinates

end

end OAI
