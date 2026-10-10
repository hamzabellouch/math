import OAI.MathematicalPhysics.DefocusingNLS.Nonlinear.MaximalSobolevEndpoint
import OAI.MathematicalPhysics.DefocusingNLS.Linear.SobolevDuhamelIntegral
import OAI.MathematicalPhysics.DefocusingNLS.Nonlinear.BlowupRate

namespace OAI

/-! # Maximality among strong Sobolev Schrödinger solutions -/

open Filter Topology Set

namespace DefocusingNLS

theorem continuousOn_maximalSobolevSchrodingerFlow
    (k : ℝ) (hk : 6 < k) (m : ℕ) (f₀ : FourierL2) :
    ContinuousOn (maximalSobolevSchrodingerFlow k hk m f₀)
      (maximalSobolevInteractionDomain k hk m f₀) := by
  apply continuousOn_schrodingerFlow_curve
  intro t ht
  exact (hasDerivAt_maximalSobolevInteractionFlow k hk m f₀ ht).continuousAt.continuousWithinAt

/-- Every strong solution through the initial datum is a restriction of the maximal flow. -/
theorem strongSobolevSchrodingerSolution_restricts_maximal
    (k : ℝ) (hk : 6 < k) (m : ℕ) (f₀ : FourierL2)
    (u : ℝ → FourierL2) (a b : ℝ) (ha : a < 0) (hb : 0 < b)
    (hu₀ : u 0 = f₀) (huc : ContinuousOn u (Ioo a b))
    (hu : ∀ t ∈ Ioo a b, HasDerivAt (fun s => lowerSobolevInclusion (u s))
      (lowerSobolevGenerator (u t) -
        Complex.I • lowerSobolevInclusion (sobolevOddPower k hk m (u t))) t) :
    Ioo a b ⊆ maximalSobolevInteractionDomain k hk m f₀ ∧
      EqOn u (maximalSobolevSchrodingerFlow k hk m f₀) (Ioo a b) := by
  let P : SobolevInteractionPatch k hk m f₀ :=
    { left := a
      right := b
      left_neg := ha
      right_pos := hb
      curve := inverseSchrodingerCurve u
      initial := by simp [inverseSchrodingerCurve, hu₀]
      solves := fun t ht => hasDerivAt_inverseSchrodingerCurve k hk m u a b t huc hu ht }
  refine ⟨P.subset_maximalDomain, ?_⟩
  intro t ht
  change u t = schrodingerFlow t (maximalSobolevInteractionFlow k hk m f₀ t)
  rw [maximalSobolevInteractionFlow_eq_patch P ht]
  change u t = schrodingerFlow t (schrodingerFlow (-t) (u t))
  rw [← schrodingerFlow_add, add_neg_cancel, schrodingerFlow_zero]

/-- A positive rescaled observation fixes the finite endpoint of the maximal strong solution.
The observation may be evaluation at any point of the twelve-dimensional torus. -/
theorem maximalSobolev_lifespan_of_positive_rescaled_observation
    {F : Type*} [NormedAddCommGroup F]
    (k : ℝ) (hk : 6 < k) (m : ℕ) (f₀ : FourierL2)
    (u : ℝ → FourierL2) (a T β c : ℝ) (ha : a < 0) (hT : 0 < T)
    (hβ : 0 < β) (hc : 0 < c) (hu₀ : u 0 = f₀)
    (huc : ContinuousOn u (Ioo a T))
    (hu : ∀ t ∈ Ioo a T, HasDerivAt (fun s => lowerSobolevInclusion (u s))
      (lowerSobolevGenerator (u t) -
        Complex.I • lowerSobolevInclusion (sobolevOddPower k hk m (u t))) t)
    (observe : FourierL2 → F) (hobs : Continuous observe)
    (hblowup : Tendsto (fun t => (T - t) ^ β * ‖observe (u t)‖)
      (𝓝[<] T) (𝓝 c)) :
    BddAbove (maximalSobolevInteractionDomain k hk m f₀) ∧
      sSup (maximalSobolevInteractionDomain k hk m f₀) = T := by
  obtain ⟨hsub, heq⟩ := strongSobolevSchrodingerSolution_restricts_maximal
    k hk m f₀ u a T ha hT hu₀ huc hu
  have hnot : T ∉ maximalSobolevInteractionDomain k hk m f₀ := by
    intro hmem
    have hcont := (continuousOn_maximalSobolevSchrodingerFlow k hk m f₀ T hmem).continuousAt
      ((isOpen_maximalSobolevInteractionDomain k hk m f₀).mem_nhds hmem)
    have hlim := hobs.continuousAt.tendsto.comp
      (hcont.tendsto.mono_left (nhdsWithin_le_nhds : 𝓝[<] T ≤ 𝓝 T))
    have hev : (fun t => observe (u t)) =ᶠ[𝓝[<] T]
        (fun t => observe (maximalSobolevSchrodingerFlow k hk m f₀ t)) := by
      filter_upwards [Ioo_mem_nhdsLT (show a < T by linarith)] with t ht
      rw [heq ht]
    exact no_left_limit_of_positive_rescaled_norm (fun t => observe (u t)) T β c hβ hc
      hblowup ⟨_, hlim.congr' hev.symm⟩
  have hbound : ∀ t ∈ maximalSobolevInteractionDomain k hk m f₀, t ≤ T := by
    intro t ht
    by_contra hn
    apply hnot
    exact (isPreconnected_maximalSobolevInteractionDomain k hk m f₀).Icc_subset
      (zero_mem_maximalSobolevInteractionDomain k hk m f₀) ht ⟨hT.le, (lt_of_not_ge hn).le⟩
  refine ⟨⟨T, hbound⟩, ?_⟩
  apply csSup_eq_of_forall_le_of_forall_lt_exists_gt
    ⟨0, zero_mem_maximalSobolevInteractionDomain k hk m f₀⟩ hbound
  intro r hr
  let s := (max a r + T) / 2
  have hs : s ∈ Ioo a T := by
    have hmax : max a r < T := max_lt (by linarith) hr
    have hamax := le_max_left a r
    dsimp [s]
    constructor <;> linarith
  refine ⟨s, hsub hs, ?_⟩
  have hrmax := le_max_right a r
  dsimp [s]
  linarith [max_lt (show a < T by linarith) hr]

end DefocusingNLS

end OAI
