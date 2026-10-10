import Mathlib
import OAI.Analysis.RCDHeat.DimensionalH1
import OAI.Analysis.RCDHeat.WeightedMidpointEndpoint

namespace OAI

/-! Cheeger energy, curvature-dimension transport and heat-flow estimates: WeightedDimensionalH1Square, WeightedDimensionalH1, VariableHeatSecant, DimensionalDualNorm. -/



namespace RegularPointCoordinates

section

 

open Set Filter MeasureTheory Metric TopologicalSpace
open scoped Topology NNReal ENNReal
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]

theorem NoncollapsedRCD.weighted_dimensional_H1_square_dual
    (K : ℝ) (n : ℕ) (hn : 2 ≤ n) (hX : NoncollapsedRCD K n X)
    (ν₀ ν₁ : Measure X) [IsProbabilityMeasure ν₀] [IsProbabilityMeasure ν₁]
    {C : ℝ≥0∞} (hC : C ≠ ∞)
    (h0 : ν₀ ≤ C • hausdorff n X) (h1 : ν₁ ≤ C • hausdorff n X)
    (p : X) {R : ℝ} (hR : 0 ≤ R)
    (hs0 : ∀ᵐ x ∂ν₀, dist x p ≤ R) (hs1 : ∀ᵐ x ∂ν₁, dist x p ≤ R)
    (ρ ρ₁ : SobolevSpace (hausdorff n X) hX.quadratic)
    (M : ℝ≥0)
    (hρ : ∀ᵐ x ∂hausdorff n X, 0 ≤ SobolevSpace.toLp _ hX.quadratic ρ x ∧
      SobolevSpace.toLp _ hX.quadratic ρ x ≤ M)
    (hρS : ∀ᵐ x ∂hausdorff n X, SobolevSpace.toLp _ hX.quadratic ρ x ≠ 0 → dist p x ≤ R)
    (hρM : (∫x, SobolevSpace.toLp _ hX.quadratic ρ x ∂hausdorff n X) = 1)
    (hν : ν₀ = (hausdorff n X).withDensity
      (fun x => ENNReal.ofReal (SobolevSpace.toLp _ hX.quadratic ρ x)))
    {h₁ : X → ℝ} {L₁ : ℝ≥0} (hh₁ : LipschitzWith L₁ h₁)
    (hh₁0 : ∀ x, 0 ≤ h₁ x) (hi₁ : Integrable h₁ (hausdorff n X))
    (hrep₁ : (SobolevSpace.toLp _ hX.quadratic ρ₁ : X → ℝ) =ᵐ[hausdorff n X] fun x => h₁ x^2)
    (hν₁ : ν₁ = (hausdorff n X).withDensity
      (fun x => ENNReal.ofReal (SobolevSpace.toLp _ hX.quadratic ρ₁ x)))
    (N : ℝ) (hN : (n:ℝ) ≤ N) (a b : ℝ) (ha : 0 ≤ a) (hb0 : 0 ≤ b) :
    ∃ d : CompactSobolevDual (hausdorff n X) hX.quadratic ν₀ ν₁
      p (16*(2*(max R 0+1))) (10*(2*(max R 0+1))^2) ⟨5*(2*(max R 0+1)),by positivity⟩,
      K*(wassersteinSq ν₀ ν₁).toReal*(a^2+a*b+b^2)/3-N*(a-b)^2 ≤
        a^2*energyForm (hausdorff n X) hX.quadratic d.u ρ+
          b^2*energyForm (hausdorff n X) hX.quadratic d.v ρ₁ := by
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
  have hcore (i : ℕ) := hX.weighted_dimensional_core_dual K n hn (νs i) ν₁ hD
    (hDs i) h1D p hB (hSs i) (hs1.mono fun x hx => hx.trans hRB) (qs i) ρ₁
    (hLip i).choose_spec hh₁ (fun x => (hb i x).1) hh₁0
    ((hLip i).choose_spec.continuous.integrable_of_hasCompactSupport (hsc i)) hi₁
    (hrep i) hrep₁ (hνs i) hν₁ N hN a b ha hb0
  choose ds henergy using hcore
  have hEL : Tendsto (fun i => boltzmannEntropy μ (νs i)) atTop (𝓝 (boltzmannEntropy μ ν₀)) := by
    have he0 : boltzmannEntropy μ ν₀ = ∫x, SobolevSpace.toLp μ hX.quadratic ρ x*
        Real.log (SobolevSpace.toLp μ hX.quadratic ρ x) ∂μ := by
      rw [hν]
      exact realDensity_entropy μ (Lp.stronglyMeasurable _).measurable (hρ.mono fun x hx => hx.1)
    have hes (i : ℕ) : boltzmannEntropy μ (νs i) = ∫x, hs i x^2*Real.log (hs i x^2) ∂μ :=
      squareDensity_entropy μ (hLip i).choose_spec.continuous.measurable
    rw [he0]
    simp_rw [hes]
    exact hEnt
  exact hX.weighted_dimensional_dual_limit K n hn ν₀ ν₁ νs hD h0D h1D hDs p hB
    (hs0.mono fun x hx => hx.trans hRB) (hs1.mono fun x hx => hx.trans hRB) hSs
    (fun i => (hLip i).choose_spec.continuous.measurable.pow_const 2)
    (M := (2*M:ℝ)) (fun i x => ⟨sq_nonneg _,(hb i x).2⟩) hSqs
    ρ ρ₁ qs hq (hρ.mono fun x hx => hx.1) hpt (fun i => rfl) hν hEL ds N a b henergy


 
theorem NoncollapsedRCD.weighted_dimensional_H1_dual
    (K : ℝ) (n : ℕ) (hn : 2 ≤ n) (hX : NoncollapsedRCD K n X)
    (ν₀ ν₁ : Measure X) [IsProbabilityMeasure ν₀] [IsProbabilityMeasure ν₁]
    {C : ℝ≥0∞} (hC : C ≠ ∞)
    (h0 : ν₀ ≤ C • hausdorff n X) (h1 : ν₁ ≤ C • hausdorff n X)
    (p : X) {R : ℝ} (hR : 0 ≤ R)
    (hs0 : ∀ᵐ x ∂ν₀, dist x p ≤ R) (hs1 : ∀ᵐ x ∂ν₁, dist x p ≤ R)
    (ρ ρ₁ : SobolevSpace (hausdorff n X) hX.quadratic)
    (M : ℝ≥0)
    (hρ : ∀ᵐ x ∂hausdorff n X, 0 ≤ SobolevSpace.toLp _ hX.quadratic ρ x ∧
      SobolevSpace.toLp _ hX.quadratic ρ x ≤ M)
    (hρS : ∀ᵐ x ∂hausdorff n X, SobolevSpace.toLp _ hX.quadratic ρ x ≠ 0 → dist p x ≤ R)
    (hρM : (∫x, SobolevSpace.toLp _ hX.quadratic ρ x ∂hausdorff n X) = 1)
    (hν : ν₀ = (hausdorff n X).withDensity
      (fun x => ENNReal.ofReal (SobolevSpace.toLp _ hX.quadratic ρ x)))
    (M₁ : ℝ≥0)
    (hρ₁ : ∀ᵐ x ∂hausdorff n X, 0 ≤ SobolevSpace.toLp _ hX.quadratic ρ₁ x ∧
      SobolevSpace.toLp _ hX.quadratic ρ₁ x ≤ M₁)
    (hρ₁S : ∀ᵐ x ∂hausdorff n X, SobolevSpace.toLp _ hX.quadratic ρ₁ x ≠ 0 → dist p x ≤ R)
    (hρ₁M : (∫x, SobolevSpace.toLp _ hX.quadratic ρ₁ x ∂hausdorff n X) = 1)
    (hν₁ : ν₁ = (hausdorff n X).withDensity
      (fun x => ENNReal.ofReal (SobolevSpace.toLp _ hX.quadratic ρ₁ x)))
    (N : ℝ) (hN : (n:ℝ) ≤ N) (a b : ℝ) (ha : 0 ≤ a) (hb0 : 0 ≤ b) :
    ∃ d : CompactSobolevDual (hausdorff n X) hX.quadratic ν₀ ν₁
      p (16*(2*(max (2*(max R 0+1)) 0+1)))
      (10*(2*(max (2*(max R 0+1)) 0+1))^2) ⟨5*(2*(max (2*(max R 0+1)) 0+1)),by positivity⟩,
      K*(wassersteinSq ν₀ ν₁).toReal*(a^2+a*b+b^2)/3-N*(a-b)^2 ≤
        a^2*energyForm (hausdorff n X) hX.quadratic d.u ρ+
          b^2*energyForm (hausdorff n X) hX.quadratic d.v ρ₁ := by
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
  have hcore (i : ℕ) := hX.weighted_dimensional_H1_square_dual K n hn ν₁ (νs i) hD
    h1D (hDs i) p hB (hs1.mono fun x hx => hx.trans hRB) (hSs i) ρ₁ (qs i)
    M₁ hρ₁ (hρ₁S.mono fun x hx hne => (hx hne).trans hRB) hρ₁M hν₁
    (hLip i).choose_spec (fun x => (hb i x).1)
    ((hLip i).choose_spec.continuous.integrable_of_hasCompactSupport (hsc i))
    (hrep i) (hνs i) N hN b a hb0 ha
  choose dsr henergyR using hcore
  let ds := fun i => (dsr i).flip
  have henergy (i : ℕ) : K*(wassersteinSq (νs i) ν₁).toReal*(a^2+a*b+b^2)/3-N*(a-b)^2 ≤
      a^2*energyForm μ hX.quadratic (ds i).u (qs i)+b^2*energyForm μ hX.quadratic (ds i).v ρ₁ := by
    have he := henergyR i
    rw [wassersteinSq_symm ν₁ (νs i)] at he
    convert he using 1
    all_goals try dsimp only [ds,CompactSobolevDual.flip]
    all_goals first | rfl | ring
  have hEL : Tendsto (fun i => boltzmannEntropy μ (νs i)) atTop (𝓝 (boltzmannEntropy μ ν₀)) := by
    have he0 : boltzmannEntropy μ ν₀ = ∫x, SobolevSpace.toLp μ hX.quadratic ρ x*
        Real.log (SobolevSpace.toLp μ hX.quadratic ρ x) ∂μ := by
      rw [hν]
      exact realDensity_entropy μ (Lp.stronglyMeasurable _).measurable (hρ.mono fun x hx => hx.1)
    have hes (i : ℕ) : boltzmannEntropy μ (νs i) = ∫x, hs i x^2*Real.log (hs i x^2) ∂μ :=
      squareDensity_entropy μ (hLip i).choose_spec.continuous.measurable
    rw [he0]
    simp_rw [hes]
    exact hEnt
  exact hX.weighted_dimensional_dual_limit K n hn ν₀ ν₁ νs hD h0D h1D hDs p hB
    (hs0.mono fun x hx => hx.trans hRB) (hs1.mono fun x hx => hx.trans hRB) hSs
    (fun i => (hLip i).choose_spec.continuous.measurable.pow_const 2)
    (M := (2*M:ℝ)) (fun i x => ⟨sq_nonneg _,(hb i x).2⟩) hSqs
    ρ ρ₁ qs hq (hρ.mono fun x hx => hx.1) hpt (fun i => rfl) hν hEL ds N a b henergy

end

 
section

 

open Set Filter MeasureTheory Metric TopologicalSpace
open scoped Topology NNReal ENNReal
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] [SeparableSpace X] (μ : Measure X) [IsLocallyFiniteMeasure μ]
  (hQ : QuadraticCheegerEnergy μ)

theorem heat_inner_scaled_secant (f : Lp ℝ 2 μ) (v : ℝ) (hv : 0 < v)
    {t h : ℝ} (ht : 0 < t) (hh : 0 < h) (ρ u : SobolevSpace μ hQ) :
    h⁻¹*inner ℝ (SobolevSpace.toLp μ hQ ρ-heatAt μ hQ (v*t) f) (SobolevSpace.toLp μ hQ u) ≤
      -v*energyForm μ hQ u ρ+‖u‖*(v^2*(2*(1+1/(v*t/2)))^2*‖f‖*h)+
      ‖u‖*(h⁻¹+2*v)*‖ρ-heatSobolev μ hQ (v*(t+h)) (mul_pos hv (add_pos ht hh)) f‖ := by
  have he := mul_le_mul_of_nonneg_left
    (heat_inner_secant μ hQ f (mul_pos hv ht) (mul_pos hv hh) ρ u) hv.le
  have htime : heatSobolev μ hQ (v*t+v*h) (add_pos (mul_pos hv ht) (mul_pos hv hh)) f =
      heatSobolev μ hQ (v*(t+h)) (mul_pos hv (add_pos ht hh)) f := by
    congr 1; ring
  rw [htime] at he
  convert he using 1 <;> first | rfl | field_simp [ne_of_gt hv]

theorem variable_heat_cutoff_dual_secant {K : ℝ} {n : ℕ} (hcd : FullCD μ K n)
    (f g : Lp ℝ 2 μ) (hf : 0 ≤ f) (hg : 0 ≤ g) (α β : ℝ) (hα : 0 < α) (hβ : 0 < β)
    {t h : ℝ} (ht : 0 < t) (hh : 0 < h)
    [IsProbabilityMeasure (heatMeasure μ hQ (α*t) f)] [IsProbabilityMeasure (heatMeasure μ hQ (β*t) g)]
    (hmf : FiniteSecondMoment (heatMeasure μ hQ (α*t) f))
    (hmg : FiniteSecondMoment (heatMeasure μ hQ (β*t) g))
    (ρ σ : SobolevSpace μ hQ) (η ζ : Measure X)
    (hρ : ∀ᵐ x ∂μ, 0 ≤ SobolevSpace.toLp μ hQ ρ x)
    (hσ : ∀ᵐ x ∂μ, 0 ≤ SobolevSpace.toLp μ hQ σ x)
    (hη : η = μ.withDensity (fun x => ENNReal.ofReal (SobolevSpace.toLp μ hQ ρ x)))
    (hζ : ζ = μ.withDensity (fun x => ENNReal.ofReal (SobolevSpace.toLp μ hQ σ x)))
    {p : X} {R A : ℝ} {L : ℝ≥0} (d : CompactSobolevDual μ hQ η ζ p R A L)
    {E : ℝ} (hE : E ≤ α*energyForm μ hQ d.u ρ+β*energyForm μ hQ d.v σ) :
    ((wassersteinSq η ζ).toReal-(wassersteinSq (heatMeasure μ hQ (α*t) f) (heatMeasure μ hQ (β*t) g)).toReal)/(2*h) ≤
      -E+‖d.u‖*(α^2*(2*(1+1/(α*t/2)))^2*‖f‖*h)+‖d.v‖*(β^2*(2*(1+1/(β*t/2)))^2*‖g‖*h)+
      ‖d.u‖*(h⁻¹+2*α)*‖ρ-heatSobolev μ hQ (α*(t+h)) (mul_pos hα (add_pos ht hh)) f‖+
      ‖d.v‖*(h⁻¹+2*β)*‖σ-heatSobolev μ hQ (β*(t+h)) (mul_pos hβ (add_pos ht hh)) g‖ := by
  have hw := hcd.compact_dual_le μ (heatMeasure μ hQ (α*t) f) (heatMeasure μ hQ (β*t) g)
    (withDensity_absolutelyContinuous _ _) (withDensity_absolutelyContinuous _ _) hmf hmg
    d.lipφ.continuous d.lipψ.continuous d.compactφ d.compactψ d.admissible
  rw [integral_heatMeasure μ hQ f hf (α*t) d.φ,integral_heatMeasure μ hQ g hg (β*t) d.ψ] at hw
  have hfi : (∫x, d.φ x*heatAt μ hQ (α*t) f x ∂μ) = inner ℝ (heatAt μ hQ (α*t) f) (SobolevSpace.toLp μ hQ d.u) := by
    rw [L2.inner_def]
    exact integral_congr_ae (d.repu.mono fun x hx => by simp only [hx,Real.inner_apply,mul_comm])
  have hgi : (∫x, d.ψ x*heatAt μ hQ (β*t) g x ∂μ) = inner ℝ (heatAt μ hQ (β*t) g) (SobolevSpace.toLp μ hQ d.v) := by
    rw [L2.inner_def]
    exact integral_congr_ae (d.repv.mono fun x hx => by simp only [hx,Real.inner_apply,mul_comm])
  rw [hfi,hgi] at hw
  have hd := d.dual
  rw [compactDual_integral_density μ hQ ρ d.u η hρ hη d.repu,
    compactDual_integral_density μ hQ σ d.v ζ hσ hζ d.repv] at hd
  have hbase : ((wassersteinSq η ζ).toReal-(wassersteinSq (heatMeasure μ hQ (α*t) f) (heatMeasure μ hQ (β*t) g)).toReal)/2 ≤
      inner ℝ (SobolevSpace.toLp μ hQ ρ-heatAt μ hQ (α*t) f) (SobolevSpace.toLp μ hQ d.u)+
      inner ℝ (SobolevSpace.toLp μ hQ σ-heatAt μ hQ (β*t) g) (SobolevSpace.toLp μ hQ d.v) := by
    rw [inner_sub_left,inner_sub_left]; linarith only [hw,hd]
  have hhbase := mul_le_mul_of_nonneg_left hbase (inv_nonneg.mpr hh.le)
  have h0 := heat_inner_scaled_secant μ hQ f α hα ht hh ρ d.u
  have h1 := heat_inner_scaled_secant μ hQ g β hβ ht hh σ d.v
  calc
    _ = h⁻¹*(((wassersteinSq η ζ).toReal-(wassersteinSq (heatMeasure μ hQ (α*t) f) (heatMeasure μ hQ (β*t) g)).toReal)/2) := by ring
    _ ≤ _ := by nlinarith only [hhbase,h0,h1,hE]

end

 

 

open Set Filter MeasureTheory Metric
open scoped Topology NNReal ENNReal
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] (μ : Measure X) [IsFiniteMeasureOnCompacts μ]
  (hQ : QuadraticCheegerEnergy μ)

theorem SobolevSpace.dimensionalDual_norm_le (p : X) {A B : ℝ}
    (hA : 0 ≤ A) (_hB : 0 ≤ B)
    (hvol : ∀ r : ℝ, 1 ≤ r → μ.real (closedBall p (2*r)) ≤ A*Real.exp (B*r))
    {R : ℝ} (hR : 1 ≤ R) (u : SobolevSpace μ hQ) {φ : X → ℝ}
    (hφ : LipschitzWith ⟨5*(2*(max (2*(max (2*R) 0+1)) 0+1)),by positivity⟩ φ)
    (hb : ∀ x, |φ x| ≤ 10*(2*(max (2*(max (2*R) 0+1)) 0+1))^2)
    (hs : tsupport φ ⊆ closedBall p (16*(2*(max (2*(max (2*R) 0+1)) 0+1))))
    (hu : φ =ᵐ[μ] SobolevSpace.toLp μ hQ u) :
    ‖u‖ ≤ 10000*(A+1)*Real.exp ((64*B+2)*R) := by
  have hR0 : 0 ≤ R := by linarith
  have hr : max (2*R) 0 = 2*R := max_eq_left (by positivity)
  have hr' : max (2*(max (2*R) 0+1)) 0 = 2*(2*R+1) := by
    rw [hr,max_eq_left (by positivity)]
  have hrad : 2*(max (2*(max (2*R) 0+1)) 0+1) ≤ 14*R := by rw [hr']; linarith
  have hrad0 : 0 ≤ 2*(max (2*(max (2*R) 0+1)) 0+1) := by positivity
  have hex : R ≤ Real.exp R := by linarith [Real.add_one_le_exp R]
  have he2 : R^2 ≤ Real.exp (2*R) := by
    calc
      _ ≤ (Real.exp R)^2 := (sq_le_sq₀ hR0 (Real.exp_pos R).le).mpr hex
      _ = _ := by rw [←Real.exp_nat_mul]; congr 1
  have hb' : ∀ x, |φ x| ≤ 2048*Real.exp (2*R) := by
    intro x
    apply (hb x).trans
    have hsum := (sq_le_sq₀ hrad0 (by positivity : 0 ≤ 14*R)).mpr hrad
    nlinarith [Real.exp_pos (2*R)]
  have hL : 5*(2*(max (2*(max (2*R) 0+1)) 0+1)) ≤ 128*Real.exp (2*R) := by
    have hRe : R ≤ Real.exp (2*R) := hex.trans (Real.exp_le_exp.mpr (by linarith))
    nlinarith [Real.exp_pos (2*R)]
  let L : ℝ≥0 := ⟨128*Real.exp (2*R),by positivity⟩
  have hφ' : LipschitzWith L φ := hφ.weaken hL
  have hs' : tsupport φ ⊆ closedBall p (256*R) := hs.trans (closedBall_subset_closedBall (by linarith))
  have hv := hvol (128*R) (by linarith)
  rw [show 2*(128*R) = 256*R by ring] at hv
  have hn := SobolevSpace.norm_le_of_common_support μ hQ p (256*R) (2048*Real.exp (2*R)) L u hφ' hb' hs' hu
  apply hn.trans
  apply (Real.sqrt_le_iff).mpr
  refine ⟨by positivity,?_⟩
  have hA' : A ≤ (A+1)^2 := by nlinarith [sq_nonneg A]
  have hc : (2048*Real.exp (2*R))^2+(L:ℝ)^2 ≤ 10000^2*Real.exp (4*R) := by
    change (2048*Real.exp (2*R))^2+(128*Real.exp (2*R))^2 ≤ _
    have he : (Real.exp (2*R))^2 = Real.exp (4*R) := by rw [←Real.exp_nat_mul]; congr 1; ring
    simp only [mul_pow]
    rw [he]
    nlinarith [Real.exp_pos (4*R)]
  calc
    _ ≤ (10000^2*Real.exp (4*R))*(A*Real.exp (B*(128*R))) :=
      mul_le_mul hc hv ENNReal.toReal_nonneg (by positivity)
    _ ≤ (10000^2*Real.exp (4*R))*((A+1)^2*Real.exp (B*(128*R))) := by gcongr
    _ = (10000*(A+1)*Real.exp ((64*B+2)*R))^2 := by
      rw [mul_pow,mul_pow,←Real.exp_nat_mul]
      have he : 2*((64*B+2)*R) = 4*R+B*(128*R) := by ring
      norm_num only [Nat.cast_ofNat]
      rw [he,Real.exp_add]
      ring


end RegularPointCoordinates

end OAI
