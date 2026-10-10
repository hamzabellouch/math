import Mathlib
import OAI.Analysis.RCDHeat.BidirectionalPotential
import OAI.Analysis.RCDHeat.RestrictedDensity

namespace OAI

/-! Cheeger energy, curvature-dimension transport and heat-flow estimates: DimensionalH1, DimensionalHeatSecant, WeightedLogCosh, WeightedMidpointGrid. -/



namespace RegularPointCoordinates

section

 

open Set Filter MeasureTheory Metric TopologicalSpace
open scoped Topology NNReal ENNReal
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]

theorem NoncollapsedRCD.dimensional_H1_dual
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
    (N : ℝ) (hN : (n:ℝ) ≤ N) :
    ∃ d : CompactSobolevDual (hausdorff n X) hX.quadratic ν₀ ν₁
      p (16*(2*(max (2*(max R 0+1)) 0+1)))
      (10*(2*(max (2*(max R 0+1)) 0+1))^2) ⟨5*(2*(max (2*(max R 0+1)) 0+1)),by positivity⟩,
      K*(wassersteinSq ν₀ ν₁).toReal+
        (boltzmannEntropy (hausdorff n X) ν₁-boltzmannEntropy (hausdorff n X) ν₀)^2/N ≤
        energyForm (hausdorff n X) hX.quadratic d.u ρ+
          energyForm (hausdorff n X) hX.quadratic d.v ρ₁ := by
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
  have hcore (i : ℕ) := hX.dimensional_H1_square_dual K n hn ν₁ (νs i) hD
    h1D (hDs i) p hB (hs1.mono fun x hx => hx.trans hRB) (hSs i) ρ₁ (qs i)
    M₁ hρ₁ (hρ₁S.mono fun x hx hne => (hx hne).trans hRB) hρ₁M hν₁
    (hLip i).choose_spec (fun x => (hb i x).1)
    ((hLip i).choose_spec.continuous.integrable_of_hasCompactSupport (hsc i))
    (hrep i) (hνs i) N hN
  choose dsr henergyR using hcore
  let ds := fun i => (dsr i).flip
  have henergy (i : ℕ) : K*(wassersteinSq (νs i) ν₁).toReal+
      (boltzmannEntropy μ ν₁-boltzmannEntropy μ (νs i))^2/N ≤
      energyForm μ hX.quadratic (ds i).u (qs i)+energyForm μ hX.quadratic (ds i).v ρ₁ := by
    have he := henergyR i
    rw [wassersteinSq_symm ν₁ (νs i),sub_sq_comm] at he
    simpa only [ds,CompactSobolevDual.flip,add_comm] using he
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
  exact hX.dimensional_dual_limit K n hn ν₀ ν₁ νs hD h0D h1D hDs p hB
    (hs0.mono fun x hx => hx.trans hRB) (hs1.mono fun x hx => hx.trans hRB) hSs
    (fun i => (hLip i).choose_spec.continuous.measurable.pow_const 2)
    (M := (2*M:ℝ)) (fun i x => ⟨sq_nonneg _,(hb i x).2⟩) hSqs
    ρ ρ₁ qs hq (hρ.mono fun x hx => hx.1) hpt (fun i => rfl) hν hEL ds N henergy

end

 
section

 

open Set Filter MeasureTheory Metric TopologicalSpace
open scoped Topology NNReal ENNReal
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] [SeparableSpace X] (μ : Measure X) [IsLocallyFiniteMeasure μ]
  (hQ : QuadraticCheegerEnergy μ)

theorem heat_inner_secant (f : Lp ℝ 2 μ) {t h : ℝ} (ht : 0 < t) (hh : 0 < h)
    (ρ u : SobolevSpace μ hQ) :
    h⁻¹*inner ℝ (SobolevSpace.toLp μ hQ ρ-heatAt μ hQ t f) (SobolevSpace.toLp μ hQ u) ≤
      -energyForm μ hQ u ρ+‖u‖*((2*(1+1/(t/2)))^2*‖f‖*h)+
      ‖u‖*(h⁻¹+2)*‖ρ-heatSobolev μ hQ (t+h) (add_pos ht hh) f‖ := by
  let q := heatSobolev μ hQ (t+h) (add_pos ht hh) f
  let v := h⁻¹ • (heatAt μ hQ (t+h) f-heatAt μ hQ t f)
  let A := heatGeneratorAt μ hQ (t+h) f
  have hc := real_inner_le_norm (v+A) (SobolevSpace.toLp μ hQ u)
  have hc' : inner ℝ v (SobolevSpace.toLp μ hQ u)+energyForm μ hQ u q ≤
      ((2*(1+1/(t/2)))^2*‖f‖*h)*‖u‖ := by
    have he : energyForm μ hQ u q = inner ℝ A (SobolevSpace.toLp μ hQ u) := by
      rw [energyForm_comm,heatGenerator_form]
      simp only [A,heatGeneratorAt_of_pos μ hQ (t+h) (add_pos ht hh)]
    rw [he,←inner_add_left]
    exact hc.trans (mul_le_mul (heatEviRemainder_le μ hQ f ht hh)
      (SobolevSpace.norm_toLp_le μ hQ u) (norm_nonneg _) (by positivity))
  have hd : |inner ℝ (SobolevSpace.toLp μ hQ (ρ-q)) (SobolevSpace.toLp μ hQ u)| ≤ ‖ρ-q‖*‖u‖ :=
    (abs_real_inner_le_norm _ _).trans (mul_le_mul (SobolevSpace.norm_toLp_le μ hQ (ρ-q))
      (SobolevSpace.norm_toLp_le μ hQ u) (norm_nonneg _) (norm_nonneg _))
  have he := (le_abs_self (energyForm μ hQ u (ρ-q))).trans (energyForm_abs_le_norm μ hQ u (ρ-q))
  rw [energyForm_sub_right] at he
  have hsplit : SobolevSpace.toLp μ hQ ρ-heatAt μ hQ t f =
      (heatAt μ hQ (t+h) f-heatAt μ hQ t f)+SobolevSpace.toLp μ hQ (ρ-q) := by
    simp only [map_sub,q,heatSobolev_toLp]; abel
  rw [hsplit,inner_add_left,mul_add]
  have hd' := mul_le_mul_of_nonneg_left ((le_abs_self _).trans hd) (inv_nonneg.mpr hh.le)
  have hv : inner ℝ v (SobolevSpace.toLp μ hQ u) =
      h⁻¹*inner ℝ (heatAt μ hQ (t+h) f-heatAt μ hQ t f) (SobolevSpace.toLp μ hQ u) := by
    simp only [v,inner_smul_left,RCLike.conj_to_real]
  rw [hv] at hc'
  change _ ≤ -energyForm μ hQ u ρ+_+‖u‖*(h⁻¹+2)*‖ρ-q‖
  nlinarith only [hc',hd',he]

theorem compactDual_integral_density {X : Type*} [MetricSpace X] [MeasurableSpace X]
    [BorelSpace X] [ProperSpace X] [SeparableSpace X]
    (μ : Measure X) [IsLocallyFiniteMeasure μ] (hQ : QuadraticCheegerEnergy μ)
    (ρ u : SobolevSpace μ hQ) (η : Measure X)
    (hρ : ∀ᵐ x ∂μ, 0 ≤ SobolevSpace.toLp μ hQ ρ x)
    (hη : η = μ.withDensity (fun x => ENNReal.ofReal (SobolevSpace.toLp μ hQ ρ x)))
    {φ : X → ℝ} (hu : φ =ᵐ[μ] SobolevSpace.toLp μ hQ u) :
    (∫x, φ x ∂η) = inner ℝ (SobolevSpace.toLp μ hQ ρ) (SobolevSpace.toLp μ hQ u) := by
  rw [hη,integral_withDensity_eq_integral_toReal_smul₀
    (Lp.aestronglyMeasurable (SobolevSpace.toLp μ hQ ρ)).aemeasurable.ennreal_ofReal
    (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top),L2.inner_def]
  apply integral_congr_ae
  filter_upwards [hu,hρ] using fun x hx hn => by
    simp only [hx,ENNReal.toReal_ofReal hn,smul_eq_mul,Real.inner_apply]

theorem dimensional_heat_cutoff_dual_secant {K : ℝ} {n : ℕ} (hcd : FullCD μ K n)
    (f g : Lp ℝ 2 μ) (hf : 0 ≤ f) (hg : 0 ≤ g)
    {t h : ℝ} (ht : 0 < t) (hh : 0 < h)
    [IsProbabilityMeasure (heatMeasure μ hQ t f)] [IsProbabilityMeasure (heatMeasure μ hQ t g)]
    (hmf : FiniteSecondMoment (heatMeasure μ hQ t f))
    (hmg : FiniteSecondMoment (heatMeasure μ hQ t g))
    (ρ σ : SobolevSpace μ hQ) (η ζ : Measure X)
    (hρ : ∀ᵐ x ∂μ, 0 ≤ SobolevSpace.toLp μ hQ ρ x)
    (hσ : ∀ᵐ x ∂μ, 0 ≤ SobolevSpace.toLp μ hQ σ x)
    (hη : η = μ.withDensity (fun x => ENNReal.ofReal (SobolevSpace.toLp μ hQ ρ x)))
    (hζ : ζ = μ.withDensity (fun x => ENNReal.ofReal (SobolevSpace.toLp μ hQ σ x)))
    {p : X} {R A : ℝ} {L : ℝ≥0} (d : CompactSobolevDual μ hQ η ζ p R A L)
    {E : ℝ} (hE : E ≤ energyForm μ hQ d.u ρ+energyForm μ hQ d.v σ) :
    ((wassersteinSq η ζ).toReal-(wassersteinSq (heatMeasure μ hQ t f) (heatMeasure μ hQ t g)).toReal)/(2*h) ≤
      -E+‖d.u‖*((2*(1+1/(t/2)))^2*‖f‖*h)+‖d.v‖*((2*(1+1/(t/2)))^2*‖g‖*h)+
      ‖d.u‖*(h⁻¹+2)*‖ρ-heatSobolev μ hQ (t+h) (add_pos ht hh) f‖+
      ‖d.v‖*(h⁻¹+2)*‖σ-heatSobolev μ hQ (t+h) (add_pos ht hh) g‖ := by
  have hw := hcd.compact_dual_le μ (heatMeasure μ hQ t f) (heatMeasure μ hQ t g)
    (withDensity_absolutelyContinuous _ _) (withDensity_absolutelyContinuous _ _) hmf hmg
    d.lipφ.continuous d.lipψ.continuous d.compactφ d.compactψ d.admissible
  rw [integral_heatMeasure μ hQ f hf t d.φ,integral_heatMeasure μ hQ g hg t d.ψ] at hw
  have hfi : (∫x, d.φ x*heatAt μ hQ t f x ∂μ) = inner ℝ (heatAt μ hQ t f) (SobolevSpace.toLp μ hQ d.u) := by
    rw [L2.inner_def]
    exact integral_congr_ae (d.repu.mono fun x hx => by simp only [hx,Real.inner_apply,mul_comm])
  have hgi : (∫x, d.ψ x*heatAt μ hQ t g x ∂μ) = inner ℝ (heatAt μ hQ t g) (SobolevSpace.toLp μ hQ d.v) := by
    rw [L2.inner_def]
    exact integral_congr_ae (d.repv.mono fun x hx => by simp only [hx,Real.inner_apply,mul_comm])
  rw [hfi,hgi] at hw
  have hd := d.dual
  rw [compactDual_integral_density μ hQ ρ d.u η hρ hη d.repu,
    compactDual_integral_density μ hQ σ d.v ζ hσ hζ d.repv] at hd
  have hbase : ((wassersteinSq η ζ).toReal-(wassersteinSq (heatMeasure μ hQ t f) (heatMeasure μ hQ t g)).toReal)/2 ≤
      inner ℝ (SobolevSpace.toLp μ hQ ρ-heatAt μ hQ t f) (SobolevSpace.toLp μ hQ d.u)+
      inner ℝ (SobolevSpace.toLp μ hQ σ-heatAt μ hQ t g) (SobolevSpace.toLp μ hQ d.v) := by
    rw [inner_sub_left,inner_sub_left]; linarith only [hw,hd]
  have hhbase := mul_le_mul_of_nonneg_left hbase (inv_nonneg.mpr hh.le)
  have h0 := heat_inner_secant μ hQ f ht hh ρ d.u
  have h1 := heat_inner_secant μ hQ g ht hh σ d.v
  calc
    _ = h⁻¹*(((wassersteinSq η ζ).toReal-(wassersteinSq (heatMeasure μ hQ t f) (heatMeasure μ hQ t g)).toReal)/2) := by ring
    _ ≤ _ := by nlinarith only [hhbase,h0,h1,hE]

end

 
section

 

open Set

lemma log_cosh_sqrt_lower (x : ℝ) :
    Real.sqrt (1+x^2)-1 ≤ Real.log (Real.cosh x) := by
  have hp (y : ℝ) : 0 < 1+y^2 := by positivity
  let F : ℝ → ℝ := fun y => Real.log (Real.cosh y)-Real.sqrt (1+y^2)
  have hd (y : ℝ) : HasDerivAt F (Real.sinh y/Real.cosh y-y/Real.sqrt (1+y^2)) y := by
    have hs := ((hasDerivAt_pow 2 y).const_add 1).sqrt (hp y).ne'
    have he : (2*y^(2-1))/(2*Real.sqrt (1+y^2)) = y/Real.sqrt (1+y^2) := by ring
    simp only [Nat.cast_ofNat] at hs
    rw [he] at hs
    exact (hasDerivAt_log_cosh y).sub hs
  have hd0 (y : ℝ) (hy : 0 ≤ y) : 0 ≤ Real.sinh y/Real.cosh y-y/Real.sqrt (1+y^2) := by
    have hs : y ≤ Real.sinh y := Real.self_le_sinh_iff.mpr hy
    have hs0 : 0 ≤ Real.sinh y := hy.trans hs
    have hc : (Real.cosh y)^2 = 1+(Real.sinh y)^2 := by
      nlinarith only [Real.cosh_sq_sub_sinh_sq y]
    have hsq : y^2 ≤ (Real.sinh y)^2 := pow_le_pow_left₀ hy hs 2
    have hprod : y*Real.cosh y ≤ Real.sinh y*Real.sqrt (1+y^2) := by
      apply (sq_le_sq₀ (by positivity) (by positivity)).mp
      rw [mul_pow,mul_pow,Real.sq_sqrt (hp y).le,hc]
      nlinarith only [hsq]
    exact sub_nonneg.mpr ((div_le_div_iff₀ (Real.sqrt_pos.mpr (hp y)) (Real.cosh_pos y)).mpr hprod)
  have hm : MonotoneOn F (Ici 0) := by
    apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ici 0)
      (fun y _ => (hd y).continuousAt.continuousWithinAt)
      (fun y _ => (hd y).hasDerivWithinAt)
    intro y hy
    apply hd0 y
    exact (interior_subset hy)
  have hpos (y : ℝ) (hy : 0 ≤ y) : Real.sqrt (1+y^2)-1 ≤ Real.log (Real.cosh y) := by
    have hh := hm (show (0:ℝ) ∈ Ici 0 from by simp) hy hy
    simp only [F,Real.cosh_zero,Real.log_one,zero_pow (by norm_num : (2:ℕ) ≠ 0),
      add_zero,Real.sqrt_one] at hh
    linarith
  rcases le_total 0 x with hx|hx
  · exact hpos x hx
  · have hh := hpos (-x) (neg_nonneg.mpr hx)
    simpa only [neg_sq,Real.cosh_neg] using hh

lemma weighted_log_cosh (a b x : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    -(a-b)^2 ≤ (a^2+b^2)*Real.log (Real.cosh x)+(a^2-b^2)*x := by
  have hs : 0 ≤ 1+x^2 := by positivity
  have hsq : (2*a*b-(a^2-b^2)*x)^2 ≤ ((a^2+b^2)*Real.sqrt (1+x^2))^2 := by
    rw [mul_pow,Real.sq_sqrt hs]
    nlinarith only [sq_nonneg (a^2-b^2+2*a*b*x)]
  have hroot : 2*a*b-(a^2-b^2)*x ≤ (a^2+b^2)*Real.sqrt (1+x^2) :=
    le_of_sq_le_sq hsq (by positivity)
  have hh := mul_le_mul_of_nonneg_left (log_cosh_sqrt_lower x)
    (add_nonneg (pow_nonneg ha 2) (pow_nonneg hb 2))
  nlinarith only [hroot,hh]

lemma weighted_dimensional_midpoint {N κ A B M : ℝ} (hN : 0 < N)
    (h : M ≤ (A+B)/2-κ/2-N*Real.log (Real.cosh ((A-B)/(2*N))))
    (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    κ*(a^2+b^2)/2-N*(a-b)^2 ≤ a^2*(A-M)+b^2*(B-M) := by
  have hw := mul_le_mul_of_nonneg_left (weighted_log_cosh a b ((A-B)/(2*N)) ha hb) hN.le
  have hm := mul_le_mul_of_nonneg_left h (show 0 ≤ a^2+b^2 by positivity)
  have he : N*((a^2-b^2)*((A-B)/(2*N))) = (a^2-b^2)*(A-B)/2 := by
    field_simp
  rw [mul_add,he] at hw
  nlinarith only [hw,hm]

end

 

 

open Set Filter
open scoped BigOperators Topology

lemma sum_weighted_first_difference (f w : ℕ → ℝ) (m : ℕ) :
    (∑ i ∈ Finset.range m, (w i^2*(f i-f (i+1))+w (i+1)^2*(f (i+2)-f (i+1)))) =
      w m^2*(f (m+1)-f m)-w 0^2*(f 1-f 0) := by
  induction m with
  | zero => simp
  | succ m hm =>
    rw [Finset.sum_range_succ,hm]
    ring

lemma sum_affine_square_trapezoid (a d : ℝ) (m : ℕ) :
    (∑ i ∈ Finset.range m, ((a+d*(i:ℝ))^2+(a+d*((i:ℝ)+1))^2)/2) =
      (m:ℝ)*a^2+a*d*(m:ℝ)^2+d^2*(m:ℝ)*(2*(m:ℝ)^2+1)/6 := by
  induction m with
  | zero => simp
  | succ m hm =>
    rw [Finset.sum_range_succ,hm]
    push_cast
    ring

lemma weighted_dimensional_discrete (f w : ℕ → ℝ) {N κ : ℝ} (hN : 0 < N)
    (m : ℕ) (hw : ∀ i ≤ m, 0 ≤ w i)
    (hmid : ∀ i < m, f (i+1) ≤ (f i+f (i+2))/2-κ/2-
      N*Real.log (Real.cosh ((f i-f (i+2))/(2*N)))) :
    κ*(∑ i ∈ Finset.range m, (w i^2+w (i+1)^2)/2)-
      N*(∑ i ∈ Finset.range m, (w i-w (i+1))^2) ≤
      w m^2*(f (m+1)-f m)-w 0^2*(f 1-f 0) := by
  have hh := Finset.sum_le_sum (s := Finset.range m) (fun i hi =>
    weighted_dimensional_midpoint hN (hmid i (Finset.mem_range.mp hi)) (w i) (w (i+1))
      (hw i (by have := Finset.mem_range.mp hi; omega))
      (hw (i+1) (by have := Finset.mem_range.mp hi; omega)))
  rw [Finset.sum_sub_distrib] at hh
  have he : (∑ i ∈ Finset.range m, κ*(w i^2+w (i+1)^2)/2) =
      κ*(∑ i ∈ Finset.range m, (w i^2+w (i+1)^2)/2) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [he,←Finset.mul_sum,sum_weighted_first_difference] at hh
  exact hh

lemma weighted_dimensional_midpoint_grid (E : ℝ → ℝ) {N κ : ℝ} (hN : 0 < N)
    (hmid : ∀ x ∈ Icc (0:ℝ) 1, ∀ y ∈ Icc (0:ℝ) 1,
      E ((x+y)/2) ≤ (E x+E y)/2-κ*(x-y)^2/8-
        N*Real.log (Real.cosh ((E x-E y)/(2*N))))
    (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (m : ℕ) (hm : 0 < m) :
    κ/((m:ℝ)+1)*((m:ℝ)*(a^2+a*b+b^2)/3+(a-b)^2/(6*(m:ℝ)))-
      N*(a-b)^2*((m:ℝ)+1)/(m:ℝ) ≤
      (a^2*(E 0-E (1/((m:ℝ)+1)))+
        b^2*(E 1-E (1-1/((m:ℝ)+1))))*((m:ℝ)+1) := by
  have hmR : 0 < (m:ℝ) := by exact_mod_cast hm
  have hD : 0 < (m:ℝ)+1 := by positivity
  let f : ℕ → ℝ := fun i => E ((i:ℝ)/((m:ℝ)+1))
  let w : ℕ → ℝ := fun i => a+(b-a)*(i:ℝ)/(m:ℝ)
  have hw : ∀ i ≤ m, 0 ≤ w i := by
    intro i hi
    have hiR : (i:ℝ) ≤ (m:ℝ) := by exact_mod_cast hi
    have h0 : 0 ≤ (i:ℝ)/(m:ℝ) := by positivity
    have h1 : (i:ℝ)/(m:ℝ) ≤ 1 := (div_le_one hmR).mpr hiR
    have he : w i = a*(1-(i:ℝ)/(m:ℝ))+b*((i:ℝ)/(m:ℝ)) := by dsimp [w]; ring
    rw [he]
    positivity
  have hc : ∀ i < m, f (i+1) ≤ (f i+f (i+2))/2-(κ/((m:ℝ)+1)^2)/2-
      N*Real.log (Real.cosh ((f i-f (i+2))/(2*N))) := by
    intro i hi
    have hiR : (i:ℝ)+1 ≤ (m:ℝ) := by exact_mod_cast hi
    have h0 : (i:ℝ)/((m:ℝ)+1) ∈ Icc (0:ℝ) 1 :=
      ⟨by positivity,(div_le_one hD).mpr (by linarith)⟩
    have h2 : ((i:ℝ)+2)/((m:ℝ)+1) ∈ Icc (0:ℝ) 1 :=
      ⟨by positivity,(div_le_one hD).mpr (by linarith)⟩
    have hh := hmid _ h0 _ h2
    have he : ((i:ℝ)/((m:ℝ)+1)+((i:ℝ)+2)/((m:ℝ)+1))/2 =
        ((i:ℝ)+1)/((m:ℝ)+1) := by ring
    have hk : κ*((i:ℝ)/((m:ℝ)+1)-((i:ℝ)+2)/((m:ℝ)+1))^2/8 =
        (κ/((m:ℝ)+1)^2)/2 := by field_simp; ring
    rw [he,hk] at hh
    simpa only [f,Nat.cast_add,Nat.cast_one,Nat.cast_ofNat] using hh
  have hh := weighted_dimensional_discrete f w hN m hw hc
  have hw0 : w 0 = a := by simp [w]
  have hwm : w m = b := by dsimp only [w]; field_simp; ring
  have hf0 : f 0 = E 0 := by simp [f]
  have hf1 : f 1 = E (1/((m:ℝ)+1)) := by simp [f]
  have hfm : f m = E (1-1/((m:ℝ)+1)) := by
    dsimp only [f]
    congr 1
    field_simp
    ring
  have hfm1 : f (m+1) = E 1 := by simp [f,hD.ne']
  have hpen : (∑ i ∈ Finset.range m, (w i-w (i+1))^2) = (a-b)^2/(m:ℝ) := by
    have he (i : ℕ) : (w i-w (i+1))^2 = (a-b)^2/(m:ℝ)^2 := by
      dsimp only [w]
      push_cast
      ring
    simp_rw [he]
    rw [Finset.sum_const,Finset.card_range,nsmul_eq_mul]
    field_simp
  have hweight : (∑ i ∈ Finset.range m, (w i^2+w (i+1)^2)/2) =
      (m:ℝ)*(a^2+a*b+b^2)/3+(a-b)^2/(6*(m:ℝ)) := by
    have hh := sum_affine_square_trapezoid a ((b-a)/(m:ℝ)) m
    have he (i : ℕ) : (w i^2+w (i+1)^2)/2 =
        ((a+((b-a)/(m:ℝ))*(i:ℝ))^2+(a+((b-a)/(m:ℝ))*((i:ℝ)+1))^2)/2 := by
      dsimp only [w]
      push_cast
      ring
    simp_rw [he]
    rw [hh]
    field_simp
    ring
  rw [hw0,hwm,hf0,hf1,hfm,hfm1,hpen,hweight] at hh
  have hh' := mul_le_mul_of_nonneg_right hh hD.le
  convert hh' using 1 <;> first | rfl | (field_simp <;> ring)


end RegularPointCoordinates

end OAI
