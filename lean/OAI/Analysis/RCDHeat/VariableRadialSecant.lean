import Mathlib
import OAI.Analysis.RCDHeat.WeightedDimensionalH1Square

namespace OAI

/-! Cheeger energy, curvature-dimension transport and heat-flow estimates: VariableRadialSecant, DimensionalPairCutoff, VariableHeatCutoffCost, VariableHeatSlope. -/



namespace RegularPointCoordinates

section

 

open Set Filter MeasureTheory Metric TopologicalSpace
open scoped Topology NNReal ENNReal
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] [SeparableSpace X]

private theorem variable_secant_algebra {α β H D U V A B F G : ℝ}
    (hα : 0 ≤ α) (hβ : 0 ≤ β) (hH : 0 ≤ H) (hD : 0 ≤ D)
    (hU : U ≤ D) (hV : V ≤ D) (_hU0 : 0 ≤ U) (_hV0 : 0 ≤ V)
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hF : 0 ≤ F) (hG : 0 ≤ G) :
    U*A+V*B+U*(H+2*α)*F+V*(H+2*β)*G ≤
      D*(1+α+β)*(A+B+(H+2)*(F+G)) := by
  let M := 1+α+β
  have hM : 1 ≤ M := by dsimp [M]; linarith
  have hD' : D ≤ D*M := le_mul_of_one_le_right hD hM
  have hα' : H+2*α ≤ M*(H+2) := by
    dsimp [M]; nlinarith [mul_nonneg hα hH,mul_nonneg hβ hH]
  have hβ' : H+2*β ≤ M*(H+2) := by
    dsimp [M]; nlinarith [mul_nonneg hα hH,mul_nonneg hβ hH]
  have h1 := mul_le_mul_of_nonneg_right (hU.trans hD') hA
  have h2 := mul_le_mul_of_nonneg_right (hV.trans hD') hB
  have h3 := mul_le_mul_of_nonneg_right (mul_le_mul hU hα' (by positivity) hD) hF
  have h4 := mul_le_mul_of_nonneg_right (mul_le_mul hV hβ' (by positivity) hD) hG
  convert add_le_add (add_le_add (add_le_add h1 h2) h3) h4 using 1
  all_goals try dsimp only [M]
  all_goals first | rfl | ring

theorem NoncollapsedRCD.variable_cutoff_heat_secant
    (K : ℝ) (n : ℕ) [IsLocallyFiniteMeasure (hausdorff n X)] (hn : 2 ≤ n)
    (hX : NoncollapsedRCD K n X) (p : X) {A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hvol : ∀ R : ℝ, 1 ≤ R → (hausdorff n X).real (closedBall p (2*R)) ≤ A*Real.exp (B*R))
    (f g : Lp ℝ 2 (hausdorff n X)) (C : ℝ≥0) (hf0 : 0 ≤ f) (hg0 : 0 ≤ g)
    (hfC : ∀ᵐ x ∂hausdorff n X, f x ≤ C) (hgC : ∀ᵐ x ∂hausdorff n X, g x ≤ C)
    (hfi : Integrable f (hausdorff n X)) (hgi : Integrable g (hausdorff n X))
    (hfm : ∫x, f x ∂hausdorff n X = 1) (hgm : ∫x, g x ∂hausdorff n X = 1)
    {r r' : ℝ} (hfs : ∀ᵐ x ∂hausdorff n X, f x ≠ 0 → dist p x ≤ r)
    (hgs : ∀ᵐ x ∂hausdorff n X, g x ≠ 0 → dist p x ≤ r')
    (a b : ℝ) (ha : 0 < a) (hb : 0 < b)
    {R t h : ℝ} (hR : 1 ≤ R) (ht : 0 < t) (hh : 0 < h)
    (hmf : (1:ℝ)/2 ≤ ∫x, radialCutoff p R x*heatAt (hausdorff n X) hX.quadratic (a^2*(t+h)) f x ∂hausdorff n X)
    (hmg : (1:ℝ)/2 ≤ ∫x, radialCutoff p R x*heatAt (hausdorff n X) hX.quadratic (b^2*(t+h)) g x ∂hausdorff n X)
    (N : ℝ) (hN : (n:ℝ) ≤ N) :
    let μ := hausdorff n X
    let η := radialHeatMeasure μ hX.quadratic p R (a^2*(t+h)) f
    let ζ := radialHeatMeasure μ hX.quadratic p R (b^2*(t+h)) g
    let ρ := radialHeatSobolev μ hX.quadratic p (zero_lt_one.trans_le hR) (mul_pos (sq_pos_of_pos ha) (add_pos ht hh)) f C
    let σ := radialHeatSobolev μ hX.quadratic p (zero_lt_one.trans_le hR) (mul_pos (sq_pos_of_pos hb) (add_pos ht hh)) g C
    ((wassersteinSq η ζ).toReal-(wassersteinSq (heatMeasure μ hX.quadratic (a^2*t) f) (heatMeasure μ hX.quadratic (b^2*t) g)).toReal)/(2*h) ≤
      N*(a-b)^2-K*(wassersteinSq η ζ).toReal*(a^2+a*b+b^2)/3+
      (10000*(A+1)*(1+a^2+b^2)*Real.exp ((64*B+2)*R)) *
        (((a^4*(2*(1+1/(a^2*t/2)))^2*‖f‖+b^4*(2*(1+1/(b^2*t/2)))^2*‖g‖)*h)+(h⁻¹+2)*
          (‖ρ-heatSobolev μ hX.quadratic (a^2*(t+h)) (mul_pos (sq_pos_of_pos ha) (add_pos ht hh)) f‖+
            ‖σ-heatSobolev μ hX.quadratic (b^2*(t+h)) (mul_pos (sq_pos_of_pos hb) (add_pos ht hh)) g‖)) := by
  let μ := hausdorff n X
  let η := radialHeatMeasure μ hX.quadratic p R (a^2*(t+h)) f
  let ζ := radialHeatMeasure μ hX.quadratic p R (b^2*(t+h)) g
  let ρ := radialHeatSobolev μ hX.quadratic p (zero_lt_one.trans_le hR) (mul_pos (sq_pos_of_pos ha) (add_pos ht hh)) f C
  let σ := radialHeatSobolev μ hX.quadratic p (zero_lt_one.trans_le hR) (mul_pos (sq_pos_of_pos hb) (add_pos ht hh)) g C
  have hdf := radialHeatMeasure_data μ hX.quadratic p hA hB hvol f C hf0 hfC hfi hfm
    (zero_lt_one.trans_le hR) (mul_pos (sq_pos_of_pos ha) (add_pos ht hh)) hmf
  have hdg := radialHeatMeasure_data μ hX.quadratic p hA hB hvol g C hg0 hgC hgi hgm
    (zero_lt_one.trans_le hR) (mul_pos (sq_pos_of_pos hb) (add_pos ht hh)) hmg
  let : IsProbabilityMeasure η := hdf.1
  let : IsProbabilityMeasure ζ := hdg.1
  have hvf := radialHeatSobolev_data μ hX.quadratic p hA hB hvol f C hf0 hfC hfi hfm
    (zero_lt_one.trans_le hR) (mul_pos (sq_pos_of_pos ha) (add_pos ht hh)) hmf
  have hvg := radialHeatSobolev_data μ hX.quadratic p hA hB hvol g C hg0 hgC hgi hgm
    (zero_lt_one.trans_le hR) (mul_pos (sq_pos_of_pos hb) (add_pos ht hh)) hmg
  have hη := radialHeatSobolev_measure μ hX.quadratic p (zero_lt_one.trans_le hR) (mul_pos (sq_pos_of_pos ha) (add_pos ht hh)) f C hf0 hfC
  have hζ := radialHeatSobolev_measure μ hX.quadratic p (zero_lt_one.trans_le hR) (mul_pos (sq_pos_of_pos hb) (add_pos ht hh)) g C hg0 hgC
  obtain ⟨d,hE⟩ := hX.weighted_dimensional_H1_dual K n hn η ζ ENNReal.ofReal_ne_top hdf.2.1 hdg.2.1
    p (by positivity : 0 ≤ 2*R) hdf.2.2 hdg.2.2 ρ σ
    (2*C) hvf.1 hvf.2.1 hvf.2.2.2 hη (2*C) hvg.1 hvg.2.1 hvg.2.2.2 hζ N hN a b ha.le hb.le
  have hfm2 := heatAt_finiteSecondMoment μ hX.quadratic p hA hB hvol f hf0 hfs (mul_pos (sq_pos_of_pos ha) ht).le
  have hgm2 := heatAt_finiteSecondMoment μ hX.quadratic p hA hB hvol g hg0 hgs (mul_pos (sq_pos_of_pos hb) ht).le
  let : IsProbabilityMeasure (heatMeasure μ hX.quadratic (a^2*t) f) := by
    apply realDensity_probability μ (heatAt_integrable μ hX.quadratic (a^2*t) f hfi)
      ((Lp.coeFn_nonneg _).mpr (heatAt_nonneg μ hX.quadratic (a^2*t) f hf0))
    exact (heatAt_integral_eq_of_exponential_volume μ hX.quadratic p hA hB hvol f hf0 hfi (mul_pos (sq_pos_of_pos ha) ht).le).trans hfm
  let : IsProbabilityMeasure (heatMeasure μ hX.quadratic (b^2*t) g) := by
    apply realDensity_probability μ (heatAt_integrable μ hX.quadratic (b^2*t) g hgi)
      ((Lp.coeFn_nonneg _).mpr (heatAt_nonneg μ hX.quadratic (b^2*t) g hg0))
    exact (heatAt_integral_eq_of_exponential_volume μ hX.quadratic p hA hB hvol g hg0 hgi (mul_pos (sq_pos_of_pos hb) ht).le).trans hgm
  have hs := variable_heat_cutoff_dual_secant μ hX.quadratic hX.cd f g hf0 hg0 (a^2) (b^2) (sq_pos_of_pos ha) (sq_pos_of_pos hb) ht hh
    hfm2 hgm2 ρ σ η ζ (hvf.1.mono fun _ hx => hx.1) (hvg.1.mono fun _ hx => hx.1) hη hζ d hE
  have hun := SobolevSpace.dimensionalDual_norm_le μ hX.quadratic p hA hB hvol hR
    d.u d.lipφ d.boundφ d.supportφ d.repu
  have hvn := SobolevSpace.dimensionalDual_norm_le μ hX.quadratic p hA hB hvol hR
    d.v d.lipψ d.boundψ d.supportψ d.repv
  have herr := variable_secant_algebra (sq_nonneg a) (sq_nonneg b) (inv_nonneg.mpr hh.le)
    (by positivity : 0 ≤ 10000*(A+1)*Real.exp ((64*B+2)*R)) hun hvn (norm_nonneg _) (norm_nonneg _)
    (by positivity : 0 ≤ (a^2)^2*(2*(1+1/(a^2*t/2)))^2*‖f‖*h)
    (by positivity : 0 ≤ (b^2)^2*(2*(1+1/(b^2*t/2)))^2*‖g‖*h)
    (norm_nonneg (ρ-heatSobolev μ hX.quadratic (a^2*(t+h)) (by positivity) f))
    (norm_nonneg (σ-heatSobolev μ hX.quadratic (b^2*(t+h)) (by positivity) g))
  apply hs.trans
  convert add_le_add_left herr (-(K*(wassersteinSq η ζ).toReal*(a^2+a*b+b^2)/3-N*(a-b)^2)) using 1
  all_goals try dsimp only [μ]
  all_goals first | rfl | ring

end

 
section

 

open Set Filter MeasureTheory Metric TopologicalSpace
open scoped Topology NNReal ENNReal

theorem square_difference_exponential {x y J M a R : ℝ}
    (hJ : 0 ≤ J) (_hM : 0 ≤ M) (ha : 0 ≤ a) (hR : 0 ≤ R)
    (hxy : |x-y| ≤ J*Real.exp (-a*R)) (hy : |y| ≤ M) :
    |x^2-y^2| ≤ J*(2*M+J)*Real.exp (-a*R) := by
  have hex : Real.exp (-a*R) ≤ 1 := by
    rw [←Real.exp_zero]; exact Real.exp_le_exp.mpr (by nlinarith)
  have hxy' : |x-y| ≤ J := hxy.trans (by nlinarith)
  have hab : |x+y| ≤ 2*M+J := by
    calc
      _ = |(x-y)+2*y| := by congr 1; ring
      _ ≤ |x-y|+|2*y| := abs_add_le _ _
      _ ≤ J+2*M := by rw [abs_mul,abs_of_pos (by norm_num : (0:ℝ)<2)]; linarith
      _ = _ := by ring
  calc
    _ = |x-y| * |x+y| := by rw [←abs_mul]; congr 1; ring
    _ ≤ (J*Real.exp (-a*R))*(2*M+J) :=
      mul_le_mul hxy hab (abs_nonneg _) (by positivity)
    _ = _ := by ring

theorem pair_dist_square_exponential {Y : Type*} [PseudoMetricSpace Y]
    (x x' y y' : Y) {D E L a R : ℝ}
    (hD : 0 ≤ D) (hE : 0 ≤ E) (hL : 0 ≤ L) (ha : 0 ≤ a) (hR : 0 ≤ R)
    (hx : dist x x'^2 ≤ D*Real.exp (-(2*a)*R))
    (hy : dist y y'^2 ≤ E*Real.exp (-(2*a)*R)) (hxy : dist x' y' ≤ L) :
    |dist x y^2-dist x' y'^2| ≤
      (Real.sqrt D+Real.sqrt E)*(2*L+(Real.sqrt D+Real.sqrt E))*Real.exp (-a*R) := by
  have he : Real.exp (-(2*a)*R) = (Real.exp (-a*R))^2 := by
    rw [←Real.exp_nat_mul]; congr 1; ring
  have hsx : dist x x' ≤ Real.sqrt D*Real.exp (-a*R) := by
    apply (sq_le_sq₀ dist_nonneg (by positivity)).mp
    rw [mul_pow,Real.sq_sqrt hD,←he]; exact hx
  have hsy : dist y y' ≤ Real.sqrt E*Real.exp (-a*R) := by
    apply (sq_le_sq₀ dist_nonneg (by positivity)).mp
    rw [mul_pow,Real.sq_sqrt hE,←he]; exact hy
  have hd : |dist x y-dist x' y'| ≤ dist x x'+dist y y' := by
    apply abs_le.mpr
    have h1 := dist_triangle x x' y
    have h2 := dist_triangle x' y' y
    have h3 := dist_triangle x' x y'
    have h4 := dist_triangle x y y'
    simp only [dist_comm y' y,dist_comm x' x] at h1 h2 h3 h4
    constructor <;> linarith
  apply square_difference_exponential (by positivity) hL ha hR
    (hd.trans (by nlinarith only [hsx,hsy]))
  simpa only [abs_of_nonneg dist_nonneg] using hxy

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] [SeparableSpace X]

theorem NoncollapsedRCD.radial_heat_pair_cost_exponential
    (K : ℝ) (n : ℕ) [IsLocallyFiniteMeasure (hausdorff n X)] (hn : 2 ≤ n)
    (hX : NoncollapsedRCD K n X) (p : X) {A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hvol : ∀ R : ℝ, 1 ≤ R → (hausdorff n X).real (closedBall p (2*R)) ≤ A*Real.exp (B*R))
    (f g : Lp ℝ 2 (hausdorff n X)) (C : ℝ≥0) (hf0 : 0 ≤ f) (hg0 : 0 ≤ g)
    (hfC : ∀ᵐ x ∂hausdorff n X, f x ≤ C) (hgC : ∀ᵐ x ∂hausdorff n X, g x ≤ C)
    (hfi : Integrable f (hausdorff n X)) (hgi : Integrable g (hausdorff n X))
    (hfm : ∫x, f x ∂hausdorff n X = 1) (hgm : ∫x, g x ∂hausdorff n X = 1)
    {r r' : ℝ} (hfs : ∀ᵐ x ∂hausdorff n X, f x ≠ 0 → dist p x ≤ r)
    (hgs : ∀ᵐ x ∂hausdorff n X, g x ≠ 0 → dist p x ≤ r')
    {a t T : ℝ} (ha : 0 ≤ a) (ht : 0 < t) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ s, t ≤ s → s ≤ T → ∀ R, 1 ≤ R →
      (1:ℝ)/2 ≤ ∫x, radialCutoff p R x*heatAt (hausdorff n X) hX.quadratic s f x ∂hausdorff n X →
      (1:ℝ)/2 ≤ ∫x, radialCutoff p R x*heatAt (hausdorff n X) hX.quadratic s g x ∂hausdorff n X →
      |(wassersteinSq (radialHeatMeasure (hausdorff n X) hX.quadratic p R s f)
          (radialHeatMeasure (hausdorff n X) hX.quadratic p R s g)).toReal-
        (wassersteinSq (heatMeasure (hausdorff n X) hX.quadratic s f)
          (heatMeasure (hausdorff n X) hX.quadratic s g)).toReal| ≤ D*Real.exp (-a*R) := by
  let μ := hausdorff n X
  let := ACWassersteinProbability.metric μ K n hX.cd
  let ρ := hX.heatProbability K n hn p f hf0 ⟨r,hfs⟩ hfm
  let σ := hX.heatProbability K n hn p g hg0 ⟨r',hgs⟩ hgm
  have hfabs : ∀ᵐ x ∂μ, |f x| ≤ C := by
    filter_upwards [(Lp.coeFn_nonneg _).mpr hf0,hfC] with x hl hu
    simpa only [abs_of_nonneg hl] using hu
  have hgabs : ∀ᵐ x ∂μ, |g x| ≤ C := by
    filter_upwards [(Lp.coeFn_nonneg _).mpr hg0,hgC] with x hl hu
    simpa only [abs_of_nonneg hl] using hu
  have hc : ContinuousOn (fun s => dist (ρ s) (σ s)) (Icc t T) := by
    intro s hs
    have hρ : ContinuousAt ρ s := hX.heat_probability_continuousAt K n hn p f hf0 ⟨r,hfs⟩ hfm C hfabs
      (ht.trans_le hs.1)
    have hσ : ContinuousAt σ s := hX.heat_probability_continuousAt K n hn p g hg0 ⟨r',hgs⟩ hgm C hgabs
      (ht.trans_le hs.1)
    have hd : ContinuousAt (fun q => dist (ρ q) (σ q)) s := hρ.dist hσ
    exact hd.continuousWithinAt
  obtain ⟨L,hL⟩ := isCompact_Icc.bddAbove_image hc
  obtain ⟨D,hD,hcutf⟩ := radialHeatMeasure_transport_exponential μ hX.quadratic p hA hB hvol
    f hf0 hfi hfm hfs (a := 2*a) (T := T) (by positivity)
  obtain ⟨E,hE,hcutg⟩ := radialHeatMeasure_transport_exponential μ hX.quadratic p hA hB hvol
    g hg0 hgi hgm hgs (a := 2*a) (T := T) (by positivity)
  refine ⟨(Real.sqrt D+Real.sqrt E)*(2*(max L 0)+(Real.sqrt D+Real.sqrt E)),by positivity,?_⟩
  intro s hs hT R hR hmf hmg
  have hsp : 0 < s := ht.trans_le hs
  have hdf := radialHeatMeasure_data μ hX.quadratic p hA hB hvol f C hf0 hfC hfi hfm
    (zero_lt_one.trans_le hR) hsp hmf
  have hdg := radialHeatMeasure_data μ hX.quadratic p hA hB hvol g C hg0 hgC hgi hgm
    (zero_lt_one.trans_le hR) hsp hmg
  let : IsProbabilityMeasure (radialHeatMeasure μ hX.quadratic p R s f) := hdf.1
  let : IsProbabilityMeasure (radialHeatMeasure μ hX.quadratic p R s g) := hdg.1
  let η : ACWassersteinProbability μ := ⟨radialHeatMeasure μ hX.quadratic p R s f,hdf.1,
    withDensity_absolutelyContinuous _ _,finiteSecondMoment_of_ae_dist_le _ p hdf.2.2⟩
  let ζ : ACWassersteinProbability μ := ⟨radialHeatMeasure μ hX.quadratic p R s g,hdg.1,
    withDensity_absolutelyContinuous _ _,finiteSecondMoment_of_ae_dist_le _ p hdg.2.2⟩
  have hρ : (ρ s).val = heatMeasure μ hX.quadratic s f := by
    dsimp only [ρ,NoncollapsedRCD.heatProbability]; rw [max_eq_left hsp.le]
  have hσ : (σ s).val = heatMeasure μ hX.quadratic s g := by
    dsimp only [σ,NoncollapsedRCD.heatProbability]; rw [max_eq_left hsp.le]
  have hxf : dist η (ρ s)^2 ≤ D*Real.exp (-(2*a)*R) := by
    rw [ACWassersteinProbability.dist_sq μ hX.cd,hρ]
    exact hcutf s hsp.le hT R (zero_lt_one.trans_le hR) hmf
  have hxg : dist ζ (σ s)^2 ≤ E*Real.exp (-(2*a)*R) := by
    rw [ACWassersteinProbability.dist_sq μ hX.cd,hσ]
    exact hcutg s hsp.le hT R (zero_lt_one.trans_le hR) hmg
  have hyz : dist (ρ s) (σ s) ≤ max L 0 :=
    (hL (mem_image_of_mem _ (show s ∈ Icc t T from ⟨hs,hT⟩))).trans (le_max_left _ _)
  have he := pair_dist_square_exponential η (ρ s) ζ (σ s) hD hE (le_max_right L 0) ha
    (zero_le_one.trans hR) hxf hxg hyz
  rw [ACWassersteinProbability.dist_sq μ hX.cd,ACWassersteinProbability.dist_sq μ hX.cd,hρ,hσ] at he
  exact he

end

 
section

 
open Set Filter MeasureTheory Metric TopologicalSpace
open scoped Topology NNReal ENNReal
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] [SeparableSpace X]

theorem NoncollapsedRCD.radial_heat_two_cost_exponential
    (K : ℝ) (n : ℕ) [IsLocallyFiniteMeasure (hausdorff n X)] (hn : 2 ≤ n)
    (hX : NoncollapsedRCD K n X) (p : X) {A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hvol : ∀ R : ℝ, 1 ≤ R → (hausdorff n X).real (closedBall p (2*R)) ≤ A*Real.exp (B*R))
    (f g : Lp ℝ 2 (hausdorff n X)) (C : ℝ≥0) (hf0 : 0 ≤ f) (hg0 : 0 ≤ g)
    (hfC : ∀ᵐ x ∂hausdorff n X, f x ≤ C) (hgC : ∀ᵐ x ∂hausdorff n X, g x ≤ C)
    (hfi : Integrable f (hausdorff n X)) (hgi : Integrable g (hausdorff n X))
    (hfm : ∫x, f x ∂hausdorff n X = 1) (hgm : ∫x, g x ∂hausdorff n X = 1)
    {r r' : ℝ} (hfs : ∀ᵐ x ∂hausdorff n X, f x ≠ 0 → dist p x ≤ r)
    (hgs : ∀ᵐ x ∂hausdorff n X, g x ≠ 0 → dist p x ≤ r')
    {a t T : ℝ} (ha : 0 ≤ a) (ht : 0 < t) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ s, t ≤ s → s ≤ T → ∀ v, t ≤ v → v ≤ T → ∀ R, 1 ≤ R →
      (1:ℝ)/2 ≤ ∫x, radialCutoff p R x*heatAt (hausdorff n X) hX.quadratic s f x ∂hausdorff n X →
      (1:ℝ)/2 ≤ ∫x, radialCutoff p R x*heatAt (hausdorff n X) hX.quadratic v g x ∂hausdorff n X →
      |(wassersteinSq (radialHeatMeasure (hausdorff n X) hX.quadratic p R s f)
          (radialHeatMeasure (hausdorff n X) hX.quadratic p R v g)).toReal-
        (wassersteinSq (heatMeasure (hausdorff n X) hX.quadratic s f)
          (heatMeasure (hausdorff n X) hX.quadratic v g)).toReal| ≤ D*Real.exp (-a*R) := by
  let μ := hausdorff n X
  let := ACWassersteinProbability.metric μ K n hX.cd
  let ρ := hX.heatProbability K n hn p f hf0 ⟨r,hfs⟩ hfm
  let σ := hX.heatProbability K n hn p g hg0 ⟨r',hgs⟩ hgm
  have hfabs : ∀ᵐ x ∂μ, |f x| ≤ C := by
    filter_upwards [(Lp.coeFn_nonneg _).mpr hf0,hfC] with x hl hu
    simpa only [abs_of_nonneg hl] using hu
  have hgabs : ∀ᵐ x ∂μ, |g x| ≤ C := by
    filter_upwards [(Lp.coeFn_nonneg _).mpr hg0,hgC] with x hl hu
    simpa only [abs_of_nonneg hl] using hu
  have hc : ContinuousOn (fun q : ℝ×ℝ => dist (ρ q.1) (σ q.2)) ((Icc t T) ×ˢ (Icc t T)) := by
    intro s hs
    have hρ : ContinuousAt ρ s.1 := hX.heat_probability_continuousAt K n hn p f hf0 ⟨r,hfs⟩ hfm C hfabs
      (ht.trans_le hs.1.1)
    have hσ : ContinuousAt σ s.2 := hX.heat_probability_continuousAt K n hn p g hg0 ⟨r',hgs⟩ hgm C hgabs
      (ht.trans_le hs.2.1)
    have hd : ContinuousAt (fun q : ℝ×ℝ => dist (ρ q.1) (σ q.2)) s :=
      (hρ.comp continuousAt_fst).dist (hσ.comp continuousAt_snd)
    exact hd.continuousWithinAt
  obtain ⟨L,hL⟩ := (isCompact_Icc.prod isCompact_Icc).bddAbove_image hc
  obtain ⟨D,hD,hcutf⟩ := radialHeatMeasure_transport_exponential μ hX.quadratic p hA hB hvol
    f hf0 hfi hfm hfs (a := 2*a) (T := T) (by positivity)
  obtain ⟨E,hE,hcutg⟩ := radialHeatMeasure_transport_exponential μ hX.quadratic p hA hB hvol
    g hg0 hgi hgm hgs (a := 2*a) (T := T) (by positivity)
  refine ⟨(Real.sqrt D+Real.sqrt E)*(2*(max L 0)+(Real.sqrt D+Real.sqrt E)),by positivity,?_⟩
  intro s hs hT v hv hvT R hR hmf hmg
  have hvp : 0 < v := ht.trans_le hv
  have hsp : 0 < s := ht.trans_le hs
  have hdf := radialHeatMeasure_data μ hX.quadratic p hA hB hvol f C hf0 hfC hfi hfm
    (zero_lt_one.trans_le hR) hsp hmf
  have hdg := radialHeatMeasure_data μ hX.quadratic p hA hB hvol g C hg0 hgC hgi hgm
    (zero_lt_one.trans_le hR) hvp hmg
  let : IsProbabilityMeasure (radialHeatMeasure μ hX.quadratic p R s f) := hdf.1
  let : IsProbabilityMeasure (radialHeatMeasure μ hX.quadratic p R v g) := hdg.1
  let η : ACWassersteinProbability μ := ⟨radialHeatMeasure μ hX.quadratic p R s f,hdf.1,
    withDensity_absolutelyContinuous _ _,finiteSecondMoment_of_ae_dist_le _ p hdf.2.2⟩
  let ζ : ACWassersteinProbability μ := ⟨radialHeatMeasure μ hX.quadratic p R v g,hdg.1,
    withDensity_absolutelyContinuous _ _,finiteSecondMoment_of_ae_dist_le _ p hdg.2.2⟩
  have hρ : (ρ s).val = heatMeasure μ hX.quadratic s f := by
    dsimp only [ρ,NoncollapsedRCD.heatProbability]; rw [max_eq_left hsp.le]
  have hσ : (σ v).val = heatMeasure μ hX.quadratic v g := by
    dsimp only [σ,NoncollapsedRCD.heatProbability]; rw [max_eq_left hvp.le]
  have hxf : dist η (ρ s)^2 ≤ D*Real.exp (-(2*a)*R) := by
    rw [ACWassersteinProbability.dist_sq μ hX.cd,hρ]
    exact hcutf s hsp.le hT R (zero_lt_one.trans_le hR) hmf
  have hxg : dist ζ (σ v)^2 ≤ E*Real.exp (-(2*a)*R) := by
    rw [ACWassersteinProbability.dist_sq μ hX.cd,hσ]
    exact hcutg v hvp.le hvT R (zero_lt_one.trans_le hR) hmg
  have hyz : dist (ρ s) (σ v) ≤ max L 0 :=
    (hL (mem_image_of_mem _ (show (s,v) ∈ (Icc t T) ×ˢ (Icc t T) from ⟨⟨hs,hT⟩,⟨hv,hvT⟩⟩))).trans (le_max_left _ _)
  have he := pair_dist_square_exponential η (ρ s) ζ (σ v) hD hE (le_max_right L 0) ha
    (zero_le_one.trans hR) hxf hxg hyz
  rw [ACWassersteinProbability.dist_sq μ hX.cd,ACWassersteinProbability.dist_sq μ hX.cd,hρ,hσ] at he
  exact he

end

 

 
open Set Filter MeasureTheory Metric TopologicalSpace
open scoped Topology NNReal ENNReal
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] [SeparableSpace X]

theorem NoncollapsedRCD.variable_heat_frequent_slope
    (K : ℝ) (n : ℕ) [IsLocallyFiniteMeasure (hausdorff n X)] (hn : 2 ≤ n)
    (hX : NoncollapsedRCD K n X) (p : X)
    (f g : Lp ℝ 2 (hausdorff n X)) (C : ℝ≥0) (hf0 : 0 ≤ f) (hg0 : 0 ≤ g)
    (hfC : ∀ᵐ x ∂hausdorff n X, f x ≤ C) (hgC : ∀ᵐ x ∂hausdorff n X, g x ≤ C)
    (hfm : ∫x, f x ∂hausdorff n X = 1) (hgm : ∫x, g x ∂hausdorff n X = 1)
    {r r' : ℝ} (hfs : ∀ᵐ x ∂hausdorff n X, f x ≠ 0 → dist p x ≤ r)
    (hgs : ∀ᵐ x ∂hausdorff n X, g x ≠ 0 → dist p x ≤ r')
    (N : ℝ) (hN : (n:ℝ) ≤ N) (u v : ℝ) (hu : 0 < u) (hv : 0 < v) {t : ℝ} (ht : 0 < t) :
    ∀ z, N*(u-v)^2-K*(u^2+u*v+v^2)/3*
      (wassersteinSq (heatMeasure (hausdorff n X) hX.quadratic (u^2*t) f)
        (heatMeasure (hausdorff n X) hX.quadratic (v^2*t) g)).toReal < z →
      ∃ᶠ s in 𝓝[>] t, slope (fun q =>
        (wassersteinSq (heatMeasure (hausdorff n X) hX.quadratic (u^2*q) f)
          (heatMeasure (hausdorff n X) hX.quadratic (v^2*q) g)).toReal/2) t s < z := by
  let μ := hausdorff n X
  obtain ⟨A,B,hA,hB,hvol⟩ := hX.exponential_volume K n hn p
  have hfi := lp_integrable_of_bounded_support μ f p hfs
  have hgi := lp_integrable_of_bounded_support μ g p hgs
  have hup : 0 < u^2 := sq_pos_of_pos hu
  have hvp : 0 < v^2 := sq_pos_of_pos hv
  let b := 64*B+2
  have hb : 0 ≤ b := by dsimp [b]; positivity
  let a := 2*b+4
  have ha : 0 ≤ a := by dsimp [a]; positivity
  obtain ⟨Hf,Rf,hHf,hRf,hNormf⟩ := heat_normalized_cutoff_exponential μ hX.quadratic p hA hB hvol
    f C hf0 hfC hfi hfm hfs (a := a) (T := u^2*(t+1)) ha (mul_pos hup ht)
  obtain ⟨Hg,Rg,hHg,hRg,hNormg⟩ := heat_normalized_cutoff_exponential μ hX.quadratic p hA hB hvol
    g C hg0 hgC hgi hgm hgs (a := a) (T := v^2*(t+1)) ha (mul_pos hvp ht)
  obtain ⟨L,hL,hCost⟩ := hX.radial_heat_two_cost_exponential K n hn p hA hB hvol
    f g C hf0 hg0 hfC hgC hfi hgi hfm hgm hfs hgs (a := a)
    (T := max (u^2) (v^2)*(t+1)) ha (mul_pos (lt_min hup hvp) ht)
  let D : ℝ → ℝ := fun s => (wassersteinSq (heatMeasure μ hX.quadratic (u^2*s) f)
    (heatMeasure μ hX.quadratic (v^2*s) g)).toReal
  let Q : ℝ → ℝ := fun R => (wassersteinSq
    (radialHeatMeasure μ hX.quadratic p R (u^2*(t+Real.exp (-(b+1)*R))) f)
    (radialHeatMeasure μ hX.quadratic p R (v^2*(t+Real.exp (-(b+1)*R))) g)).toReal
  have hDc : ContinuousAt D t :=
    (hX.heat_two_cost_continuousAt K n hn p f g C hf0 hfC hfm hfs hg0 hgC hgm hgs
      (mul_pos hup ht) (mul_pos hvp ht)).comp (f := fun s : ℝ => (u^2*s,v^2*s)) (x := t)
      ((continuousAt_id.const_mul _).prodMk (continuousAt_id.const_mul _))
  have hc : ContinuousAt (fun s => N*(u-v)^2-(0:ℝ)-(2*K*(u^2+u*v+v^2)/3/2)*D s) t :=
    continuousAt_const.sub (hDc.const_mul _)
  have hs := frequent_slope_of_expanding_cutoffs (D := D) (E := fun _ => 0) (Q := Q) (F := fun _ => 0)
    (ev := N*(u-v)^2) (K := 2*K*(u^2+u*v+v^2)/3) (J := 0) (L := L)
    (N := 10000*(A+1)*(1+u^2+v^2))
    (A := u^4*(2*(1+1/(u^2*t/2)))^2*‖f‖+v^4*(2*(1+1/(v^2*t/2)))^2*‖g‖)
    (H := Hf+Hg) hb hc (by
      have htime : ∀ᶠ R : ℝ in atTop, Real.exp (-(b+1)*R) ≤ 1 :=
        (exp_neg_mul_tendsto_zero (by linarith : 0 < b+1)).eventually_le_const (by norm_num)
      filter_upwards [eventually_ge_atTop (max 1 (max Rf Rg)),htime] with R hR htime
      have hR1 : 1 ≤ R := (le_max_left _ _).trans hR
      have hRf' : Rf ≤ R := (le_max_left _ _).trans ((le_max_right _ _).trans hR)
      have hRg' : Rg ≤ R := (le_max_right _ _).trans ((le_max_right _ _).trans hR)
      have hRp : 0 < R := zero_lt_one.trans_le hR1
      let h := Real.exp (-(b+1)*R)
      have hh : 0 < h := Real.exp_pos _
      have hts : t ≤ t+h := le_add_of_nonneg_right hh.le
      have hsT : t+h ≤ t+1 := by dsimp only [h]; linarith only [htime]
      have hnf := hNormf (u^2*(t+h)) (mul_le_mul_of_nonneg_left hts hup.le)
        (mul_le_mul_of_nonneg_left hsT hup.le) R hRp hRf'
      have hng := hNormg (v^2*(t+h)) (mul_le_mul_of_nonneg_left hts hvp.le)
        (mul_le_mul_of_nonneg_left hsT hvp.le) R hRp hRg'
      have hcost := hCost (u^2*(t+h))
        ((mul_le_mul_of_nonneg_right (min_le_left _ _) ht.le).trans (mul_le_mul_of_nonneg_left hts hup.le))
        ((mul_le_mul_of_nonneg_left hsT hup.le).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)))
        (v^2*(t+h))
        ((mul_le_mul_of_nonneg_right (min_le_right _ _) ht.le).trans (mul_le_mul_of_nonneg_left hts hvp.le))
        ((mul_le_mul_of_nonneg_left hsT hvp.le).trans (mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity)))
        R hR1 hnf.1 hng.1
      refine ⟨hcost,by simp,?_⟩
      have hsec := hX.variable_cutoff_heat_secant K n hn p hA hB hvol f g C hf0 hg0
        hfC hgC hfi hgi hfm hgm hfs hgs u v hu hv hR1 ht hh hnf.1 hng.1 N hN
      have hnormf : ‖radialHeatSobolev μ hX.quadratic p hRp (mul_pos hup (add_pos ht hh)) f C-
          heatSobolev μ hX.quadratic (u^2*(t+h)) (mul_pos hup (add_pos ht hh)) f‖ ≤ Hf*Real.exp (-(2*b+4)*R) := by
        simpa only [radialHeatSobolev,norm_sub_rev,a] using hnf.2
      have hnormg : ‖radialHeatSobolev μ hX.quadratic p hRp (mul_pos hvp (add_pos ht hh)) g C-
          heatSobolev μ hX.quadratic (v^2*(t+h)) (mul_pos hvp (add_pos ht hh)) g‖ ≤ Hg*Real.exp (-(2*b+4)*R) := by
        simpa only [radialHeatSobolev,norm_sub_rev,a] using hng.2
      have hnorm := add_le_add hnormf hnormg
      rw [←add_mul] at hnorm
      have hbound := mul_le_mul_of_nonneg_left
        (add_le_add (le_refl ((u^4*(2*(1+1/(u^2*t/2)))^2*‖f‖+v^4*(2*(1+1/(v^2*t/2)))^2*‖g‖)*h))
          (mul_le_mul_of_nonneg_left hnorm (by positivity : 0 ≤ h⁻¹+2)))
        (by positivity : 0 ≤ 10000*(A+1)*(1+u^2+v^2)*Real.exp (b*R))
      convert hsec.trans (add_le_add (le_refl
        (N*(u-v)^2-K*(wassersteinSq
          (radialHeatMeasure μ hX.quadratic p R (u^2*(t+h)) f)
          (radialHeatMeasure μ hX.quadratic p R (v^2*(t+h)) g)).toReal*(u^2+u*v+v^2)/3)) hbound) using 1
      all_goals try dsimp only [D,Q,μ,h,b]
      all_goals first | rfl | ring)
  intro z hz
  apply hs z
  convert hz using 1
  dsimp only [D,μ]
  ring


end RegularPointCoordinates

end OAI
