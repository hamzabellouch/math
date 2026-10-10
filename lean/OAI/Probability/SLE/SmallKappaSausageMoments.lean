import Mathlib
import OAI.Probability.SLE.RetainedSeedMoments
import OAI.Probability.SLE.SimpleTails

namespace OAI

/-! Small Kappa Sausage Moments for chordal SLE. -/

section
section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal
open Set Filter MeasureTheory
open scoped Topology NNReal
open Set Filter MeasureTheory Complex
open MeasureTheory ProbabilityTheory Set Filter
open Set Filter Metric Complex InnerProductSpace
open scoped Topology Laplacian
open Set Filter Metric Complex MeasureTheory
open Set Filter Metric Complex MeasureTheory InnerProductSpace
open scoped Topology Laplacian ENNReal
open scoped Topology ENNReal
open scoped Topology Laplacian RealInnerProductSpace
open Set Filter Metric Complex
open scoped Topology
open Set Filter Metric
open Set Filter MeasureTheory Metric
open Set Filter Complex
open scoped Topology ComplexConjugate NNReal
open scoped Topology ENNReal NNReal ComplexConjugate
open Set Filter Metric MeasureTheory Complex
open Set Filter MeasureTheory ProbabilityTheory Classical
open scoped Topology ENNReal NNReal
open Set Filter MeasureTheory ProbabilityTheory Metric Classical
open Set Filter
open scoped Topology NNReal ENNReal ComplexConjugate
open scoped ENNReal NNReal
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology
section
open Set Filter MeasureTheory ProbabilityTheory Metric Complex Classical
open scoped Topology NNReal ENNReal
namespace SLEExactGauge
noncomputable section
lemma RegularSLEPresentation.source_initial_unit_mesh_tail_small
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {κ : ℝ} {γ : Ω → ℝ≥0 → ℂ} (a : RegularSLEPresentation P κ γ)
    (hκ : 0 < κ) (hκ4 : κ ≤ 4) (z₀ : ℂ) (hz : 2 < z₀.im) :
    ∃ C c d : ℝ, 0 < C ∧ 0 < c ∧ 0 < d ∧ d < 1 ∧
      ∀ rf δ : ℝ, 0 < rf → rf ≤ δ → δ ≤ d →
      (P.comap Subtype.val) {ω : a.samples | C*δ^(-codimension κ) <
        spatialRealMass κ (fun t => Real.sqrt κ*a.B t ω) (γ ω) (a.G ω) rf (ball z₀ 1)} ≤
        ENNReal.ofReal (C*Real.exp (-c*δ^(-2:ℝ))) := by
  let A := ball z₀ 1
  let B := meshTailAmplitude κ (1/2) A
  let C := max 1 ((volume A).toReal*(1/2:ℝ)^(-codimension κ)+1)
  have hB : 0 < B := meshTailAmplitude_pos A hκ (by norm_num) (by norm_num)
  have hC : 0 < C := zero_lt_one.trans_le (le_max_left _ _)
  refine ⟨C,1/(2*B^2),1/2,hC,by positivity,by norm_num,by norm_num,?_⟩
  intro rf δ hrf hrδ hδd
  have hδ : 0 < δ := hrf.trans_le hrδ
  have hR : δ ≤ ‖z₀‖+2 := by have := norm_nonneg z₀; linarith
  have hh := a.half_plane_mesh_tail hκ hκ4 A measurableSet_ball (1/2) rf δ (‖z₀‖+2)
    (by norm_num) (by norm_num) hrf hrδ hR
    (fun z hz' => (show δ ≤ 1 by linarith).trans (source_unit_ball_height hz (ball_subset_closedBall hz')).le)
    (fun z hz' => by
      have hz'' : dist z z₀ < 1 := hz'
      have htri := dist_triangle z z₀ 0
      simp only [dist_zero_right] at htri
      linarith)
  apply (measure_mono (show {ω : a.samples | C*δ^(-codimension κ) <
      spatialRealMass κ (fun t => Real.sqrt κ*a.B t ω) (γ ω) (a.G ω) rf A} ⊆
      {ω : a.samples | ((volume A).toReal*(1/2:ℝ)^(-codimension κ)+1)*δ^(-codimension κ) ≤
      spatialRealMass κ (fun t => Real.sqrt κ*a.B t ω) (γ ω) (a.G ω) rf A} from
      fun ω hω => ((mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.rpow_nonneg hδ.le _)).trans_lt hω).le)).trans
  apply hh.trans
  apply ENNReal.ofReal_le_ofReal
  have he := mul_le_mul_of_nonneg_right (show 1 ≤ C from le_max_left _ _)
    (Real.exp_pos (-(1/(2*B^2))*δ^(-2:ℝ))).le
  simpa only [one_mul] using he

lemma RegularSLEPresentation.source_unit_mesh_second_moment_small
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {κ : ℝ} {γ : Ω → ℝ≥0 → ℂ} (a : RegularSLEPresentation P κ γ)
    (hκ : 0 < κ) (hκ4 : κ ≤ 4) (z₀ : ℂ) (hz : 2 < z₀.im) :
    ∃ d m₂ : ℝ, 0 < d ∧ d < 1 ∧ 0 < m₂ ∧ ∀ rf : ℝ, 0 < rf → rf ≤ d →
      (∫⁻ ω : a.samples, ENNReal.ofReal (spatialRealMass κ (fun t => Real.sqrt κ*a.B t ω)
        (γ ω) (a.G ω) rf (ball z₀ 1))^2 ∂(P.comap Subtype.val)) ≤ ENNReal.ofReal m₂ := by
  obtain ⟨C,c,d,hC,hc,hd,hd1,ht⟩ := a.source_initial_unit_mesh_tail_small hκ hκ4 z₀ hz
  let μ := P.comap (Subtype.val : a.samples → Ω)
  let v := (volume (ball z₀ 1)).toReal
  let M := max C v*d^(-codimension κ)
  let b := c*d^(-2:ℝ)
  let A := max 1 C*Real.exp b
  let α := b/M
  have hκ8 : κ < 8 := by linarith
  have hp : 0 < codimension κ := codimension_pos κ hκ8
  have hp1 : codimension κ < 1 := by dsimp [codimension, dimension]; linarith
  have hM : 0 < M := mul_pos (hC.trans_le (le_max_left _ _)) (Real.rpow_pos_of_pos hd _)
  have hb : 0 < b := mul_pos hc (Real.rpow_pos_of_pos hd _)
  have hA : 0 < A := mul_pos (zero_lt_one.trans_le (le_max_left _ _)) (Real.exp_pos _)
  have hα : 0 < α := div_pos hb hM
  refine ⟨d,8*A/α^2,hd,hd1,by positivity,?_⟩
  intro rf hf hfd
  let X := fun ω : a.samples => spatialRealMass κ (fun t => Real.sqrt κ*a.B t ω)
    (γ ω) (a.G ω) rf (ball z₀ 1)
  have hx (ω : a.samples) : 0 ≤ X ω ∧ X ω ≤ v*rf^(-codimension κ) :=
    a.spatialRealMass_bound hκ hκ8 rf hf (ball z₀ 1) measurableSet_ball
      (measure_ball_lt_top (μ := volume) (x := z₀) (r := 1)).ne
      (fun z hz' => (hfd.trans hd1.le).trans (source_unit_ball_height hz (ball_subset_closedBall hz')).le) ω
  have hlinear : ∀ t : ℝ, 1 ≤ t → μ {ω | M*t < X ω} ≤ ENNReal.ofReal (C*Real.exp (-b*t)) :=
    source_mesh_tail_to_linear μ X (codimension κ) C c d v rf hp hp1.le hC hc hd
      ENNReal.toReal_nonneg hf (fun ω => (hx ω).2)
      (fun δ hfd hd' => ht rf δ hf hfd hd')
  exact source_exponential_second_moment μ X (a.spatialRealMass_measurable _ _) (fun ω => (hx ω).1)
    A α hA.le hα (source_linear_tail_all X M C b hM hC hb hlinear)

lemma source_retained_seed_all (κ : ℝ) (hκ : 0 < κ) (hκ8 : κ < 8)
    (Ω : Type) (m : MeasurableSpace Ω) (P : Measure Ω) (hP : IsProbabilityMeasure P)
    (γ : Ω → ℝ≥0 → ℂ) (a : RegularSLEPresentation P κ γ) (z₀ : ℂ) (hz : 2 < z₀.im) :
    ∃ (T : ℝ≥0) (e₀ m₀ m₂ : ℝ), 0 < T ∧ 0 < e₀ ∧ 0 < m₀ ∧ 0 < m₂ ∧
      ∀ r : ℝ, 0 < r → r ≤ e₀ →
      let X := fun ω : a.samples => finiteSpatialGreenMass κ
        (fun t => Real.sqrt κ*a.B t ω) (γ ω) (a.G ω) r T (closedBall z₀ 1)
      ENNReal.ofReal m₀ ≤ ∫⁻ ω, X ω ∂(P.comap Subtype.val) ∧
      (∫⁻ ω, (X ω)^2 ∂(P.comap Subtype.val)) ≤ ENNReal.ofReal m₂ := by
  let : IsProbabilityMeasure P := hP
  by_cases hκ4 : 4 < κ
  · exact sourceRetainedSeed_proved κ hκ4 hκ8 Ω m P hP γ a z₀ hz
  have hk4 : κ ≤ 4 := le_of_not_gt hκ4
  have hK : closedBall z₀ 1 ⊆ upperHalfPlane :=
    fun z hz' => zero_lt_one.trans (source_unit_ball_height hz hz')
  obtain ⟨T,e₀,m₀,hT,he,hm,hfirst⟩ := a.source_finite_time_first_moment hκ hκ8 z₀ 1 (by norm_num) hK
  obtain ⟨d,m₂,hd,hd1,hm₂,hsecond⟩ := a.source_unit_mesh_second_moment_small hκ hk4 z₀ hz
  refine ⟨T,min e₀ d,m₀,m₂,hT,lt_min he hd,hm,hm₂,?_⟩
  intro r hr hre
  refine ⟨hfirst r hr (hre.trans (min_le_left _ _)),?_⟩
  have hrd : r ≤ d := hre.trans (min_le_right _ _)
  apply le_trans (lintegral_mono (fun ω => pow_le_pow_left' (source_finite_mass_le_unit_mass
    a hκ hκ8 z₀ hz r hr (hrd.trans hd1.le) T ω) 2))
  exact hsecond r hr hrd
end
end SLEExactGauge
end

 
section
open Set Filter MeasureTheory ProbabilityTheory Metric
open scoped Topology NNReal ENNReal
namespace SLEExactGauge
noncomputable section
attribute [local instance] Classical.propDecidable
namespace RegularSLEPresentation
variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {κ : ℝ} {γ : Ω → ℝ≥0 → ℂ} (a : RegularSLEPresentation P κ γ)
theorem source_localized_spatial_slab_past_exponential
    (hκ : 0 < κ) (hκ4 : κ ≤ 4)
    (A : Set ℂ) (hA : MeasurableSet A)
    [IsFiniteMeasure (volume.comap (Subtype.val : A → ℂ))]
    (hfin : volume A ≠ ∞)
    (ε r : ℝ) (hε : 0 < ε) (hεr : ε ≤ r)
    (hheight : ∀ z ∈ A, r ≤ z.im)
    (u δ : ℝ) (b : SpatialAngularFamily a.B a.measurable_B κ
      (Subtype.val : A → ℂ) u δ)
    (M : ℝ) (hM : ∀ z : A, ‖initialLogCoordinates z‖ ≤ M)
    (S s : ℝ≥0) (D : Set a.samples) (hD : MeasurableSet[a.filtration s] D)
    (hbefore : ∀ ω ∈ D, ∀ z : A, s ≤ boundedSpatialHit (γ ω) z r S)
    (θ : ℝ) :
    (∫⁻ ω : a.samples, if ω ∈ D then ENNReal.ofReal (Real.exp
      (θ * (∫ z : A,
        (b.section z).physicalWeight (boundedSpatialHit (γ ω) z ε S) ω -
        (b.section z).physicalWeight (boundedSpatialHit (γ ω) z r S) ω
        ∂(volume.comap (Subtype.val : A → ℂ))) -
        θ^2 * slabVariance κ ε r A / 2)) else 1 ∂(P.comap Subtype.val)) ≤ 1 := by
  classical
  let ν := volume.comap (Subtype.val : A → ℂ)
  classical
  let σ₀ (p : A × a.samples) := boundedSpatialHit (γ p.2) p.1 r S
  let τ₀ (p : A × a.samples) := boundedSpatialHit (γ p.2) p.1 ε S
  let σ₁ (p : A × a.samples) := max (σ₀ p) s
  let τ₁ (p : A × a.samples) := if p.2 ∈ D then max (τ₀ p) s else σ₁ p
  let σ (p : A × a.samples) := min (σ₁ p) (b.τ p)
  let τ (p : A × a.samples) := min (τ₁ p) (b.τ p)
  have hσ₀ := a.joint_boundedSpatialHit_stopping (Subtype.val : A → ℂ) measurable_subtype_coe r S
  have hτ₀ := a.joint_boundedSpatialHit_stopping (Subtype.val : A → ℂ) measurable_subtype_coe ε S
  have hs := isStoppingTime_const (spatialFiltration (Z := A) a.filtration) s
  have hσ₁ : IsStoppingTime (spatialFiltration (Z := A) a.filtration)
      (fun p => (σ₁ p : WithTop ℝ≥0)) := by
    simpa only [σ₁, σ₀, WithTop.coe_max] using hσ₀.max hs
  have hDm : MeasurableSet[spatialFiltration (Z := A) a.filtration s] {p : A × a.samples | p.2 ∈ D} := by
    let : MeasurableSpace a.samples := a.filtration s
    exact hD.preimage measurable_snd
  have hτ₁ : IsStoppingTime (spatialFiltration (Z := A) a.filtration)
      (fun p => (τ₁ p : WithTop ℝ≥0)) := by
    have htmax : IsStoppingTime (spatialFiltration (Z := A) a.filtration)
        (fun p => ((max (τ₀ p) s : ℝ≥0) : WithTop ℝ≥0)) := by
      simpa only [τ₀, WithTop.coe_max] using hτ₀.max hs
    have hh := htmax.piecewise_of_le hσ₁
      (fun p => WithTop.coe_le_coe.mpr (le_max_right (τ₀ p) s))
      (fun p => WithTop.coe_le_coe.mpr (le_max_right (σ₀ p) s)) hDm
    convert hh using 1
    funext p
    by_cases hp : p.2 ∈ D <;> simp [τ₁, Set.piecewise, hp]
    rfl
  have hσ : IsStoppingTime (spatialFiltration (Z := A) a.filtration)
      (fun p => (σ p : WithTop ℝ≥0)) := by
    simpa only [σ, WithTop.coe_min] using hσ₁.min b.stopping
  have hτ : IsStoppingTime (spatialFiltration (Z := A) a.filtration)
      (fun p => (τ p : WithTop ℝ≥0)) := by
    simpa only [τ, WithTop.coe_min] using hτ₁.min b.stopping
  have hord (p : A × a.samples) : σ₀ p ≤ τ₀ p := by
    apply boundedSpatialHit_antitone_radius (a.trace_continuous p.2) p.1 hεr
    rw [(a.witness p.2).2.1, dist_zero_left]
    exact (hheight p.1 p.1.2).trans ((le_abs_self p.1.val.im).trans (Complex.abs_im_le_norm p.1))
  have hστ (p : A × a.samples) : σ p ≤ τ p := by
    apply min_le_min _ le_rfl
    dsimp only [τ₁]
    split_ifs
    · exact max_le_max (hord p) le_rfl
    · exact le_rfl
  have hsD (ω : a.samples) (hω : ω ∈ D) (z : A) :
      σ (z,ω) = min (boundedSpatialHit (γ ω) z r S) (b.τ (z,ω)) := by
    simp only [σ, σ₁, σ₀, max_eq_left (hbefore ω hω z)]
  have htD (ω : a.samples) (hω : ω ∈ D) (z : A) :
      τ (z,ω) = min (boundedSpatialHit (γ ω) z ε S) (b.τ (z,ω)) := by
    have hh := (hbefore ω hω z).trans (hord (z,ω))
    simp only [τ, τ₁, τ₀, hω, ↓reduceIte, max_eq_left hh]
  have hnotD (ω : a.samples) (hω : ω ∉ D) (z : A) : τ (z,ω) = σ (z,ω) := by
    simp only [τ, τ₁, hω, ↓reduceIte, σ]
  have htbound (p : A × a.samples) : τ p ≤ b.T := (min_le_right _ _).trans (b.bounded p)
  have hin (z : A) (ω : a.samples) (t : ℝ≥0) (ht : t ≤ τ (z,ω)) :
      b.lo ≤ ((b.c (initialLogCoordinates z)).Q t ω).1.im ∧
        ((b.c (initialLogCoordinates z)).Q t ω).1.im ≤ b.hi :=
    (b.inside z ω t (ht.trans (min_le_right _ _))).2.2
  have hexp := clipped_spatial_green_window_unbounded_driver (ν := ν) a.measurable_B a.brownian
    a.continuous_B a.zero_B κ b.lo b.hi b.le hκ (by linarith) b.c
    (fun z : A => initialLogCoordinates z) (measurable_initialLogCoordinates.comp measurable_subtype_coe)
    M hM b.T σ τ hσ hτ hστ htbound hin θ
  let E (ω : a.samples) := ∫ t in (0 : ℝ)..(b.T : ℝ),
    (∫ z : A, if (σ (z,ω) : ℝ) ≤ t ∧ t < (τ (z,ω) : ℝ) then
      greenLogCoefficient κ ((b.c (initialLogCoordinates z)).Q t ω) (a.B t.toNNReal ω) else 0 ∂ν)^2
  have hE (ω : a.samples) : E ω ≤ slabVariance κ ε r A := by
    apply interval_square_energy_bound _ b.T _ (slabVariance_nonneg _ _ _ _)
    rw [ofReal_slabVariance _ _ _ _ hfin]
    apply (a.witness ω).spatial_masked_bracket_bound ((a.continuous_B ω).const_mul _)
      hκ hκ4 hε (hε.trans_le hεr) A hA (fun z hz => hεr.trans (hheight z hz))
    intro t ht z
    have hb := clipped_spatial_window_coefficient_le b.c a.continuous_B z
      (show z.val ∈ upperHalfPlane from hε.trans_le (hεr.trans (hheight z z.2))) ω (b.τ (z,ω)) S
      (γ ω) (a.G ω) (a.F ω) (a.witness ω)
      (fun s hs => (b.inside z ω s hs).2.2) r ε t.toNNReal
    by_cases hω : ω ∈ D
    · simpa only [hsD ω hω z, htD ω hω z, ← NNReal.coe_le_coe,
        ← NNReal.coe_lt_coe, Real.coe_toNNReal _ ht] using hb
    · simp only [hnotD ω hω z]
      have hn (v : ℝ) : ¬ ((σ (z,ω) : ℝ) ≤ v ∧ v < (σ (z,ω) : ℝ)) := fun hh => (not_lt_of_ge hh.1) hh.2
      simp only [hn t, ↓reduceIte, abs_zero]
      exact (abs_nonneg _)

  have hEzero (ω : a.samples) (hω : ω ∉ D) : E ω = 0 := by
    have hf (t : ℝ) (z : A) : ¬ ((σ (z,ω) : ℝ) ≤ t ∧ t < (τ (z,ω) : ℝ)) := by
      rw [hnotD ω hω z]
      exact fun hh => (not_lt_of_ge hh.1) hh.2
    simp only [E, hf, ↓reduceIte, integral_zero, zero_pow (by norm_num : 2 ≠ 0), intervalIntegral.integral_zero]
  apply le_trans _ hexp
  apply lintegral_mono
  intro ω
  by_cases hω : ω ∈ D
  · simp only [hω, ↓reduceIte]
    apply ENNReal.ofReal_le_ofReal
    apply Real.exp_le_exp.mpr
    change θ * _ - θ^2 * slabVariance κ ε r A / 2 ≤ θ * _ - θ^2 * E ω / 2
    have hid : (∫ z : A,
        (b.section z).physicalWeight (boundedSpatialHit (γ ω) z ε S) ω -
        (b.section z).physicalWeight (boundedSpatialHit (γ ω) z r S) ω ∂ν) =
        ∫ z : A, greenLogDensity κ ((b.c (initialLogCoordinates z)).Q (τ (z,ω)) ω) (a.B (τ (z,ω)) ω) -
          greenLogDensity κ ((b.c (initialLogCoordinates z)).Q (σ (z,ω)) ω) (a.B (σ (z,ω)) ω) ∂ν := by
      apply integral_congr_ae
      exact Eventually.of_forall fun z => by
        simp only [AngularLocalization.physicalWeight, SpatialAngularFamily.section,
          hsD ω hω z, htD ω hω z, NNReal.coe_min]
    rw [hid]
    nlinarith [mul_le_mul_of_nonneg_left (hE ω) (sq_nonneg θ)]
  · simp only [hω, ↓reduceIte]
    change (1:ℝ≥0∞) ≤ ENNReal.ofReal (Real.exp (θ*_ - θ^2*E ω/2))
    simp only [hnotD ω hω, sub_self, integral_zero, hEzero ω hω, mul_zero,
      zero_div, Real.exp_zero, ENNReal.ofReal_one, le_refl]

end RegularSLEPresentation
end
end SLEExactGauge
end

 
section
open Set Filter MeasureTheory ProbabilityTheory Metric
open scoped Topology NNReal ENNReal
namespace SLEExactGauge
noncomputable section
attribute [local instance] Classical.propDecidable
lemma source_past_exponential_fatou
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (D : Set Ω) (hD : MeasurableSet D) (X : ℕ → Ω → ℝ) (Y : Ω → ℝ)
    (θ V : ℝ) (hm : ∀ n, Measurable (X n))
    (hlim : ∀ᵐ ω ∂P, Tendsto (fun n => X n ω) atTop (𝓝 (Y ω)))
    (hexp : ∀ n, (∫⁻ ω, if ω ∈ D then ENNReal.ofReal
      (Real.exp (θ*X n ω-θ^2*V/2)) else 1 ∂P) ≤ 1) :
    (∫⁻ ω, if ω ∈ D then ENNReal.ofReal
      (Real.exp (θ*Y ω-θ^2*V/2)) else 1 ∂P) ≤ 1 := by
  let f (n : ℕ) (ω : Ω) := if ω ∈ D then
    ENNReal.ofReal (Real.exp (θ*X n ω-θ^2*V/2)) else 1
  have hfm (n : ℕ) : Measurable (f n) :=
    (((((hm n).const_mul θ).sub_const (θ^2*V/2)).exp).ennreal_ofReal).ite hD measurable_const
  have hl : ∀ᵐ ω ∂P, (if ω ∈ D then ENNReal.ofReal
      (Real.exp (θ*Y ω-θ^2*V/2)) else 1) = liminf (fun n => f n ω) atTop := by
    filter_upwards [hlim] with ω hω
    by_cases hmem : ω ∈ D
    · simp only [hmem, ↓reduceIte, f]
      exact ((ENNReal.continuous_ofReal.tendsto _).comp
        ((Real.continuous_exp.tendsto _).comp
          ((hω.const_mul θ).sub_const (θ^2*V/2)))).liminf_eq.symm
    · simp only [hmem, ↓reduceIte, f, liminf_const]
  calc
    _ = ∫⁻ ω, liminf (fun n => f n ω) atTop ∂P := lintegral_congr_ae hl
    _ ≤ liminf (fun n => ∫⁻ ω, f n ω ∂P) atTop := lintegral_liminf_le' (fun n => (hfm n).aemeasurable)
    _ ≤ 1 := liminf_le_of_frequently_le (Frequently.of_forall hexp)
end
end SLEExactGauge
end

 
section
open Set Filter MeasureTheory ProbabilityTheory Metric
open scoped Topology NNReal ENNReal
namespace SLEExactGauge
noncomputable section
attribute [local instance] Classical.propDecidable
namespace RegularSLEPresentation
variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {κ : ℝ} {γ : Ω → ℝ≥0 → ℂ} (a : RegularSLEPresentation P κ γ)
theorem source_past_spatial_slab_finite_exponential_of_localizations
    (hκ : 0 < κ) (hκ4 : κ ≤ 4)
    (A : Set ℂ) (hA : MeasurableSet A)
    [IsFiniteMeasure (volume.comap (Subtype.val : A → ℂ))]
    (hfin : volume A ≠ ∞)
    (ε r : ℝ) (hε : 0 < ε) (hεr : ε ≤ r)
    (hheight : ∀ z ∈ A, r ≤ z.im)
    (u : ℝ) (δ : ℕ → ℝ) (hδ : Tendsto δ atTop (𝓝 0))
    (b : ∀ n, SpatialAngularFamily a.B a.measurable_B κ (Subtype.val : A → ℂ) u (δ n))
    (l : ℝ) (hl : ∀ z : A, l ≤ Real.log z.val.im)
    (hlevel : ∀ z : A, (2 * z.val.im) * Real.exp (-u) < ε)
    (M : ℝ) (hM : ∀ z : A, ‖initialLogCoordinates z‖ ≤ M)
    (S s : ℝ≥0) (D : Set a.samples) (hD : MeasurableSet[a.filtration s] D)
    (hbefore : ∀ ω ∈ D, ∀ z : A, s ≤ boundedSpatialHit (γ ω) z r S)
    (θ : ℝ) :
    (∫⁻ ω : a.samples, if ω ∈ D then ENNReal.ofReal (Real.exp
      (θ * (∫ z : A,
        greenDensity κ (fun t => Real.sqrt κ * a.B t ω) (γ ω) (a.G ω) (boundedSpatialHit (γ ω) z ε S) z -
        greenDensity κ (fun t => Real.sqrt κ * a.B t ω) (γ ω) (a.G ω) (boundedSpatialHit (γ ω) z r S) z
        ∂(volume.comap (Subtype.val : A → ℂ))) -
        θ^2 * slabVariance κ ε r A / 2)) else 1 ∂(P.comap Subtype.val)) ≤ 1 := by
  let ν := volume.comap (Subtype.val : A → ℂ)
  let σ (p : A × a.samples) := boundedSpatialHit (γ p.2) p.1 r S
  let τ (p : A × a.samples) := boundedSpatialHit (γ p.2) p.1 ε S
  have hσ : Measurable σ := stopping_time_measurable_nnreal
    (a.joint_boundedSpatialHit_stopping Subtype.val measurable_subtype_coe r S)
  have hτ : Measurable τ := stopping_time_measurable_nnreal
    (a.joint_boundedSpatialHit_stopping Subtype.val measurable_subtype_coe ε S)
  let X (n : ℕ) (ω : a.samples) := ∫ z : A,
        ((b n).section z).physicalWeight (τ (z,ω)) ω -
        ((b n).section z).physicalWeight (σ (z,ω)) ω ∂ν
  let Y (ω : a.samples) := ∫ z : A,
        greenDensity κ (fun t => Real.sqrt κ * a.B t ω) (γ ω) (a.G ω) (τ (z,ω)) z -
        greenDensity κ (fun t => Real.sqrt κ * a.B t ω) (γ ω) (a.G ω) (σ (z,ω)) z ∂ν
  have hXm (n : ℕ) : Measurable (X n) :=
    (((b n).physicalWeight_joint_measurable a.continuous_B measurable_subtype_coe τ hτ).sub
      ((b n).physicalWeight_joint_measurable a.continuous_B measurable_subtype_coe σ hσ)).stronglyMeasurable.integral_prod_left'.measurable
  have hlim (ω : a.samples) : Tendsto (fun n => X n ω) atTop (𝓝 (Y ω)) := by
    have hh := spatial_angular_weight_integral_tendsto (ν := ν) b hδ a.continuous_B
      measurable_subtype_coe hκ (by linarith) (fun z => hε.trans_le (hεr.trans (hheight z z.2)))
      l hl ω (γ ω) (a.G ω) (a.F ω) (a.witness ω) σ τ hσ hτ
    convert hh using 1
    congr 1
    apply integral_congr_ae
    apply Eventually.of_forall
    intro z
    dsimp only
    rw [(a.witness ω).physicalGreen_eq_before_spatial ((a.continuous_B ω).const_mul _)
      κ z ε hε (hεr.trans (hheight z z.2)) u (hlevel z) (τ (z,ω)) (boundedSpatialHit_le _ _ _ _),
      (a.witness ω).physicalGreen_eq_before_spatial ((a.continuous_B ω).const_mul _)
      κ z r (hε.trans_le hεr) (hheight z z.2) u ((hlevel z).trans_le hεr)
        (σ (z,ω)) (boundedSpatialHit_le _ _ _ _)]
  apply source_past_exponential_fatou D ((a.filtration.le s) _ hD) X Y θ
    (slabVariance κ ε r A) hXm (Eventually.of_forall hlim)
  intro n
  exact a.source_localized_spatial_slab_past_exponential hκ hκ4 A hA hfin ε r hε hεr hheight u (δ n) (b n) M hM S s D hD hbefore θ

end RegularSLEPresentation
end
end SLEExactGauge
end

 
section
open Set Filter MeasureTheory ProbabilityTheory Metric
open scoped Topology NNReal ENNReal
namespace SLEExactGauge
noncomputable section
attribute [local instance] Classical.propDecidable
namespace RegularSLEPresentation
variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {κ : ℝ} {γ : Ω → ℝ≥0 → ℂ} (a : RegularSLEPresentation P κ γ)
theorem source_past_spatial_slab_finite_exponential
    (hκ : 0 < κ) (hκ4 : κ ≤ 4)
    (A : Set ℂ) (hA : MeasurableSet A)
    (ε r R : ℝ) (hε : 0 < ε) (hεr : ε ≤ r) (hrR : r ≤ R)
    (hheight : ∀ z ∈ A, r ≤ z.im) (hbound : ∀ z ∈ A, ‖z‖ ≤ R)
    (S s : ℝ≥0) (D : Set a.samples) (hD : MeasurableSet[a.filtration s] D)
    (hbefore : ∀ ω ∈ D, ∀ z : A, s ≤ boundedSpatialHit (γ ω) z r S)
    (θ : ℝ) :
    (∫⁻ ω : a.samples, if ω ∈ D then ENNReal.ofReal (Real.exp
      (θ * (∫ z in A,
        greenDensity κ (fun t => Real.sqrt κ * a.B t ω) (γ ω) (a.G ω) (boundedSpatialHit (γ ω) z ε S) z -
        greenDensity κ (fun t => Real.sqrt κ * a.B t ω) (γ ω) (a.G ω) (boundedSpatialHit (γ ω) z r S) z) -
        θ^2 * slabVariance κ ε r A / 2)) else 1 ∂(P.comap Subtype.val)) ≤ 1 := by
  have hr : 0 < r := hε.trans_le hεr
  have hR : 0 < R := hr.trans_le hrR
  have hs : A ⊆ closedBall 0 R := by
    intro z hz
    simpa only [mem_closedBall, dist_zero_right] using hbound z hz
  have hfin : volume A ≠ ∞ := ne_of_lt
    ((measure_mono hs).trans_lt (isCompact_closedBall (0 : ℂ) R).measure_lt_top)
  let ν := volume.comap (Subtype.val : A → ℂ)
  let : IsFiniteMeasure ν := ⟨by
    have hh := Measure.comap_apply_le (Subtype.val : A → ℂ) volume
      (show NullMeasurableSet (univ : Set A) ν from MeasurableSet.univ.nullMeasurableSet)
    apply lt_of_le_of_lt hh
    simpa only [Set.image_univ, Subtype.range_coe] using lt_top_iff_ne_top.mpr hfin⟩
  obtain ⟨u, hu, hul⟩ := exists_uniform_radius_level ε R hε hR.le
  let α := r^2 / R^2
  have hα : 0 < α := by dsimp [α]; positivity
  let δ (n : ℕ) := α / ((n : ℝ) + 1)
  have hδpos (n : ℕ) : 0 < δ n := by dsimp [δ]; positivity
  have hδle (n : ℕ) : δ n ≤ α := div_le_self hα.le (by linarith [Nat.cast_nonneg (α := ℝ) n])
  have hδlim : Tendsto δ atTop (𝓝 0) := by
    simpa only [mul_one_div, mul_zero] using
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul α
  have hbounds (z : A) := initial_spatial_bounds κ r R hr hR z (hheight z z.2) (hbound z z.2)
  have hBm : Measurable (fun p : ℝ≥0 × a.samples => a.B p.1 p.2) :=
    measurable_uncurry_of_continuous_of_measurable a.continuous_B a.measurable_B
  let b (n : ℕ) : SpatialAngularFamily a.B a.measurable_B κ (Subtype.val : A → ℂ) u (δ n) :=
    (exists_spatial_angular_family a.measurable_B hBm a.continuous_B a.zero_B κ Subtype.val
      measurable_subtype_coe (Real.log r) (Real.log R) (Real.log_le_log hr hrR)
      (fun z => (hbounds z).1) u (δ n) hu (hδpos n)
      (fun z => (hδle n).trans (hbounds z).2.1)).some
  have hlevel (z : A) : (2 * z.val.im) * Real.exp (-u) < ε := by
    have hi : z.val.im ≤ R := (le_abs_self _).trans ((Complex.abs_im_le_norm z).trans (hbound z z.2))
    exact (mul_le_mul_of_nonneg_right (by linarith : 2 * z.val.im ≤ 2 * R) (Real.exp_pos _).le).trans_lt hul
  have hh := a.source_past_spatial_slab_finite_exponential_of_localizations hκ hκ4 A hA hfin ε r hε hεr
    hheight u δ hδlim b (Real.log r) (fun z => (hbounds z).1.1) hlevel
    (R + |Real.log r| + |Real.log R|) (fun z => (hbounds z).2.2) S s D hD hbefore θ
  have he (ω : a.samples) :
      (∫ z : A,
        greenDensity κ (fun t => Real.sqrt κ * a.B t ω) (γ ω) (a.G ω) (boundedSpatialHit (γ ω) z ε S) z -
        greenDensity κ (fun t => Real.sqrt κ * a.B t ω) (γ ω) (a.G ω) (boundedSpatialHit (γ ω) z r S) z
        ∂(volume.comap (Subtype.val : A → ℂ))) =
      ∫ z in A,
        greenDensity κ (fun t => Real.sqrt κ * a.B t ω) (γ ω) (a.G ω) (boundedSpatialHit (γ ω) z ε S) z -
        greenDensity κ (fun t => Real.sqrt κ * a.B t ω) (γ ω) (a.G ω) (boundedSpatialHit (γ ω) z r S) z :=
    integral_subtype_comap (μ := volume) hA (fun z =>
      greenDensity κ (fun t => Real.sqrt κ * a.B t ω) (γ ω) (a.G ω) (boundedSpatialHit (γ ω) z ε S) z -
      greenDensity κ (fun t => Real.sqrt κ * a.B t ω) (γ ω) (a.G ω) (boundedSpatialHit (γ ω) z r S) z)
  simpa only [he] using hh

end RegularSLEPresentation
end
end SLEExactGauge
end

 
section
open Set Filter MeasureTheory ProbabilityTheory Metric
open scoped Topology NNReal ENNReal
namespace SLEExactGauge
noncomputable section
attribute [local instance] Classical.propDecidable
namespace RegularSLEPresentation
variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {κ : ℝ} {γ : Ω → ℝ≥0 → ℂ} (a : RegularSLEPresentation P κ γ)
lemma source_past_spatial_slab_terminal_exponential [IsProbabilityMeasure P]
    (hκ : 0 < κ) (hκ4 : κ ≤ 4)
    (A : Set ℂ) (hA : MeasurableSet A)
    (ε r R : ℝ) (hε : 0 < ε) (hεr : ε ≤ r) (hrR : r ≤ R)
    (hheight : ∀ z ∈ A, r ≤ z.im) (hbound : ∀ z ∈ A, ‖z‖ ≤ R)
    (s : ℝ≥0) (D : Set a.samples) (hD : MeasurableSet[a.filtration s] D)
    (hbefore : ∀ ω ∈ D, ∀ z ∈ A, (s : WithTop ℝ≥0) ≤ spatialHitTime (γ ω) z r)
    (θ : ℝ) :
    (∫⁻ ω in D, ENNReal.ofReal (Real.exp
      (θ*spatialSlabIncrement κ (fun t => Real.sqrt κ*a.B t ω)
        (γ ω) (a.G ω) A ε r - θ^2*slabVariance κ ε r A/2))
      ∂(P.comap Subtype.val)) ≤ (P.comap Subtype.val) D := by
  have hs : A ⊆ closedBall 0 R := by
    intro z hz
    simpa only [mem_closedBall, dist_zero_right] using hbound z hz
  have hfin : volume A ≠ ∞ := ne_of_lt
    ((measure_mono hs).trans_lt (isCompact_closedBall (0 : ℂ) R).measure_lt_top)
  obtain ⟨N,hN⟩ := exists_nat_ge s
  let X (n : ℕ) (ω : a.samples) := ∫ z in A,
    greenDensity κ (fun t => Real.sqrt κ*a.B t ω) (γ ω) (a.G ω) (boundedSpatialHit (γ ω) z ε (n+N)) z -
    greenDensity κ (fun t => Real.sqrt κ*a.B t ω) (γ ω) (a.G ω) (boundedSpatialHit (γ ω) z r (n+N)) z
  let Y (ω : a.samples) := spatialSlabIncrement κ (fun t => Real.sqrt κ*a.B t ω)
    (γ ω) (a.G ω) A ε r
  have hXm (n : ℕ) : Measurable (X n) :=
    ((a.boundedSpatialGreen_measurable ε (n+N)).sub
      (a.boundedSpatialGreen_measurable r (n+N))).stronglyMeasurable.integral_prod_left'.measurable
  have hDm : MeasurableSet D := (a.filtration.le s) _ hD
  have hmask : (∫⁻ ω : a.samples, if ω ∈ D then ENNReal.ofReal
      (Real.exp (θ*Y ω-θ^2*slabVariance κ ε r A/2)) else 1 ∂P.comap Subtype.val) ≤ 1 := by
    apply source_past_exponential_fatou D hDm X Y θ (slabVariance κ ε r A) hXm
    · filter_upwards [a.spatial_slab_area_tendsto hκ (by linarith) A hA hfin ε r R hε hεr hrR hheight hbound] with ω hω
      simpa only [X, Y, spatialSlabIncrement, Function.comp_def, Nat.cast_add] using hω.comp (tendsto_add_atTop_nat N)
    · intro n
      apply a.source_past_spatial_slab_finite_exponential hκ hκ4 A hA ε r R hε hεr hrR hheight hbound (n+N) s D hD
      intro ω hω z
      apply WithTop.coe_le_coe.mp
      rw [boundedSpatialHit_coe]
      apply le_min (hbefore ω hω z z.2)
      exact WithTop.coe_le_coe.mpr (hN.trans (le_add_of_nonneg_left (by positivity)))
  let μ := P.comap (Subtype.val : a.samples → Ω)
  let f (ω : a.samples) := ENNReal.ofReal (Real.exp (θ*Y ω-θ^2*slabVariance κ ε r A/2))
  change (∫⁻ ω, if ω ∈ D then f ω else 1 ∂μ) ≤ 1 at hmask
  rw [←lintegral_add_compl _ hDm] at hmask
  have hleft : (∫⁻ ω in D, if ω ∈ D then f ω else 1 ∂μ) = ∫⁻ ω in D, f ω ∂μ :=
    setLIntegral_congr_fun hDm (fun ω hω => ite_eq_left hω)
  have hright : (∫⁻ ω in Dᶜ, if ω ∈ D then f ω else 1 ∂μ) = μ Dᶜ := by
    rw [setLIntegral_congr_fun hDm.compl (fun ω hω => ite_eq_right hω)]
    simp
  rw [hleft,hright] at hmask
  have hsum : μ D+μ Dᶜ = 1 := by rw [measure_add_measure_compl hDm,measure_univ]
  exact (ENNReal.add_le_add_iff_right (measure_ne_top μ Dᶜ)).mp (hmask.trans_eq hsum.symm)
end RegularSLEPresentation
end
end SLEExactGauge
end

 
section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal
namespace SLEExactGauge
noncomputable section
attribute [local instance] Classical.propDecidable
lemma source_infinite_stopping_grid_piece
    {Ω : Type*} [m : MeasurableSpace Ω] {ℱ : Filtration ℝ≥0 m}
    {ρ : Ω → WithTop ℝ≥0} (hρ : IsStoppingTime ℱ ρ) (n k : ℕ) :
    MeasurableSet[ℱ (stopGridTime n k)]
      ({ω | ρ ω ≠ ⊤} ∩ {ω | stopGridIndex n ((ρ ω).untopD 0) = k}) := by
  let A := {ω | ρ ω ≠ ⊤}
  have hle (j : ℕ) : MeasurableSet[ℱ (stopGridTime n j)]
      (A ∩ {ω | stopGridIndex n ((ρ ω).untopD 0) ≤ j}) := by
    convert hρ (stopGridTime n j) using 1
    ext ω
    cases he : ρ ω with
    | top => simp only [A,mem_inter_iff,mem_ofPred_eq,he,ne_eq,not_true_eq_false,false_and,WithTop.not_top_le_coe]
    | coe t => simp only [A,mem_inter_iff,mem_ofPred_eq,he,WithTop.coe_ne_top,ne_eq,not_false_eq_true,true_and,WithTop.untopD_coe,stopGridIndex_le,WithTop.coe_le_coe]
  cases k with
  | zero => simpa only [Nat.le_zero] using hle 0
  | succ k =>
    have he : A ∩ {ω | stopGridIndex n ((ρ ω).untopD 0) = k+1} =
        (A ∩ {ω | stopGridIndex n ((ρ ω).untopD 0) ≤ k+1}) \
          (A ∩ {ω | stopGridIndex n ((ρ ω).untopD 0) ≤ k}) := by
      ext ω
      simp only [mem_inter_iff,mem_ofPred_eq,Set.mem_sdiff]
      constructor
      · rintro ⟨hω,he⟩; exact ⟨⟨hω,he.le⟩,fun hn => by omega⟩
      · rintro ⟨⟨hω,hle⟩,hn⟩
        exact ⟨hω,by have hh : ¬stopGridIndex n ((ρ ω).untopD 0) ≤ k := fun hk => hn ⟨hω,hk⟩; omega⟩
    change MeasurableSet[ℱ (stopGridTime n (k+1))] (A ∩ _)
    rw [he]
    exact (hle (k+1)).diff (ℱ.mono (monotone_stopGridTime n (Nat.le_succ k)) _ (hle k))

 

lemma source_between_stopping_tail
    {Ω : Type*} [m : MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]
    {ℱ : Filtration ℝ≥0 m} {ρ τ : Ω → WithTop ℝ≥0}
    (hρ : IsStoppingTime ℱ ρ) (hτ : IsStoppingTime ℱ τ)
    (H : Set Ω) (hH : MeasurableSet H)
    (hHA : H ⊆ {ω | ρ ω ≠ ⊤})
    (hsep : ∀ ω, ρ ω ≠ ⊤ → ρ ω < τ ω)
    (K : ℝ≥0∞)
    (ht : ∀ (s : ℝ≥0) (D : Set Ω), MeasurableSet[ℱ s] D →
      (∀ ω ∈ D, (s : WithTop ℝ≥0) ≤ τ ω) → μ (D ∩ H) ≤ μ D*K) :
    μ H ≤ μ {ω | ρ ω ≠ ⊤}*K := by
  let A := {ω | ρ ω ≠ ⊤}
  let Q (n k : ℕ) := A ∩ {ω | stopGridIndex n ((ρ ω).untopD 0) = k}
  let D (n k : ℕ) := Q n k ∩ {ω | (stopGridTime n k : WithTop ℝ≥0) < τ ω}
  let E (n : ℕ) := ⋃ k, D n k
  have hQ (n k : ℕ) : MeasurableSet[ℱ (stopGridTime n k)] (Q n k) :=
    source_infinite_stopping_grid_piece hρ n k
  have hD (n k : ℕ) : MeasurableSet[ℱ (stopGridTime n k)] (D n k) :=
    (hQ n k).inter (by simpa only [compl_ofPred,not_le] using (hτ (stopGridTime n k)).compl)
  have hDm (n k : ℕ) : MeasurableSet (D n k) := (ℱ.le _) _ (hD n k)
  have hEm (n : ℕ) : MeasurableSet (E n) := MeasurableSet.iUnion (hDm n)
  have hEq (n : ℕ) : ⋃ k, Q n k = A := grid_partition_union A n
  have hEd (n : ℕ) : Pairwise (fun i j => Disjoint (Q n i) (Q n j)) := grid_partition_disjoint A n
  have hb (n : ℕ) : μ (E n ∩ H) ≤ μ A*K := by
    calc
      μ (E n ∩ H) = μ (⋃ k, D n k ∩ H) := by simp only [E,iUnion_inter]
      _ ≤ ∑' k, μ (D n k ∩ H) := measure_iUnion_le _
      _ ≤ ∑' k, μ (Q n k)*K := ENNReal.tsum_le_tsum fun k =>
        (ht (stopGridTime n k) (D n k) (hD n k) (fun ω hω => hω.2.le)).trans
          (mul_le_mul' (measure_mono inter_subset_left) le_rfl)
      _ = (∑' k, μ (Q n k))*K := ENNReal.tsum_mul_right
      _ = μ A*K := by rw [←measure_iUnion (hEd n) (fun k => (ℱ.le _) _ (hQ n k)),hEq]
  have hevent (ω : Ω) (hω : ω ∈ A) : ∀ᶠ n in atTop, ω ∈ E n := by
    obtain ⟨t,ht'⟩ := WithTop.ne_top_iff_exists.mp hω
    have ht : ρ ω = (t : WithTop ℝ≥0) := ht'.symm
    have hlt := hsep ω hω
    rw [ht] at hlt
    have hgrid : ∀ᶠ n in atTop, (stopGrid n t : WithTop ℝ≥0) < τ ω := by
      cases hv : τ ω with
      | top => exact Eventually.of_forall fun n => WithTop.coe_lt_top _
      | coe v =>
        rw [hv] at hlt
        have hh : ∀ᶠ n in atTop, stopGrid n t < v := (stopGrid_tendsto t) (Iio_mem_nhds (WithTop.coe_lt_coe.mp hlt))
        exact hh.mono fun n hn => by simpa only [hv,WithTop.coe_lt_coe] using hn
    filter_upwards [hgrid] with n hn
    refine mem_iUnion.mpr ⟨stopGridIndex n t, ?_⟩
    exact ⟨⟨hω,by change stopGridIndex n ((ρ ω).untopD 0) = stopGridIndex n t; rw [ht]; rfl⟩,hn⟩
  let f (n : ℕ) := (E n ∩ H).indicator (fun _ : Ω => (1 : ℝ≥0∞))
  have hfm (n : ℕ) : Measurable (f n) := measurable_const.indicator ((hEm n).inter hH)
  have hp : H.indicator (fun _ : Ω => (1 : ℝ≥0∞)) ≤ fun ω => liminf (fun n => f n ω) atTop := by
    intro ω
    by_cases hω : ω ∈ H
    · rw [indicator_of_mem hω]
      apply le_liminf_of_le (by isBoundedDefault)
      filter_upwards [hevent ω (hHA hω)] with n hn
      simp only [f,indicator_of_mem (show ω ∈ E n ∩ H from ⟨hn,hω⟩),le_refl]
    · simp only [indicator_of_notMem hω]
      exact bot_le
  calc
    μ H = ∫⁻ ω, H.indicator (fun _ => (1 : ℝ≥0∞)) ω ∂μ := by simp [hH]
    _ ≤ ∫⁻ ω, liminf (fun n => f n ω) atTop ∂μ := lintegral_mono hp
    _ ≤ liminf (fun n => ∫⁻ ω, f n ω ∂μ) atTop := lintegral_liminf_le' (fun n => (hfm n).aemeasurable)
    _ ≤ μ A*K := liminf_le_of_frequently_le (Frequently.of_forall fun n => by
      simpa only [f,lintegral_indicator ((hEm n).inter hH),lintegral_const,Measure.restrict_apply_univ,one_mul] using hb n)
end
end SLEExactGauge
end

 
section
open Set Filter MeasureTheory ProbabilityTheory Metric
open scoped Topology NNReal ENNReal
namespace SLEExactGauge
noncomputable section
attribute [local instance] Classical.propDecidable
namespace RegularSLEPresentation
variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {κ : ℝ} {γ : Ω → ℝ≥0 → ℂ} (a : RegularSLEPresentation P κ γ)
lemma source_simple_sphere_stopping (z : ℂ) (r : ℝ) :
    IsStoppingTime a.filtration (fun ω : a.samples => spatialHitTime (γ ω) z r) := by
  let X (t : ℝ≥0) (ω : a.samples) := dist (γ ω t) z-r
  have ha : Adapted a.filtration X := by
    intro t
    let : MeasurableSpace a.samples := a.filtration t
    exact ((a.trace_adapted t).dist measurable_const).sub_const _
  exact continuous_zero_hit_stopping a.filtration X ha
    (fun ω => ((a.trace_continuous ω).dist continuous_const).sub continuous_const) 0
lemma source_simple_center_before (z₀ : ℂ) (hz : 4 ≤ z₀.im) (r : ℝ) (hr : r ≤ 1)
    (ω : a.samples) (z : ℂ) (hzz : z ∈ ball z₀ 1) :
    spatialHitTime (γ ω) z₀ 2 ≤ spatialHitTime (γ ω) z r := by
  by_cases hn : spatialHitTime (γ ω) z r = ⊤
  · rw [hn]; exact le_top
  obtain ⟨t,ht⟩ := WithTop.ne_top_iff_exists.mp hn
  rw [←ht]
  have hm := spatialHitTime_mem (a.trace_continuous ω) z r t ht.symm
  have hs : 2 ≤ dist (γ ω 0) z₀ := by
    rw [(a.witness ω).2.1,dist_zero_left]
    have hh := (le_abs_self z₀.im).trans (Complex.abs_im_le_norm z₀)
    linarith
  apply (spatialHitTime_lt_of_dist_lt (a.trace_continuous ω) z₀ 2 hs t ?_).le
  have hh : dist z z₀ < 1 := hzz
  have ht' := dist_triangle (γ ω t) z z₀
  linarith
lemma source_simple_spheres_separated (z : ℂ) (hz : 4 ≤ z.im) (ω : a.samples)
    (hn : spatialHitTime (γ ω) z 3 ≠ ⊤) :
    spatialHitTime (γ ω) z 3 < spatialHitTime (γ ω) z 2 := by
  have hs : 3 ≤ dist (γ ω 0) z := by
    rw [(a.witness ω).2.1,dist_zero_left]
    have hh := (le_abs_self z.im).trans (Complex.abs_im_le_norm z)
    linarith
  apply lt_of_le_of_ne (spatialHitTime_antitone_radius (a.trace_continuous ω) z (by norm_num : (2:ℝ) ≤ 3) hs)
  intro he
  obtain ⟨t,ht⟩ := WithTop.ne_top_iff_exists.mp hn
  have h3 := spatialHitTime_mem (a.trace_continuous ω) z 3 t ht.symm
  have h2 := spatialHitTime_mem (a.trace_continuous ω) z 2 t (he.symm.trans ht.symm)
  linarith
lemma source_simple_weight_zero_no_entrance (z₀ : ℂ) (hz : 4 ≤ z₀.im) (r : ℝ) (hr : r ≤ 1)
    (ω : a.samples) (hn : spatialHitTime (γ ω) z₀ 3 = ⊤) (z : ℂ) (hzz : z ∈ ball z₀ 1) :
    spatialGreenWeight κ (fun t => Real.sqrt κ*a.B t ω) (γ ω) (a.G ω) z r = 0 := by
  unfold spatialGreenWeight
  split_ifs with hb
  · rfl
  · have hn' : spatialHitTime (γ ω) z r ≠ ⊤ := fun hh => hb hh
    obtain ⟨t,ht⟩ := WithTop.ne_top_iff_exists.mp hn'
    have hm := spatialHitTime_mem (a.trace_continuous ω) z r t ht.symm
    have hs : 3 ≤ dist (γ ω 0) z₀ := by
      rw [(a.witness ω).2.1,dist_zero_left]
      have hh := (le_abs_self z₀.im).trans (Complex.abs_im_le_norm z₀)
      linarith
    have hd : dist (γ ω t) z₀ < 3 := by
      have hh : dist z z₀ < 1 := hzz
      have ht' := dist_triangle (γ ω t) z z₀
      linarith
    have hh := spatialHitTime_lt_of_dist_lt (a.trace_continuous ω) z₀ 3 hs t hd
    rw [hn] at hh
    exact (not_lt_of_ge le_top hh).elim
end RegularSLEPresentation
end
end SLEExactGauge
end

 
section
open Set Filter MeasureTheory ProbabilityTheory Metric
open scoped Topology NNReal ENNReal
namespace SLEExactGauge
noncomputable section
namespace RegularSLEPresentation
variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {κ : ℝ} {γ : Ω → ℝ≥0 → ℂ} (a : RegularSLEPresentation P κ γ)
theorem source_past_spatial_slab_subgaussian [IsProbabilityMeasure P]
    (hκ : 0 < κ) (hκ4 : κ ≤ 4)
    (A : Set ℂ) (hA : MeasurableSet A)
    (q ε r R : ℝ) (hq : 0 < q) (hε : 0 < ε) (hqr : q*r ≤ ε)
    (hεr : ε ≤ r) (hrR : r ≤ R)
    (hheight : ∀ z ∈ A, r ≤ z.im) (hbound : ∀ z ∈ A, ‖z‖ ≤ R)
    (s : ℝ≥0) (D : Set a.samples) (hD : MeasurableSet[a.filtration s] D)
    (hbefore : ∀ ω ∈ D, ∀ z ∈ A, (s : WithTop ℝ≥0) ≤ spatialHitTime (γ ω) z r)
    :
    HasSubgaussianMGF (fun ω : a.samples => spatialSlabIncrement κ
      (fun t => Real.sqrt κ * a.B t ω) (γ ω) (a.G ω) A ε r)
      (⟨slabAmplitude κ q A * r ^ (1 - codimension κ),
        mul_nonneg (slabAmplitude_nonneg κ q A) (Real.rpow_nonneg (hε.trans_le hεr).le _)⟩ ^ 2)
      ((P.comap Subtype.val)[|D]) := by
  apply hasSubgaussianMGF_of_compensated (a.spatialSlabIncrement_measurable A ε r).aemeasurable
  intro θ
  rw [ProbabilityTheory.cond, lintegral_smul_measure]
  apply (mul_le_mul' (le_refl (((P.comap Subtype.val) D)⁻¹)) ?_).trans (ENNReal.inv_mul_le_one _)
  have hv := slabVariance_scale_le A hκ (by linarith) hq (hε.trans_le hεr) hqr
  apply le_trans _ (a.source_past_spatial_slab_terminal_exponential hκ hκ4 A hA ε r R hε hεr hrR hheight hbound s D hD hbefore θ)
  apply lintegral_mono
  intro ω
  apply ENNReal.ofReal_le_ofReal
  apply Real.exp_le_exp.mpr
  change θ * _ - θ^2 * (slabAmplitude κ q A * r ^ (1 - codimension κ))^2 / 2 ≤ _
  nlinarith [mul_le_mul_of_nonneg_left hv (sq_nonneg θ)]

end RegularSLEPresentation
end
end SLEExactGauge
end

 
section
open Set Filter MeasureTheory ProbabilityTheory Metric
open scoped Topology NNReal ENNReal
namespace SLEExactGauge
noncomputable section
namespace RegularSLEPresentation
variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {κ : ℝ} {γ : Ω → ℝ≥0 → ℂ} (a : RegularSLEPresentation P κ γ)
theorem source_past_spatial_geometric_subgaussian [IsProbabilityMeasure P]
    (hκ : 0 < κ) (hκ4 : κ ≤ 4) (A : Set ℂ) (hA : MeasurableSet A)
    (q r R : ℝ) (hq : 0 < q) (hq1 : q < 1) (hr : 0 < r) (hrR : r ≤ R)
    (hheight : ∀ z ∈ A, r ≤ z.im) (hbound : ∀ z ∈ A, ‖z‖ ≤ R) (N : ℕ)
    (s : ℝ≥0) (D : Set a.samples) (hD : MeasurableSet[a.filtration s] D)
    (hbefore : ∀ ω ∈ D, ∀ z ∈ A, (s : WithTop ℝ≥0) ≤ spatialHitTime (γ ω) z r)
    :
    HasSubgaussianMGF (fun ω : a.samples =>
      spatialRealMass κ (fun t => Real.sqrt κ*a.B t ω) (γ ω) (a.G ω) (r*q^N) A -
      spatialRealMass κ (fun t => Real.sqrt κ*a.B t ω) (γ ω) (a.G ω) r A)
      (NNReal.mk (slabAmplitude κ q A*r^(1-codimension κ)/(1-q^(1-codimension κ)))
        (div_nonneg (mul_nonneg (slabAmplitude_nonneg κ q A) (Real.rpow_nonneg hr.le _))
          (sub_nonneg.mpr (Real.rpow_lt_one hq.le hq1 (sub_pos.mpr (codimension_lt_one κ hκ))).le)) ^ 2)
      ((P.comap Subtype.val)[|D]) := by
  let rj : ℕ → ℝ := fun n => r*q^n
  have hp (n : ℕ) : 0 < rj n := mul_pos hr (pow_pos hq n)
  have hl (n : ℕ) : rj n ≤ r := by
    simpa only [mul_one] using mul_le_mul_of_nonneg_left (pow_le_one₀ (n := n) hq.le hq1.le) hr.le
  have he (n : ℕ) : rj (n+1) = q*rj n := by dsimp [rj]; rw [pow_succ]; ring
  let X : ℕ → a.samples → ℝ := fun n ω => spatialSlabIncrement κ
    (fun t => Real.sqrt κ*a.B t ω) (γ ω) (a.G ω) A (rj (n+1)) (rj n)
  let b : ℕ → ℝ≥0 := fun n => NNReal.mk (slabAmplitude κ q A*(rj n)^(1-codimension κ))
    (mul_nonneg (slabAmplitude_nonneg κ q A) (Real.rpow_nonneg (hp n).le _))
  have hsub (n : ℕ) : HasSubgaussianMGF (X n) (b n^2) ((P.comap Subtype.val)[|D]) := by
    apply a.source_past_spatial_slab_subgaussian hκ hκ4 A hA q (rj (n+1)) (rj n) R hq (hp _) (he n).symm.le (s := s) (D := D)
    · rw [he]; exact mul_le_of_le_one_left (hp n).le hq1.le
    · exact (hl n).trans hrR
    · exact fun z hz => (hl n).trans (hheight z hz)
    · exact hbound
    · exact hD
    · intro ω hω z hz
      apply (hbefore ω hω z hz).trans
      apply spatialHitTime_antitone_radius (a.trace_continuous ω) z (hl n)
      rw [(a.witness ω).2.1,dist_zero_left]
      exact (hheight z hz).trans ((le_abs_self z.im).trans (Complex.abs_im_le_norm z))
  have hsum := subgaussian_sum_amplitudes X b N (fun n _ => hsub n)
  have hfin : volume A ≠ ∞ := (measure_mono (show A ⊆ Metric.closedBall 0 R from
    fun z hz => by simpa only [Metric.mem_closedBall, dist_zero_right] using hbound z hz)).trans_lt
      (measure_closedBall_lt_top (μ := volume) (x := (0 : ℂ)) (r := R)) |>.ne
  have htel (ω : a.samples) : (∑ n ∈ Finset.range N, X n ω) =
      spatialRealMass κ (fun t => Real.sqrt κ*a.B t ω) (γ ω) (a.G ω) (r*q^N) A -
      spatialRealMass κ (fun t => Real.sqrt κ*a.B t ω) (γ ω) (a.G ω) r A := by
    have hm (n : ℕ) : X n ω =
        spatialRealMass κ (fun t => Real.sqrt κ*a.B t ω) (γ ω) (a.G ω) (rj (n+1)) A -
        spatialRealMass κ (fun t => Real.sqrt κ*a.B t ω) (γ ω) (a.G ω) (rj n) A := by
      symm
      apply a.spatialRealMass_sub_eq_slab hκ (by linarith) A hA hfin _ _ (hp _)
      · rw [he]; exact mul_le_of_le_one_left (hp n).le hq1.le
      · exact fun z hz => (hl n).trans (hheight z hz)
    simp_rw [hm]
    simpa only [rj, pow_zero, mul_one] using Finset.sum_range_sub
      (fun n => spatialRealMass κ (fun t => Real.sqrt κ*a.B t ω) (γ ω) (a.G ω) (rj n) A) N
  simp_rw [htel] at hsum
  apply SLEExactGauge.HasSubgaussianMGF.mono_parameter hsum
  apply pow_le_pow_left₀ (by positivity)
  apply NNReal.coe_le_coe.mp
  simpa only [NNReal.coe_sum, b, rj, NNReal.coe_mk] using geometric_amplitude_sum (slabAmplitude κ q A) r q (1-codimension κ)
    (slabAmplitude_nonneg κ q A) hr hq hq1 (sub_pos.mpr (codimension_lt_one κ hκ)) N

end RegularSLEPresentation
end
end SLEExactGauge
end

 
end
end
end

end OAI
