import OAI.MathematicalPhysics.Boltzmann.Branching.TranslatedCoreKernel
import OAI.MathematicalPhysics.Boltzmann.Branching.TwoCoreLimit
import OAI.MathematicalPhysics.Boltzmann.Collision.AxialBandMeasure
import OAI.MathematicalPhysics.Boltzmann.Collision.AxialSecondMismatch
import OAI.MathematicalPhysics.Boltzmann.Jets.CoreDensityTranslation
import OAI.MathematicalPhysics.Boltzmann.Jets.FreeCoreMismatch
import OAI.MathematicalPhysics.Boltzmann.Jets.JetCoreConvergence

namespace OAI

section

/-! # Exact measure representation of the dilated cold core

The masks stay at their original physical scale. Dilation is carried by the
measure factor and the time/position arguments, without identifying masks.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
open BoltzmannNonuniqueness.VelocityWeight

namespace BoltzmannNonuniqueness.ChartKernel

theorem inputKernel_smul_base {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (c : Kernel X Velocity) (d : Kernel Y Velocity) [IsSFiniteKernel c] [IsSFiniteKernel d]
    {x : X} {y : Y} {a : ℝ≥0∞} (h : c x = a • d y) (q : ℝ) (v : Velocity) :
    inputKernel c q (x,v) = a • inputKernel d q (y,v) := by
  change (coordinateKernel c q (x,v)).map _ = a • (coordinateKernel d q (y,v)).map _
  rw [coordinateKernel_apply,coordinateKernel_apply]
  unfold normalizedMeasure
  rw [h,measure_smul,Measure.map_smul]
  exact (measurable_point v).aemeasurable

end BoltzmannNonuniqueness.ChartKernel

namespace BoltzmannNonuniqueness.JetCoreSheet

def rescaledCoreMeasure (r η K α γ μ d q : ℝ) (sign : Bool)
    (t : ℝ) (x : JetPrototype.Space) (v : Velocity) : Measure Velocity :=
  ENNReal.ofReal r • ChartKernel.offAxis
    (normalizedCoreKernel η K α γ (r*μ) d q sign) ((r*t,r • x),v)

theorem amplitude_dilation {r : ℝ} (hr : r ≠ 0) (K α γ μ t : ℝ) :
    r*amplitude K α γ (r*μ) (r*t) = amplitude K α γ μ t := by
  unfold amplitude
  rw [show r*μ+r*t = r*(μ+t) by ring]
  by_cases h : μ+t = 0
  · simp [h]
  · field_simp

theorem rescaledCoreMeasure_axis (r η K α γ μ d q : ℝ) (sign : Bool)
    (t : ℝ) (x : JetPrototype.Space) {v : Velocity} (hv : transverse v = 0) :
    rescaledCoreMeasure r η K α γ μ d q sign t x v = 0 := by
  unfold rescaledCoreMeasure
  rw [ChartKernel.offAxis_axis _ _ hv,smul_zero]

theorem dilatedFreeKernel_eq_rescaled {r : ℝ} (hr : 0 < r)
    (η K α γ s d q : ℝ) (sign : Bool) (z : Published.KineticPhase) :
    dilatedFreeKernel r η K α γ s d q sign z =
      rescaledCoreMeasure r η K α γ (s/r) d q sign z.1.1
        (JetPeriodicDatum.spatialMap z.1.2) z.2 := by
  have hs : r*(s/r) = s := by field_simp
  have hx : JetPeriodicDatum.spatialMap (r • z.1.2) =
      r • JetPeriodicDatum.spatialMap z.1.2 := by
    ext i <;> rfl
  by_cases hv : transverse z.2 = 0
  · rw [dilatedFreeKernel,ChartKernel.offAxis_axis _ _ hv,
      rescaledCoreMeasure_axis _ _ _ _ _ _ _ _ _ _ _ hv]
  · rw [dilatedFreeKernel,ChartKernel.offAxis_apply _ z hv,rescaledCoreMeasure,
      ChartKernel.offAxis_apply _ ((r*z.1.1,r • JetPeriodicDatum.spatialMap z.1.2),z.2) hv,hs]
    have h := ChartKernel.inputKernel_smul_base
      (dilatedColdKernel r η K α γ s d sign) (coreKernel η K α γ s d sign)
      (x := z.1) (y := (r*z.1.1,r • JetPeriodicDatum.spatialMap z.1.2))
      (a := ENNReal.ofReal r) ?_ q z.2
    · exact h
    · rw [dilatedColdKernel_apply]
      change ENNReal.ofReal r • coreKernel η K α γ s d sign
        (r*z.1.1,JetPeriodicDatum.spatialMap (r • z.1.2)) = _
      rw [hx]

theorem rescaled_region_le {r K α γ μ d t q : ℝ} (hr : 0 < r) (η : ℝ) (sign : Bool)
    (x : JetPrototype.Space) {v : Velocity} (hv : transverse v ≠ 0)
    (E : Set Velocity) {B : ℝ≥0∞}
    (hbound : normalizedCoreKernel η K α γ (r*μ) d q sign ((r*t,r • x),v) E ≤
      ENNReal.ofReal (amplitude K α γ (r*μ) (r*t))*B) :
    rescaledCoreMeasure r η K α γ μ d q sign t x v E ≤
      ENNReal.ofReal (amplitude K α γ μ t)*B := by
  rw [rescaledCoreMeasure,ChartKernel.offAxis_apply _ _ hv,Measure.smul_apply,smul_eq_mul]
  calc
    _ ≤ ENNReal.ofReal r*(ENNReal.ofReal (amplitude K α γ (r*μ) (r*t))*B) :=
      mul_le_mul' le_rfl hbound
    _ = _ := by
      rw [← mul_assoc,← ENNReal.ofReal_mul hr.le,amplitude_dilation hr.ne']

end BoltzmannNonuniqueness.JetCoreSheet

end

end

section

/-! # Dilation-uniform mass, interval, transverse and mismatch estimates -/

noncomputable section

open MeasureTheory Set
open scoped ENNReal
open BoltzmannNonuniqueness.VelocityWeight BoltzmannNonuniqueness.AxialFlow

namespace BoltzmannNonuniqueness.JetCoreSheet

theorem rescaled_mass_bound {r K α γ μ d t q : ℝ} (hr : 0 < r) (hK : 0 ≤ K)
    (hα : 0 < α) (hγ : 0 < γ) (hμ : 0 < μ) (hd : 0 < d) (hdmax : d ≤ 1/16)
    (ht : 0 < t) (hq₁ : 1 < q) (hq₂ : q < 2) (η : ℝ) (sign : Bool)
    (x : JetPrototype.Space) (v : Velocity) :
    rescaledCoreMeasure r η K α γ μ d q sign t x v univ ≤
      ENNReal.ofReal (growthConstant K α γ q/t) := by
  rw [rescaledCoreMeasure,Measure.smul_apply,smul_eq_mul]
  calc
    _ ≤ ENNReal.ofReal r*ENNReal.ofReal (growthConstant K α γ q/(r*t)) :=
      mul_le_mul' le_rfl (offAxisCoreKernel_time_bound hK hα hγ (mul_pos hr hμ)
        hd hdmax (mul_pos hr ht) hq₁ hq₂ η sign _ _)
    _ = _ := by
      rw [← ENNReal.ofReal_mul hr.le]
      congr 1
      field_simp

theorem rescaled_axial_bands {α q ε : ℝ} (hq₁ : 1 < q) (hq₂ : q < 2) (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ {r K γ μ d t : ℝ}, 0 < r → 0 ≤ K → 0 < α → 0 < γ →
      0 < μ → 0 < d → d ≤ 1/16 → 0 ≤ t → ∀ (η : ℝ) (sign : Bool)
      (x : JetPrototype.Space) (v : Velocity) (S : Finset ℝ),
      rescaledCoreMeasure r η K α γ μ d q sign t x v (axial ⁻¹' bands S δ) ≤
        S.card*(ENNReal.ofReal (amplitude K α γ μ t)*ENNReal.ofReal ε) := by
  obtain ⟨δ,hδ,hb⟩ := core_axial_bands (α := α) hq₁ hq₂ hε
  refine ⟨δ,hδ,?_⟩
  intro r K γ μ d t hr hK hα hγ hμ hd hdmax ht η sign x v S
  by_cases hv : transverse v = 0
  · rw [rescaledCoreMeasure_axis _ _ _ _ _ _ _ _ _ _ _ hv]
    simp
  have h := hb hK hα hγ (mul_pos hr hμ) hd hdmax (mul_nonneg hr.le ht) η sign (r • x) v hv S
  have h' := rescaled_region_le hr η sign x hv (axial ⁻¹' bands S δ)
    (B := S.card*ENNReal.ofReal ε) (h.trans_eq (by ring))
  exact h'.trans_eq (by ring)

theorem rescaled_axis_input {α q b ε : ℝ} (hq₁ : 1 < q) (hq₂ : q < 2)
    (hb : 0 < b) (hε : 0 < ε) :
    ∃ r₀ : ℝ, 0 < r₀ ∧ ∀ {r K γ μ d t : ℝ}, 0 < r → 0 ≤ K → 0 < α → 0 < γ →
      0 < μ → 0 < d → d ≤ 1/16 → 0 ≤ t → ∀ (η : ℝ) (sign : Bool)
      (x : JetPrototype.Space) (v : Velocity), ‖transverse v‖ ≤ r₀ →
      rescaledCoreMeasure r η K α γ μ d q sign t x v {w | b ≤ ‖transverse w‖} ≤
        ENNReal.ofReal (amplitude K α γ μ t)*ENNReal.ofReal ε := by
  obtain ⟨r₀,hr₀,hb⟩ := core_axis_input (α := α) hq₁ hq₂ hb hε
  refine ⟨r₀,hr₀,?_⟩
  intro r K γ μ d t hr hK hα hγ hμ hd hdmax ht η sign x v hvr
  by_cases hv : transverse v = 0
  · rw [rescaledCoreMeasure_axis _ _ _ _ _ _ _ _ _ _ _ hv]
    simp
  apply rescaled_region_le hr η sign x hv
  rw [inputKernel_region sign (r*t,r • x) v
    (show MeasurableSet {w : Velocity | b ≤ ‖transverse w‖} from
      measurableSet_le measurable_const ChartKernel.measurable_transverse.norm)]
  exact hb hK hα hγ (mul_pos hr hμ) hd hdmax (mul_nonneg hr.le ht) η sign (r • x) v hv hvr

theorem rescaled_speed_gap {α q δ ε : ℝ} (hq₁ : 1 < q) (hq₂ : q < 2)
    (hδ : 0 < δ) (hε : 0 < ε) :
    ∃ r₀ : ℝ, 0 < r₀ ∧ ∀ {r K γ μ d t : ℝ}, 0 < r → 0 ≤ K → 0 < α → 0 < γ →
      0 < μ → 0 < d → d ≤ 1/16 → 0 ≤ t → ∀ (η : ℝ) (sign : Bool)
      (x : JetPrototype.Space) (v : Velocity), ‖transverse v‖ ≤ r₀ →
      δ+d ≤ |axial v-velocity (JetPrototype.sign sign) α γ μ t x.2| →
      rescaledCoreMeasure r η K α γ μ d q sign t x v univ ≤
        ENNReal.ofReal (amplitude K α γ μ t)*ENNReal.ofReal ε := by
  obtain ⟨r₀,hr₀,hb⟩ := core_mass_small_of_speed_gap (α := α) hq₁ hq₂ hδ hε
  refine ⟨r₀,hr₀,?_⟩
  intro r K γ μ d t hr hK hα hγ hμ hd hdmax ht η sign x v hvr hgap
  by_cases hv : transverse v = 0
  · rw [rescaledCoreMeasure_axis _ _ _ _ _ _ _ _ _ _ _ hv]
    simp
  apply rescaled_region_le hr η sign x hv
  apply hb hK hα hγ (mul_pos hr hμ) hd hdmax (mul_nonneg hr.le ht) η sign (r • x) v hv hvr
  change δ+d ≤ |axial v-velocity (JetPrototype.sign sign) α γ (r*μ) (r*t) (r*x.2)|
  rwa [velocity_dilation hr hα.le hγ.le hμ ht]

end BoltzmannNonuniqueness.JetCoreSheet

end

end

section

/-! # Uniform exceptional-region bounds for dilated cores on a positive slab -/

noncomputable section

open MeasureTheory Set
open scoped ENNReal
open BoltzmannNonuniqueness.VelocityWeight BoltzmannNonuniqueness.AxialFlow

namespace BoltzmannNonuniqueness.JetCoreSheet

/-- The radius is uniform in the interval centers, core scale, and thermal width. -/
theorem rescaled_bands_small_of_card {K α γ q a ε : ℝ} (hK : 0 ≤ K)
    (hα : 0 < α) (hγ : 0 < γ) (hq₁ : 1 < q) (hq₂ : q < 2)
    (ha : 0 < a) (hε : 0 < ε) (N : ℕ) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ {r s d t : ℝ}, 0 < r → 0 < s → 0 < d → d ≤ 1/16 → a ≤ t →
      ∀ (η : ℝ) (sign : Bool) (x : JetPrototype.Space) (v : Velocity) (S : Finset ℝ),
      S.card ≤ N →
      rescaledCoreMeasure r η K α γ s d q sign t x v
        (axial ⁻¹' bands S δ) ≤ ENNReal.ofReal ε := by
  let A := slabAmplitude K α γ a
  have hA : 0 ≤ A := slabAmplitude_nonneg hK ha α γ
  let T : ℝ := ((N : ℝ)+1)*(A+1)
  have hT : 0 < T := by dsimp [T]; positivity
  have he : 0 < ε/T := div_pos hε hT
  obtain ⟨δ,hδ,hband⟩ := rescaled_axial_bands (α := α) hq₁ hq₂ he
  refine ⟨δ,hδ,?_⟩
  intro r s d t hr hs hd hdmax ht η sign x v S hS
  have hb := hband hr hK hα hγ hs hd hdmax (ha.le.trans ht) η sign x v S
  have hcard : (S.card : ℝ) ≤ N := by exact_mod_cast hS
  have hcoef : (S.card : ℝ)*amplitude K α γ s t ≤ T := by
    have hi := mul_le_mul hcard (amplitude_le_slab hK ha hs ht α γ)
      (amplitude_nonneg hK hs (ha.le.trans ht) α γ) (Nat.cast_nonneg N)
    dsimp only [A] at hA
    have hNA : (N : ℝ)*A ≤ T := by dsimp [T]; nlinarith [show (0 : ℝ) ≤ N from Nat.cast_nonneg N]
    exact hi.trans hNA
  calc
    _ ≤ _ := hb
    _ = ENNReal.ofReal ((S.card : ℝ)*amplitude K α γ s t*(ε/T)) := by
      rw [← ENNReal.ofReal_mul (amplitude_nonneg hK hs (ha.le.trans ht) α γ),
        ← ENNReal.ofReal_natCast,← ENNReal.ofReal_mul (Nat.cast_nonneg S.card)]
      congr 1
      ring
    _ ≤ ENNReal.ofReal (T*(ε/T)) :=
      ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right hcoef he.le)
    _ = ENNReal.ofReal ε := by rw [mul_div_cancel₀ _ hT.ne']


theorem rescaled_away_small_of_transverse {K α γ q a b ε : ℝ} (hK : 0 ≤ K)
    (hα : 0 < α) (hγ : 0 < γ) (hq₁ : 1 < q) (hq₂ : q < 2)
    (ha : 0 < a) (hb : 0 < b) (hε : 0 < ε) :
    ∃ r₀ : ℝ, 0 < r₀ ∧ ∀ {r s d t : ℝ}, 0 < r → 0 < s → 0 < d → d ≤ 1/16 → a ≤ t →
      ∀ (η : ℝ) (sign : Bool) (x : JetPrototype.Space) (v : Velocity),
      ‖transverse v‖ ≤ r₀ →
      rescaledCoreMeasure r η K α γ s d q sign t x v
        {w | b ≤ ‖transverse w‖} ≤ ENNReal.ofReal ε := by
  let A := slabAmplitude K α γ a
  have hA : 0 ≤ A := slabAmplitude_nonneg hK ha α γ
  have he : 0 < ε/(A+1) := div_pos hε (by positivity)
  obtain ⟨r₀,hr₀,haway⟩ := rescaled_axis_input (α := α) hq₁ hq₂ hb he
  refine ⟨r₀,hr₀,?_⟩
  intro r s d t hr hs hd hdmax ht η sign x v hvr
  apply (haway hr hK hα hγ hs hd hdmax (ha.le.trans ht) η sign x v hvr).trans
  rw [← ENNReal.ofReal_mul (amplitude_nonneg hK hs (ha.le.trans ht) α γ)]
  apply ENNReal.ofReal_le_ofReal
  have hcoef := amplitude_le_slab hK ha hs ht α γ
  have hprod : (A+1)*(ε/(A+1)) = ε := by field_simp
  calc
    _ ≤ (A+1)*(ε/(A+1)) :=
      mul_le_mul_of_nonneg_right (hcoef.trans (by change A ≤ A+1; linarith)) he.le
    _ = _ := hprod


end BoltzmannNonuniqueness.JetCoreSheet

end

end

section

/-! # Small near-axis input mass for the actual thin dilated cores -/

noncomputable section

open MeasureTheory Set
open scoped ENNReal
open BoltzmannNonuniqueness.VelocityWeight

namespace BoltzmannNonuniqueness.JetCoreSheet

theorem rescaled_small_input {K α γ q a b ε : ℝ} (hK : 0 ≤ K)
    (hα : 0 < α) (hγ : 0 < γ) (hq₁ : 1 < q) (hq₂ : q < 2)
    (ha : 0 < a) (hb : 0 < b) (hε : 0 < ε) :
    ∃ δ θ : ℝ, 0 < δ ∧ 0 < θ ∧ ∀ {r s d t : ℝ},
      0 < r → 0 < s → 0 < d → d ≤ 1/16 → d ≤ θ → a ≤ t →
      ∀ (η : ℝ) (sign : Bool) (x : JetPrototype.Space) (v : Velocity),
      b ≤ ‖transverse v‖ →
      rescaledCoreMeasure r η K α γ s d q sign t x v
        {w | ‖transverse w‖ < δ} ≤ ENNReal.ofReal ε := by
  let A := slabAmplitude K α γ a
  have hA : 0 ≤ A := slabAmplitude_nonneg hK ha α γ
  have he : 0 < ε/(A+1) := div_pos hε (by positivity)
  obtain ⟨δ,θ,hδ,hθ,hsmall⟩ := core_small_input (α := α) hq₁ hq₂ hb he
  refine ⟨δ,θ,hδ,hθ,?_⟩
  intro r s d t hr hs hd hdmax hdθ ht η sign x v hv
  have hvne : transverse v ≠ 0 := norm_pos_iff.mp (hb.trans_le hv)
  have hmass := hsmall hK hα hγ (mul_pos hr hs) hd hdmax hdθ
    (mul_nonneg hr.le (ha.le.trans ht)) η sign (r • x) v hv
  have hbound : normalizedCoreKernel η K α γ (r*s) d q sign ((r*t,r • x),v)
      {w | ‖transverse w‖ < δ} ≤
      ENNReal.ofReal (amplitude K α γ (r*s) (r*t))*ENNReal.ofReal (ε/(A+1)) := by
    rw [inputKernel_region sign (r*t,r • x) v
      (measurableSet_lt ChartKernel.measurable_transverse.norm measurable_const)]
    exact hmass
  apply (rescaled_region_le hr η sign x hvne _ hbound).trans
  rw [← ENNReal.ofReal_mul (amplitude_nonneg hK hs (ha.le.trans ht) α γ)]
  apply ENNReal.ofReal_le_ofReal
  calc
    _ ≤ (A+1)*(ε/(A+1)) := mul_le_mul_of_nonneg_right
      ((amplitude_le_slab hK ha hs ht α γ).trans (by change A ≤ A+1; linarith)) he.le
    _ = ε := by field_simp

end BoltzmannNonuniqueness.JetCoreSheet

end

end

section

/-! # Axial core decay with constants independent of the dilation -/

noncomputable section

open MeasureTheory Set
open scoped ENNReal
open BoltzmannNonuniqueness.VelocityWeight

namespace BoltzmannNonuniqueness.JetCoreSheet

theorem rescaled_axial_decay {r K α γ μ d t T M Z q : ℝ}
    (hr : 0 < r) (hK : 0 ≤ K) (hα : 0 ≤ α) (hγ : 0 < γ) (hμ : 0 < μ)
    (hd : 0 < d) (hdmax : d ≤ 1/16) (ht : 0 ≤ t) (htT : t ≤ T)
    (hM : μ ≤ M) (hZ : 0 < Z) (hq₁ : 1 < q) (hq₂ : q < 2)
    (η : ℝ) (a : Bool) (x : JetPrototype.Space) (hx : Z+T*(α+2) ≤ |x.2|)
    (v : Velocity) :
    rescaledCoreMeasure r η K α γ μ d q a t x v univ ≤
      ENNReal.ofReal ((4*K*M/(γ^2*Z^2))*JetGaussianProduct.coefficient)*
        SheetTotal.bound q (2*Real.exp (16*(1+α)^2)) := by
  by_cases hv : transverse v = 0
  · rw [rescaledCoreMeasure_axis _ _ _ _ _ _ _ _ _ _ _ hv]
    simp
  have hx' : r*Z+(r*T)*(α+2) ≤ |(r • x).2| := by
    change r*Z+(r*T)*(α+2) ≤ |r*x.2|
    rw [abs_mul,abs_of_pos hr]
    nlinarith
  have h := normalized_core_axial_decay hK hα hγ (mul_pos hr hμ) hd hdmax
    (mul_nonneg hr.le ht) (mul_le_mul_of_nonneg_left htT hr.le)
    (mul_le_mul_of_nonneg_left hM hr.le) (mul_pos hr hZ) hq₁ hq₂ η a (r • x) hx' hv
  rw [rescaledCoreMeasure,ChartKernel.offAxis_apply _ _ hv,Measure.smul_apply,smul_eq_mul]
  apply (mul_le_mul' le_rfl h).trans_eq
  rw [← mul_assoc,← ENNReal.ofReal_mul hr.le]
  have he : r*((4*K*(r*M)/(γ^2*(r*Z)^2))*JetGaussianProduct.coefficient) =
      (4*K*M/(γ^2*Z^2))*JetGaussianProduct.coefficient := by
    field_simp
  rw [he]

end BoltzmannNonuniqueness.JetCoreSheet

end

end

section

/-! # Uniform decay of dilated core mass at large outgoing velocities -/

noncomputable section

open MeasureTheory Set
open scoped ENNReal
open BoltzmannNonuniqueness.VelocityWeight

namespace BoltzmannNonuniqueness.JetCoreSheet

theorem rescaled_large_output {K α γ q a ε : ℝ} (hK : 0 ≤ K)
    (hα : 0 < α) (hγ : 0 < γ) (hq₁ : 1 < q) (hq₂ : q < 2)
    (ha : 0 < a) (hε : 0 < ε) :
    ∃ R : ℝ, 0 < R ∧ ∀ {r μ d t : ℝ}, 0 < r → 0 < μ → 0 < d →
      d ≤ 1/16 → a ≤ t → ∀ (η : ℝ) (sign : Bool) (x : JetPrototype.Space) (v : Velocity),
      R < ‖v‖ → rescaledCoreMeasure r η K α γ μ d q sign t x v univ ≤ ENNReal.ofReal ε := by
  let A := slabAmplitude K α γ a
  have hA : 0 ≤ A := slabAmplitude_nonneg hK ha α γ
  have he : 0 < ε/(A+1) := div_pos hε (by positivity)
  obtain ⟨R,hR,hb⟩ := core_large_output (α := α) hq₁ hq₂ he
  refine ⟨R,hR,?_⟩
  intro r μ d t hr hμ hd hdmax ht η sign x v hv
  by_cases haxis : transverse v = 0
  · rw [rescaledCoreMeasure_axis _ _ _ _ _ _ _ _ _ _ _ haxis]
    simp
  have h := hb hK hα hγ (mul_pos hr hμ) hd hdmax
    (mul_nonneg hr.le (ha.le.trans ht)) η sign (r • x) v haxis hv
  apply (rescaled_region_le hr η sign x haxis univ h).trans
  rw [← ENNReal.ofReal_mul (amplitude_nonneg hK hμ (ha.le.trans ht) α γ)]
  apply ENNReal.ofReal_le_ofReal
  calc
    _ ≤ (A+1)*(ε/(A+1)) := mul_le_mul_of_nonneg_right
      ((amplitude_le_slab hK ha hμ ht α γ).trans (by change A ≤ A+1; linarith)) he.le
    _ = ε := by field_simp

end BoltzmannNonuniqueness.JetCoreSheet

end

end

section

/-! # The dilated Gaussian core remainder has uniformly vanishing gain -/

noncomputable section

open MeasureTheory Filter
open scoped ENNReal Topology
open BoltzmannNonuniqueness.VelocityWeight

namespace BoltzmannNonuniqueness.JetRemainderSheet

theorem uniformConstant_nonneg {K : ℝ} (hK : 0 ≤ K) : 0 ≤ uniformConstant K := by
  have := JetComparisonCoefficient.coefficient_ge_one hK
  have := JetThermalKernel.bound_pos
  unfold uniformConstant
  positivity

theorem thermal_amplitude_bound {K s d₀ t : ℝ} (hK : 0 ≤ K) (hs : 0 < s) (hsmax : s ≤ 1)
    (hd₀ : 0 < d₀) (hdmax : d₀ ≤ 1) (ht : 0 < t) (htmax : t ≤ 1)
    (η α γ : ℝ) (sign : Bool) (x : JetPrototype.Space) :
    amplitude η K α γ s (d₀*s^10) t sign x ≤ uniformConstant K := by
  apply (amplitude_bound hK hs (by positivity) ht htmax η α γ sign x).trans
  have hpower : s^8 ≤ 1 := pow_le_one₀ hs.le hsmax
  have hsmall : d₀*s^10/s^2 ≤ 1 := by
    have he : d₀*s^10/s^2 = d₀*s^8 := by field_simp
    rw [he]
    exact (mul_le_mul hdmax hpower (pow_nonneg hs.le _) (by norm_num)).trans_eq (by ring)
  simpa only [mul_one] using mul_le_mul_of_nonneg_left hsmall (uniformConstant_nonneg hK)

theorem dilated_gain_bound {K α γ s d₀ t q : ℝ} (hK : 0 ≤ K) (hα : 0 ≤ α)
    (hs : 0 < s) (hsmax : s ≤ 1) (hd₀ : 0 < d₀) (hdmax : d₀ ≤ 1)
    (hwidth : d₀*s^10 ≤ 1/16) (ht : 0 < t) (htmax : t ≤ 1)
    (hq₁ : 1 < q) (hq₂ : q < 2) (r η : ℝ) (sign : Bool) (x : JetPrototype.Space)
    {v : Velocity} (hv : transverse v ≠ 0) :
    normalizedChartGain
      (ENNReal.ofReal r • volume.withDensity
        (fun p => ENNReal.ofReal (remainder η K α γ s (d₀*s^10) t sign x p))) q v ≤
      ENNReal.ofReal r*(ENNReal.ofReal (uniformConstant K)*
        SheetTotal.bound q (2*Real.exp (16*(1+α)^2))) := by
  change chartGain _ _ _ ≤ _
  rw [chartGain_smul_measure]
  apply mul_le_mul' le_rfl
  exact (normalized_gain_bound hK hα hs (by positivity) hwidth htmax hq₁ hq₂ η sign x hv).trans
    (mul_le_mul' (ENNReal.ofReal_le_ofReal
      (thermal_amplitude_bound hK hs hsmax hd₀ hdmax ht htmax η α γ sign x)) le_rfl)

theorem remainder_gain_majorant_tendsto_zero {K α q : ℝ} {r : ℕ → ℝ}
    (hr : Tendsto r atTop (𝓝 0)) :
    Tendsto (fun n => ENNReal.ofReal (r n)*(ENNReal.ofReal (uniformConstant K)*
      SheetTotal.bound q (2*Real.exp (16*(1+α)^2)))) atTop (𝓝 0) := by
  have h := ENNReal.continuous_ofReal.continuousAt.tendsto.comp hr
  have hf : ENNReal.ofReal (uniformConstant K)*
      SheetTotal.bound q (2*Real.exp (16*(1+α)^2)) ≠ ∞ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top (SheetTotal.bound_lt_top _ _).ne
  simpa only [Function.comp_def,ENNReal.ofReal_zero,zero_mul] using ENNReal.Tendsto.mul_const h (Or.inr hf)

end BoltzmannNonuniqueness.JetRemainderSheet

end

end

section

/-! # Uniform velocity tails for dilated cores with bounded outgoing velocity -/

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal Topology
open BoltzmannNonuniqueness.VelocityWeight

namespace BoltzmannNonuniqueness.JetCoreSheet

theorem rescaled_velocity_tail {K α γ q a V ε : ℝ} (hK : 0 ≤ K)
    (hα : 0 < α) (hγ : 0 < γ) (hq₁ : 1 < q) (hq₂ : q < 2)
    (ha : 0 < a) (hV : 0 ≤ V) (hε : 0 < ε) :
    ∃ R : ℝ, 0 < R ∧ ∀ {r s d t : ℝ}, 0 < r → 0 < s → 0 < d →
      d ≤ 1/16 → a ≤ t → ∀ (η : ℝ) (sign : Bool) (x : JetPrototype.Space) (v : Velocity),
      ‖v‖ ≤ V → rescaledCoreMeasure r η K α γ s d q sign t x v {w | R < ‖w‖} ≤
        ENNReal.ofReal ε := by
  let A := slabAmplitude K α γ a
  have hA : 0 ≤ A := slabAmplitude_nonneg hK ha α γ
  have he : 0 < ε/(A+1) := div_pos hε (by positivity)
  obtain ⟨N,hN⟩ := eventually_atTop.mp
    ((SheetTightness.tendsto_tailBound q (2*Real.exp (16*(1+α)^2))).eventually
      (gt_mem_nhds (ENNReal.ofReal_pos.mpr he)))
  refine ⟨V+2*(N+1),by positivity,?_⟩
  intro r s d t hr hs hd hdmax ht η sign x v hv
  by_cases haxis : transverse v = 0
  · rw [rescaledCoreMeasure_axis _ _ _ _ _ _ _ _ _ _ _ haxis]
    simp
  have hb : normalizedCoreKernel η K α γ (r*s) d q sign ((r*t,r • x),v)
      {w | V+2*(N+1) < ‖w‖} ≤
      ENNReal.ofReal (amplitude K α γ (r*s) (r*t))*ENNReal.ofReal (ε/(A+1)) := by
    rw [inputKernel_region sign (r*t,r • x) v
      (measurableSet_lt measurable_const measurable_norm)]
    apply (measure_mono (show
      (fun y => PlaneChart.chart v y.1 y.2.1 y.2.2) ⁻¹' {w | V+2*(N+1) < ‖w‖} ⊆
        SheetTightness.tailRegion v N from ?_)).trans
      ((core_tail_bound hK hα hγ (mul_pos hr hs) hd hdmax
        (mul_nonneg hr.le (ha.le.trans ht)) hq₁ hq₂ η sign (r • x) haxis N).trans ?_)
    · intro y hy
      change V+2*(N+1) < ‖PlaneChart.chart v y.1 y.2.1 y.2.2‖ at hy
      have hn := norm_sub_norm_le (PlaneChart.chart v y.1 y.2.1 y.2.2) v
      change 2*((N : ℝ)+1) < ‖y.1‖+‖PlaneChart.chart v y.1 y.2.1 y.2.2-v‖
      have hp := norm_nonneg y.1
      linarith
    · have hsign : |JetPrototype.sign sign| = 1 := by cases sign <;> norm_num [JetPrototype.sign]
      rw [hsign]
      exact mul_le_mul' le_rfl (hN N le_rfl).le
  apply (rescaled_region_le hr η sign x haxis _ hb).trans
  rw [← ENNReal.ofReal_mul (amplitude_nonneg hK hs (ha.le.trans ht) α γ)]
  apply ENNReal.ofReal_le_ofReal
  calc
    _ ≤ (A+1)*(ε/(A+1)) := mul_le_mul_of_nonneg_right
      ((amplitude_le_slab hK ha hs ht α γ).trans (by change A ≤ A+1; linarith)) he.le
    _ = ε := by field_simp

end BoltzmannNonuniqueness.JetCoreSheet

end

end

section

/-! # The second actual core is small outside the finite exceptional speed list -/

noncomputable section

open MeasureTheory Set
open scoped ENNReal
open BoltzmannNonuniqueness.VelocityWeight BoltzmannNonuniqueness.AxialFlow

namespace BoltzmannNonuniqueness.JetCoreSheet

theorem rescaled_second_core_small_off_bands {α γ q a δ : ℝ}
    (hα : 0 < α) (hγ : 0 < γ) (hq₁ : 1 < q) (hq₂ : q < 2)
    (ha : 0 < a) (hδ : 0 < δ) :
    ∃ μ₀ : ℝ, 0 < μ₀ ∧ ∀ b : ℝ, 0 < b → ∀ ε : ℝ, 0 < ε →
      ∃ r₀ : ℝ, 0 < r₀ ∧ ∀ {r K s d t₁ t₂ z : ℝ},
      0 < r → 0 ≤ K → 0 < s → 0 < d → d ≤ 1/16 → d ≤ min δ b/4 → a ≤ t₂ → t₂ ≤ t₁ →
      ∀ (η : ℝ) (sign : Bool) (y : Transverse) (v : Velocity) (S : Finset ℝ),
      (μ₀ ≤ s → s ∈ S) → ‖transverse v‖ ≤ r₀ →
      axial v ∉ bands (collapsedCenters α t₁ z) δ →
      axial v ∉ bands (profileCenters α γ t₁ z S) b →
      rescaledCoreMeasure r η K α γ s d q sign t₂ (y,z-(t₁-t₂)*axial v) v univ ≤
        ENNReal.ofReal (amplitude K α γ s t₂)*ENNReal.ofReal ε := by
  obtain ⟨μ₀,hμ₀,hsmall⟩ := outside_collapsedBands_second_gap hα hγ ha hδ
  refine ⟨μ₀,hμ₀,?_⟩
  intro b hb ε hε
  have hc : 0 < min δ b/4 := div_pos (lt_min hδ hb) (by norm_num)
  obtain ⟨r₀,hr₀,hcore⟩ := rescaled_speed_gap (α := α) hq₁ hq₂ hc hε
  refine ⟨r₀,hr₀,?_⟩
  intro r K s d t₁ t₂ z hr hK hs hd hdmax hdc ht₂ htt η sign y v S hS hvr hcollapsed hprofile
  apply hcore hr hK hα hγ hs hd hdmax (ha.le.trans ht₂) η sign
    (y,z-(t₁-t₂)*axial v) v hvr
  have hsign : JetPrototype.sign sign = 1 ∨ JetPrototype.sign sign = -1 := by
    cases sign <;> simp [JetPrototype.sign]
  have hbound : min δ b/4+d ≤ min δ b/2 := by linarith
  by_cases hss : s < μ₀
  · have hg := hsmall (JetPrototype.sign sign) s 0 t₁ t₂ z (axial v) 0
      hsign hs hss ht₂ htt (by simpa using div_pos hδ (by norm_num : (0:ℝ)<4)) hcollapsed
    simp only [JetCoreMap.axialMap,mul_zero,zero_add,sub_zero] at hg
    exact hbound.trans ((by linarith [min_le_left δ b] : min δ b/2 ≤ δ/2).trans hg)
  · have hg := outside_profileBands_second_gap (b := b) (w := axial v)
      hα.le hγ.le hs (ha.le.trans ht₂) htt
      S (hS (le_of_not_gt hss)) hprofile (d := 0) (ω := 0)
      (show |(0 : ℝ)*0| ≤ b/2 by simpa using (half_pos hb).le)
      (JetPrototype.sign sign) hsign
    simp only [JetCoreMap.axialMap,mul_zero,zero_add,sub_zero] at hg
    exact hbound.trans ((by linarith [min_le_right δ b] : min δ b/2 ≤ b/2).trans hg)

end BoltzmannNonuniqueness.JetCoreSheet

end

end

section

/-! # The actual dilated two-core three-region estimate -/

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal Topology
open BoltzmannNonuniqueness.VelocityWeight BoltzmannNonuniqueness.AxialFlow

namespace BoltzmannNonuniqueness.JetCoreSheet

def rescaledBallisticSecondCoreMass (R η K α γ q t₁ t₂ z : ℝ)
    (s d : Velocity → ℝ) (sign : Velocity → Bool) (y : Velocity → Transverse)
    (w : Velocity) : ℝ≥0∞ :=
  rescaledCoreMeasure R η K α γ (s w) (d w) q (sign w)
    t₂ (y w,z-(t₁-t₂)*axial w) w univ

/-- The small-scale threshold precedes the cardinality and large-scale radius.
This is the order of choices in the two-axial-gains lemma of §8. -/
theorem rescaled_two_core_small_regions {K α γ q a ε : ℝ} (hK : 0 ≤ K)
    (hα : 0 < α) (hγ : 0 < γ) (hq₁ : 1 < q) (hq₂ : q < 2)
    (ha : 0 < a) (hε : 0 < ε) :
    ∃ μ₀ : ℝ, 0 < μ₀ ∧ ∀ J : ℕ, ∃ d₀ r₀ : ℝ, 0 < d₀ ∧ 0 < r₀ ∧
      ∀ {R s₁ d₁ t₁ t₂ : ℝ}, 0 < R → 0 < s₁ → 0 < d₁ → d₁ ≤ 1/16 →
      a ≤ t₂ → t₂ ≤ t₁ →
      ∀ (η : ℝ) (sign₁ : Bool) (x : JetPrototype.Space) (v : Velocity)
        (S : Finset ℝ) (s₂ d₂ : Velocity → ℝ)
        (sign₂ : Velocity → Bool) (y₂ : Velocity → Transverse),
      ‖transverse v‖ ≤ r₀ → S.card ≤ J →
      (∀ w, 0 < s₂ w) → (∀ w, 0 < d₂ w) → (∀ w, d₂ w ≤ 1/16) →
      (∀ w, d₂ w ≤ d₀) → (∀ w, μ₀ ≤ s₂ w → s₂ w ∈ S) →
      ∃ E T : Set Velocity, MeasurableSet E ∧ MeasurableSet T ∧
        rescaledCoreMeasure R η K α γ s₁ d₁ q sign₁ t₁ x v E ≤ ENNReal.ofReal ε ∧
        rescaledCoreMeasure R η K α γ s₁ d₁ q sign₁ t₁ x v T ≤ ENNReal.ofReal ε ∧
        ∀ w, w ∉ E → w ∉ T →
          rescaledBallisticSecondCoreMass R η K α γ q t₁ t₂ x.2 s₂ d₂ sign₂ y₂ w ≤
            ENNReal.ofReal ε := by
  obtain ⟨δ,hδ,hcollapsed⟩ := rescaled_bands_small_of_card hK hα hγ hq₁ hq₂
    ha (half_pos hε) 5
  obtain ⟨μ₀,hμ₀,hsecond⟩ := rescaled_second_core_small_off_bands hα hγ hq₁ hq₂ ha hδ
  refine ⟨μ₀,hμ₀,?_⟩
  intro J
  obtain ⟨b,hb,hprofile⟩ := rescaled_bands_small_of_card hK hα hγ hq₁ hq₂
    ha (half_pos hε) (2*J)
  let A := slabAmplitude K α γ a
  have hA : 0 ≤ A := slabAmplitude_nonneg hK ha α γ
  have he : 0 < ε/(A+1) := div_pos hε (by positivity)
  obtain ⟨r,hr,hgood⟩ := hsecond b hb (ε/(A+1)) he
  obtain ⟨r₀,hr₀,htail⟩ := rescaled_away_small_of_transverse hK hα hγ hq₁ hq₂ ha hr hε
  refine ⟨min δ b/4,r₀,div_pos (lt_min hδ hb) (by norm_num),hr₀,?_⟩
  intro R s₁ d₁ t₁ t₂ hR hs₁ hd₁ hd₁max ht₂ htt η sign₁ x v S s₂ d₂ sign₂ y₂
    hv hS hs₂ hd₂ hd₂max hd₂small hmesh
  let E₁ := axial ⁻¹' bands (collapsedCenters α t₁ x.2) δ
  let E₂ := axial ⁻¹' bands (profileCenters α γ t₁ x.2 S) b
  let E := E₁ ∪ E₂
  let T := {w : Velocity | r ≤ ‖transverse w‖}
  have hE₁ : MeasurableSet E₁ :=
    (bands_measurableSet _ _).preimage ChartKernel.measurable_axial
  have hE₂ : MeasurableSet E₂ :=
    (bands_measurableSet _ _).preimage ChartKernel.measurable_axial
  refine ⟨E,T,hE₁.union hE₂,
    measurableSet_le measurable_const ChartKernel.measurable_transverse.norm,?_,?_,?_⟩
  · calc
      _ ≤ _ := measure_union_le _ _
      _ ≤ ENNReal.ofReal (ε/2)+ENNReal.ofReal (ε/2) := add_le_add
        (hcollapsed hR hs₁ hd₁ hd₁max (ht₂.trans htt) η sign₁ x v _
          (collapsedCenters_card_le _ _ _))
        (hprofile hR hs₁ hd₁ hd₁max (ht₂.trans htt) η sign₁ x v _
          ((profileCenters_card_le _ _ _ _ _).trans (Nat.mul_le_mul_left 2 hS)))
      _ = ENNReal.ofReal ε := by
        rw [← ENNReal.ofReal_add (half_pos hε).le (half_pos hε).le]
        congr 1
        ring
  · exact htail hR hs₁ hd₁ hd₁max (ht₂.trans htt) η sign₁ x v hv
  · intro w hwE hwT
    have hw₁ : axial w ∉ bands (collapsedCenters α t₁ x.2) δ := fun h => hwE (Or.inl h)
    have hw₂ : axial w ∉ bands (profileCenters α γ t₁ x.2 S) b := fun h => hwE (Or.inr h)
    unfold rescaledBallisticSecondCoreMass
    apply (hgood hR hK (hs₂ w) (hd₂ w) (hd₂max w) (hd₂small w) ht₂ htt η
      (sign₂ w) (y₂ w) w S (hmesh w) (le_of_not_ge hwT) hw₁ hw₂).trans
    rw [← ENNReal.ofReal_mul (amplitude_nonneg hK (hs₂ w) (ha.le.trans ht₂) α γ)]
    apply ENNReal.ofReal_le_ofReal
    calc
      _ ≤ (A+1)*(ε/(A+1)) := mul_le_mul_of_nonneg_right
        ((amplitude_le_slab hK ha (hs₂ w) ht₂ α γ).trans (by change A ≤ A+1; linarith)) he.le
      _ = ε := by field_simp

end BoltzmannNonuniqueness.JetCoreSheet

end

end

section

/-! # Uniform quantitative smallness of the two dilated core gains -/

noncomputable section

open MeasureTheory Set
open scoped ENNReal
open BoltzmannNonuniqueness.VelocityWeight

namespace BoltzmannNonuniqueness.JetCoreSheet

theorem rescaled_two_core_small_integral {K α γ q a ε : ℝ} (hK : 0 ≤ K)
    (hα : 0 < α) (hγ : 0 < γ) (hq₁ : 1 < q) (hq₂ : q < 2)
    (ha : 0 < a) (hε : 0 < ε) :
    ∃ μ₀ : ℝ, 0 < μ₀ ∧ ∀ J : ℕ, ∃ d₀ r₀ : ℝ, 0 < d₀ ∧ 0 < r₀ ∧
      ∀ {R s₁ d₁ t₁ t₂ : ℝ}, 0 < R → 0 < s₁ → 0 < d₁ → d₁ ≤ 1/16 →
      a ≤ t₂ → t₂ ≤ t₁ →
      ∀ (η : ℝ) (sign₁ : Bool) (x : JetPrototype.Space) (v : Velocity)
        (S : Finset ℝ) (s₂ d₂ : Velocity → ℝ)
        (sign₂ : Velocity → Bool) (y₂ : Velocity → Transverse),
      ‖transverse v‖ ≤ r₀ → S.card ≤ J →
      (∀ w, 0 < s₂ w) → (∀ w, 0 < d₂ w) → (∀ w, d₂ w ≤ 1/16) →
      (∀ w, d₂ w ≤ d₀) → (∀ w, μ₀ ≤ s₂ w → s₂ w ∈ S) →
      (∫⁻ w, rescaledBallisticSecondCoreMass R η K α γ q t₁ t₂ x.2 s₂ d₂ sign₂ y₂ w
        ∂rescaledCoreMeasure R η K α γ s₁ d₁ q sign₁ t₁ x v) ≤ ENNReal.ofReal ε := by
  let C := growthConstant K α γ q/a
  have hC : 0 ≤ C := div_nonneg (growthConstant_nonneg hK α γ q) ha.le
  let e := ε/(3*C+1)
  have he : 0 < e := div_pos hε (by positivity)
  obtain ⟨μ,hμ,hreg⟩ := rescaled_two_core_small_regions hK hα hγ hq₁ hq₂ ha he
  refine ⟨μ,hμ,?_⟩
  intro J
  obtain ⟨d₀,r₀,hd₀,hr₀,hr⟩ := hreg J
  refine ⟨d₀,r₀,hd₀,hr₀,?_⟩
  intro R s₁ d₁ t₁ t₂ hR hs₁ hd₁ hd₁max ht₂ htt η sign₁ x v S s₂ d₂ sign₂ y₂
    hv hS hs₂ hd₂ hd₂max hd₂small hmesh
  have hmass {s d t : ℝ} (hs : 0 < s) (hd : 0 < d) (hdmax : d ≤ 1/16)
      (ht : a ≤ t) (sign : Bool) (x : JetPrototype.Space) (v : Velocity) :
      rescaledCoreMeasure R η K α γ s d q sign t x v univ ≤ ENNReal.ofReal C := by
    apply (rescaled_mass_bound hR hK hα hγ hs hd hdmax (ha.trans_le ht) hq₁ hq₂ η sign x v).trans
    exact ENNReal.ofReal_le_ofReal
      (div_le_div_of_nonneg_left (growthConstant_nonneg hK α γ q) ha ht)
  obtain ⟨E,T,hE,hT,heE,heT,hgood⟩ := hr hR hs₁ hd₁ hd₁max ht₂ htt η sign₁ x v S
    s₂ d₂ sign₂ y₂ hv hS hs₂ hd₂ hd₂max hd₂small hmesh
  have hb (w : Velocity) :
      rescaledBallisticSecondCoreMass R η K α γ q t₁ t₂ x.2 s₂ d₂ sign₂ y₂ w ≤
        ENNReal.ofReal C := hmass (hs₂ w) (hd₂ w) (hd₂max w) ht₂ _ _ _
  calc
    _ ≤ ENNReal.ofReal C*rescaledCoreMeasure R η K α γ s₁ d₁ q sign₁ t₁ x v E+
        ENNReal.ofReal C*rescaledCoreMeasure R η K α γ s₁ d₁ q sign₁ t₁ x v T+
        ENNReal.ofReal e*rescaledCoreMeasure R η K α γ s₁ d₁ q sign₁ t₁ x v univ :=
      GainPullback.integral_three_regions_le _ hE hT hb hgood
    _ ≤ ENNReal.ofReal C*ENNReal.ofReal e+ENNReal.ofReal C*ENNReal.ofReal e+
        ENNReal.ofReal e*ENNReal.ofReal C := by
      gcongr
      exact hmass hs₁ hd₁ hd₁max (ht₂.trans htt) _ _ _
    _ = ENNReal.ofReal (3*C*e) := by
      rw [← ENNReal.ofReal_mul hC,← ENNReal.ofReal_mul he.le,
        ← ENNReal.ofReal_add (mul_nonneg hC he.le) (mul_nonneg hC he.le),
        ← ENNReal.ofReal_add (add_nonneg (mul_nonneg hC he.le) (mul_nonneg hC he.le))
          (mul_nonneg he.le hC)]
      congr 1
      ring
    _ ≤ ENNReal.ofReal ε := by
      apply ENNReal.ofReal_le_ofReal
      calc
        _ ≤ (3*C+1)*e := mul_le_mul_of_nonneg_right (by linarith) he.le
        _ = ε := by dsimp [e]; field_simp

end BoltzmannNonuniqueness.JetCoreSheet

end

end

section

/-! # Vanishing of the actual two-core velocity integral at an axial endpoint -/

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal Topology
open BoltzmannNonuniqueness.VelocityWeight

namespace BoltzmannNonuniqueness.JetCoreSheet

/-- This is the velocity-integral part of the two-axial-gains lemma. The finite
list hypothesis is a scale-discretization condition, with no integral or
compactness conclusion assumed. Both collision times and positions may vary. -/
theorem rescaled_two_core_axial_tendsto {K α γ q a : ℝ} (hK : 0 ≤ K)
    (hα : 0 < α) (hγ : 0 < γ) (hq₁ : 1 < q) (hq₂ : q < 2) (ha : 0 < a)
    (R η s₁ d₁ t₁ t₂ D : ℕ → ℝ) (sign₁ : ℕ → Bool)
    (x : ℕ → JetPrototype.Space) (v : ℕ → Velocity)
    (s₂ d₂ : ℕ → Velocity → ℝ) (sign₂ : ℕ → Velocity → Bool)
    (y₂ : ℕ → Velocity → Transverse)
    (hR : ∀ n, 0 < R n) (hs₁ : ∀ n, 0 < s₁ n) (hd₁ : ∀ n, 0 < d₁ n) (hd₁max : ∀ n, d₁ n ≤ 1/16)
    (ht₂ : ∀ n, a ≤ t₂ n) (htt : ∀ n, t₂ n ≤ t₁ n)
    (hs₂ : ∀ n w, 0 < s₂ n w) (hd₂ : ∀ n w, 0 < d₂ n w)
    (hd₂max : ∀ n w, d₂ n w ≤ 1/16) (hd₂D : ∀ n w, d₂ n w ≤ D n)
    (hD : Tendsto D atTop (𝓝 0))
    (hv : Tendsto (fun n => ‖transverse (v n)‖) atTop (𝓝 0))
    (hmesh : ∀ μ : ℝ, 0 < μ → ∃ J : ℕ, ∀ n, ∃ S : Finset ℝ,
      S.card ≤ J ∧ ∀ w, μ ≤ s₂ n w → s₂ n w ∈ S) :
    Tendsto (fun n => ∫⁻ w,
      rescaledBallisticSecondCoreMass (R n) (η n) K α γ q (t₁ n) (t₂ n) (x n).2
        (s₂ n) (d₂ n) (sign₂ n) (y₂ n) w
      ∂rescaledCoreMeasure (R n) (η n) K α γ (s₁ n) (d₁ n) q (sign₁ n) (t₁ n) (x n) (v n)) atTop (𝓝 0) := by
  let B := ENNReal.ofReal (growthConstant K α γ q/a)
  have htotal {R s d t : ℝ} (hR : 0 < R) (hs : 0 < s) (hd : 0 < d) (hdmax : d ≤ 1/16) (ht : a ≤ t)
      (η : ℝ) (sign : Bool) (x : JetPrototype.Space) (v : Velocity) :
      rescaledCoreMeasure R η K α γ s d q sign t x v univ ≤ B := by
    apply (rescaled_mass_bound hR hK hα hγ hs hd hdmax (ha.trans_le ht)
      hq₁ hq₂ η sign x v).trans
    exact ENNReal.ofReal_le_ofReal
      (div_le_div_of_nonneg_left (growthConstant_nonneg hK α γ q) ha ht)
  apply GainPullback.integral_three_regions_tendsto (B := B) (C := B)
    ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top
  · intro n w
    exact htotal (hR n) (hs₂ n w) (hd₂ n w) (hd₂max n w) (ht₂ n) _ _ _ _
  · intro n
    exact htotal (hR n) (hs₁ n) (hd₁ n) (hd₁max n) ((ht₂ n).trans (htt n)) _ _ _ _
  · intro ε hε
    obtain ⟨e,he,heε⟩ := ENNReal.exists_nnreal_pos_mul_lt
      (by simp : (1 : ℝ≥0∞) ≠ ∞) hε.ne'
    have he' : (0 : ℝ) < e := he
    have heε' : ENNReal.ofReal (e : ℝ) ≤ ε := by simpa using heε.le
    obtain ⟨μ,hμ,hregions⟩ := rescaled_two_core_small_regions hK hα hγ hq₁ hq₂ ha he'
    obtain ⟨J,hJ⟩ := hmesh μ hμ
    obtain ⟨d₀,r₀,hd₀,hr₀,hr⟩ := hregions J
    filter_upwards [hD.eventually (gt_mem_nhds hd₀),hv.eventually (gt_mem_nhds hr₀)]
      with n hnD hnv
    obtain ⟨S,hS,hsS⟩ := hJ n
    obtain ⟨E,T,hE,hT,heE,heT,hgood⟩ := hr (hR n) (hs₁ n) (hd₁ n) (hd₁max n)
      (ht₂ n) (htt n) (η n) (sign₁ n) (x n) (v n) S (s₂ n) (d₂ n) (sign₂ n) (y₂ n)
      hnv.le hS (hs₂ n) (hd₂ n) (hd₂max n) (fun w => (hd₂D n w).trans hnD.le) hsS
    exact ⟨E,T,hE,hT,heE.trans heε',heT.trans heε',
      fun w hwE hwT => (hgood w hwE hwT).trans heε'⟩

end BoltzmannNonuniqueness.JetCoreSheet

end

end

end OAI
