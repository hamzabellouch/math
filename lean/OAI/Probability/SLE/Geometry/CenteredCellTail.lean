import OAI.Probability.SLE.Geometry.RadiusCellTail
import OAI.Probability.SLE.Geometry.FinitePastCellTail
import OAI.Probability.SLE.Angle.RadiusAngleBounds
import OAI.Probability.SLE.Geometry.ArbitraryDiskTail

namespace OAI

/-! Actual centered cell tails, and finite strict-past tests, are bounded
by the prescribed limiting disk tail after angular mixing at the start. -/
noncomputable section
open Set Filter _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory Metric
open scoped Topology NNReal ENNReal

namespace SLEExactGauge.Multipoint
local instance centeredCellMeasurable : MeasurableSpace C(ℝ≥0,ℝ) := borel _
local instance centeredCellBorel : BorelSpace C(ℝ≥0,ℝ) := ⟨rfl⟩

theorem CanonicalMass.centered_cell_tail_of_angle_bound
    {Ω : Type} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {κ : ℝ} {B : ℝ≥0 → Ω → ℝ} {hBm : Measurable (Function.uncurry B)}
    {γ : Ω → ℝ≥0 → ℂ} {G : Ω → ℝ≥0 → ℂ → ℂ}
    (C : CanonicalMass P κ B hBm γ G)
    (hB : IsBrownianReal B P) (hc : ∀ ω, Continuous (fun t => B t ω))
    (h0 : ∀ ω, B 0 ω=0) (hκ : 0 < κ) (hκ8 : κ < 8)
    (F : Ω → ℝ≥0 → ℂ → ℂ)
    (hw : ∀ ω, IsCapacityTwoWitness (fun t => Real.sqrt κ*B t ω) (γ ω) (G ω) (F ω))
    (R : RawCanonicalMass)
    (he : ∀ᵐ ω ∂P, (∀ t, R.process t (sourceDriverPath B hc ω)=C.process t ω) ∧
      R.terminal (sourceDriverPath B hc ω)=C.rational.terminal ω)
    (D : Set C(ℝ≥0,ℝ)) (hD : MeasurableSet D)
    (hDf : ∀ᵐ p ∂P.map (sourceDriverPath B hc), p∈D)
    (hDp : ∀ p∈D, PositiveMassPaths (fun t => R.process t p) (R.terminal p))
    (hgrowth : PublishedDiskUnivalentGrowth)
    (hpublished : PublishedTraceGeneration (P.map (sourceDriverPath B hc)) κ (fun t p => p t))
    (z : ℂ) (hz : z∈upperHalfPlane) (u v r b : ℝ)
    (hu : 0<u) (hv : 0<v) (hr : 0<r)
    (hR : (2*z.im)*Real.exp (-u)=(2048*Real.pi)*r)
    (K : Set ℂ) (hK : MeasurableSet K) (hKball : K⊆closedBall z (2*r))
    (hangle : ∀ θ∈Ioo (0:ℝ) Real.pi,
      canonicalAngleAverage (P.map (sourceDriverPath B hc)) κ u
        (R.angleDiskTail (P.map (sourceDriverPath B hc)) κ b v) θ ≤
      2*(∫⁻ φ, R.angleDiskTail (P.map (sourceDriverPath B hc)) κ b v φ ∂Target.angleLaw κ)) :
    finiteCenteredLaw P κ B γ G z (u+v)
      (C.finiteCellMassTest (fun ω => radiusLevelTime (γ ω) (G ω) z (u+v)) K
        (ENNReal.ofReal (((32768*Real.pi)*r)^dimension κ)*ENNReal.ofReal b)) ≤
      2*C.limitingDiskTail hc b := by
  have hm (t : ℝ≥0) : Measurable (B t) := hBm.of_uncurry_left
  let ν := P.map (sourceDriverPath B hc)
  let : IsProbabilityMeasure ν :=
    (Measure.isProbabilityMeasure_map_iff (source_path_measurable _ hm).aemeasurable).mpr inferInstance
  let Q := finiteCenteredLaw P κ B γ G z (u+v)
  let : IsProbabilityMeasure Q := finiteCenteredLaw_probability hB κ hκ hκ8 γ G F
    (Eventually.of_forall hw) z hz (u+v) (by linarith)
  let f := R.angleDiskTail ν κ b v
  have hf : Measurable f := R.angleDiskTail_measurable ν κ b v
  have hh := C.cell_mass_disk_tail_at_radius hB hc h0 hκ hκ8 F hw R he D hD hDf hDp
    hgrowth hpublished z hz u v r b hu.le hv hr hR K hK hKball univ MeasurableSet.univ
  simp only [univ_inter,setLIntegral_univ] at hh
  have hi := (radius_angle_average_bounds hB hBm hc h0 hκ hκ8 γ G F hw hpublished
    z hz 0 u (u+v) (by norm_num) hu (by linarith) f hf 0
    (2*(∫⁻ φ, f φ ∂Target.angleLaw κ)) (fun θ hθ => ⟨bot_le,hangle θ hθ⟩)
    univ MeasurableSet.univ).2
  simp only [zero_add,setLIntegral_univ,measure_univ,mul_one] at hi
  exact hh.trans (hi.trans (mul_le_mul' le_rfl
    (C.raw_angle_tail_average_le_limit hB hc h0 hκ hκ8 F hw R he b v hv.le)))

theorem CanonicalMass.centered_strict_past_cell_tail_of_angle_bound
    {Ω : Type} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {κ : ℝ} {B : ℝ≥0 → Ω → ℝ} {hBm : Measurable (Function.uncurry B)}
    {γ : Ω → ℝ≥0 → ℂ} {G : Ω → ℝ≥0 → ℂ → ℂ}
    (C : CanonicalMass P κ B hBm γ G)
    (hB : IsBrownianReal B P) (hc : ∀ ω, Continuous (fun t => B t ω))
    (h0 : ∀ ω, B 0 ω=0) (hκ : 0 < κ) (hκ8 : κ < 8)
    (F : Ω → ℝ≥0 → ℂ → ℂ)
    (hw : ∀ ω, IsCapacityTwoWitness (fun t => Real.sqrt κ*B t ω) (γ ω) (G ω) (F ω))
    (R : RawCanonicalMass)
    (he : ∀ᵐ ω ∂P, (∀ t, R.process t (sourceDriverPath B hc ω)=C.process t ω) ∧
      R.terminal (sourceDriverPath B hc ω)=C.rational.terminal ω)
    (D : Set C(ℝ≥0,ℝ)) (hD : MeasurableSet D)
    (hDf : ∀ᵐ p ∂P.map (sourceDriverPath B hc), p∈D)
    (hDp : ∀ p∈D, PositiveMassPaths (fun t => R.process t p) (R.terminal p))
    (hgrowth : PublishedDiskUnivalentGrowth)
    (hpublished : PublishedTraceGeneration (P.map (sourceDriverPath B hc)) κ (fun t p => p t))
    (z : ℂ) (hz : z∈upperHalfPlane) (u v r b : ℝ)
    (hu : 0<u) (hv : 0<v) (hr : 0<r)
    (hR : (2*z.im)*Real.exp (-u)=(2048*Real.pi)*r)
    (K : Set ℂ) (hK : MeasurableSet K) (hKball : K⊆closedBall z (2*r))
    (hangle : ∀ θ∈Ioo (0:ℝ) Real.pi,
      canonicalAngleAverage (P.map (sourceDriverPath B hc)) κ u
        (R.angleDiskTail (P.map (sourceDriverPath B hc)) κ b v) θ ≤
      2*(∫⁻ φ, R.angleDiskTail (P.map (sourceDriverPath B hc)) κ b v φ ∂Target.angleLaw κ)) (J : Finset ℝ≥0) :
    finiteCenteredLaw P κ B γ G z (u+v)
      (finiteStrictPastEvent J
        (fun t => {ω | (((32768*Real.pi)*r)^dimension κ)*b <
          (C.process t ω (Subtype.val ⁻¹' K)).toReal})
        (fun ω => radiusLevelTime (γ ω) (G ω) z (u+v))) ≤
      2*C.limitingDiskTail hc b := by
  let Q := finiteCenteredLaw P κ B γ G z (u+v)
  let T : Ω → WithTop ℝ≥0 := fun ω => radiusLevelTime (γ ω) (G ω) z (u+v)
  have hfinite : ∀ᵐ ω ∂Q, T ω≠⊤ :=
    finiteCenteredLaw_earlier_stop_ae_finite hB hc κ hκ hκ8 γ G F (Eventually.of_forall hw)
      z hz (u+v) (u+v) (by linarith) le_rfl T (Eventually.of_forall fun _ => le_rfl)
  have hh := C.finite_strict_past_le_cell_test Q (withDensity_absolutelyContinuous P _) T
    hfinite J K ((((32768*Real.pi)*r)^dimension κ)*b)
  rw [ENNReal.ofReal_mul (Real.rpow_nonneg (by positivity) _)] at hh
  exact hh.trans (C.centered_cell_tail_of_angle_bound hB hc h0 hκ hκ8 F hw R he D hD hDf hDp
    hgrowth hpublished z hz u v r b hu hv hr hR K hK hKball hangle)

end SLEExactGauge.Multipoint

end

end OAI
