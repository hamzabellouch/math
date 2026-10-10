import OAI.Probability.SLE.Geometry.NormalizedRestartDensity
import OAI.Probability.SLE.Geometry.NormalizedCanonicalRestart
import OAI.Probability.SLE.Loewner.RawDiskRadiusLaw

namespace OAI

/-! Exact finite centered density in the disk coordinates used by the
prescribed tests. This includes paths which never reach the later level. -/
noncomputable section
open Set Filter _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal

namespace SLEExactGauge
local instance diskDensityMeasurable : MeasurableSpace C(ℝ≥0,ℝ) := borel _
local instance diskDensityBorel : BorelSpace C(ℝ≥0,ℝ) := ⟨rfl⟩

lemma IsCapacityTwoWitness.normalized_disk_density
    {U : ℝ≥0 → ℝ} {γ : ℝ≥0 → ℂ} {G F : ℝ≥0 → ℂ → ℂ}
    (hw : IsCapacityTwoWitness U γ G F) (hU : Continuous U)
    (κ : ℝ) (T a : ℝ≥0) (ha : 0 < a) (p : C(ℝ≥0,ℝ))
    {β : ℝ≥0 → ℂ} {G' F' : ℝ≥0 → ℂ → ℂ}
    (hb : IsCapacityTwoWitness (fun t => Real.sqrt κ*p t) β G' F')
    (hdriver : (fun t => Real.sqrt κ*p t)=normalizedRestartDriver U T a)
    (θ : ℝ) (hθ : θ ∈ Ioo (0:ℝ) Real.pi) (z : ℂ)
    (hz : z ∈ survivingDomain γ T) (hzH : z ∈ upperHalfPlane)
    (hpolar : G T z=(U T:ℂ)+(a:ℂ)*Complex.exp (θ*Complex.I))
    (u v : ℝ) (hu : 0 ≤ u) (hv : 0 < v)
    (hbase : fullRadius G T z=(2*z.im)*Real.exp (-u)) :
    ENNReal.ofReal (stoppedGreen κ U γ G z (u+v)/initialGreen κ z) =
      ENNReal.ofReal (greenDensity κ U γ G T z/initialGreen κ z)*
        canonicalFiniteDensity κ (v,Target.diskMapInv θ 0,p) := by
  have hb' : IsCapacityTwoWitness (normalizedRestartDriver U T a) β G' F' := by
    rwa [hdriver] at hb
  have hF : F T ((a:ℂ)*Target.diskMapInv θ 0+(U T:ℂ))=z := by
    rw [Target.diskMapInv_zero,add_comm,← hpolar]
    exact hw.2.2.2.2.2.2.2.1 T z hz
  have heq := hw.normalized_restart_stopped_green_eq hU T a ha hb' κ
    (Target.diskMapInv θ 0) (Target.diskMapInv_maps hθ (by simp))
    u v hu hv (by simpa only [hF] using hbase)
  rw [hF] at heq
  rw [canonicalFiniteDensity_eq κ p hb v hv.le,hdriver,
    ← ENNReal.ofReal_mul (div_nonneg (greenDensity_nonneg hw κ T z)
      (initialGreen_pos κ z hzH).le),← heq]
  congr 1
  ring

theorem normalized_restart_disk_density
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {κ : ℝ} {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P)
    (hm : ∀ t, Measurable (B t)) (hc : ∀ ω, Continuous (fun t => B t ω))
    (γ : Ω → ℝ≥0 → ℂ) (G F : Ω → ℝ≥0 → ℂ → ℂ)
    (hw : ∀ ω, IsCapacityTwoWitness (fun t => Real.sqrt κ*B t ω) (γ ω) (G ω) (F ω))
    (hpublished : PublishedTraceGeneration (P.map (sourceDriverPath B hc)) κ (fun t p => p t))
    (τ : Ω → ℝ≥0)
    (hτ : IsStoppingTime (Filtration.natural B (fun t => (hm t).stronglyMeasurable))
      (fun ω => (τ ω:WithTop ℝ≥0)))
    (a : Ω → ℝ≥0) (haM : Measurable[hτ.measurableSpace] a) (ha : ∀ ω, 0 < a ω) :
    ∀ᵐ ω ∂P, ∀ (θ : ℝ) (_hθ : θ ∈ Ioo (0:ℝ) Real.pi) (z : ℂ)
      (_hz : z ∈ survivingDomain (γ ω) (τ ω)) (_hzH : z ∈ upperHalfPlane)
      (_hpolar : G ω (τ ω) z=(Real.sqrt κ*B (τ ω) ω:ℝ)+
        (a ω:ℂ)*Complex.exp (θ*Complex.I))
      (u v : ℝ) (_hu : 0 ≤ u) (_hv : 0 < v)
      (_hbase : fullRadius (G ω) (τ ω) z=(2*z.im)*Real.exp (-u)),
      ENNReal.ofReal (stoppedGreen κ (fun t => Real.sqrt κ*B t ω) (γ ω) (G ω) z
        (u+v)/initialGreen κ z) =
      ENNReal.ofReal (greenDensity κ (fun t => Real.sqrt κ*B t ω) (γ ω) (G ω)
        (τ ω) z/initialGreen κ z)*canonicalFiniteDensity κ
          (v,Target.diskMapInv θ 0,normalizedRestartDriverPath B hc τ a ω) := by
  obtain ⟨Φ,Gc,Fc,_hΦ,hW⟩ := exists_measurable_canonical_witness _ κ hpublished
  let Y := normalizedRestartDriverPath B hc τ a
  have hY : Measurable Y := measurable_scaleDriverPath.comp
    ((haM.mono hτ.measurableSpace_le le_rfl).inv.prodMk
      (sourceRestartDriverPath_measurable B hm hc τ hτ))
  have hYlaw : P.map Y=P.map (sourceDriverPath B hc) := by
    change P.map (fun ω => scaleDriverPath (a ω)⁻¹
      (sourceRestartDriverPath B hc τ ω))=P.map (sourceDriverPath B hc)
    simpa only [Measure.restrict_univ,measure_univ,one_smul] using
      source_restart_random_scale_driver_law B hB hm hc τ hτ
        (fun ω => (a ω)⁻¹) haM.inv (fun ω => inv_pos.mpr (ha ω))
        univ MeasurableSet.univ
  filter_upwards [canonical_witness_pullback hW Y hY hYlaw] with ω hb
  intro θ hθ z hz hzH hpolar u v hu hv hbase
  exact (hw ω).normalized_disk_density ((hc ω).const_mul _) κ (τ ω) (a ω) (ha ω)
    (Y ω) hb (normalizedRestartDriverPath_driver κ B hc τ a ω)
    θ hθ z hz hzH hpolar u v hu hv hbase

end SLEExactGauge

end

end OAI
