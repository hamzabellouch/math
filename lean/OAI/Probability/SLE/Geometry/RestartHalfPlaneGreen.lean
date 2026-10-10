import OAI.Probability.SLE.Geometry.RestartInitialGreenIntegral
import OAI.Probability.SLE.StochasticIntegrals

namespace OAI

/-! Half-plane form of the inverse-map Green covariance, including tests
that reach the old trace. The current Green density vanishes off survival. -/

noncomputable section
open Set Filter _root_.MeasureTheory _root_.OAI.MeasureTheory Classical
open scoped NNReal ENNReal Topology

namespace SLEExactGauge.Multipoint

def extendHalfPlaneENN (f : upperHalfPlane → ℝ≥0∞) (z : ℂ) : ℝ≥0∞ :=
  if hz : z ∈ upperHalfPlane then f ⟨z,hz⟩ else 0

@[simp] lemma extendHalfPlaneENN_apply (f : upperHalfPlane → ℝ≥0∞) (z : upperHalfPlane) :
    extendHalfPlaneENN f z=f z := dite_eq_left z.property

def halfPlaneInversePoint
    {U : ℝ≥0 → ℝ} {γ : ℝ≥0 → ℂ} {G F : ℝ≥0 → ℂ → ℂ}
    (hw : IsCapacityTwoWitness U γ G F) (T : ℝ≥0) (z : upperHalfPlane) : upperHalfPlane :=
  ⟨F T ((z:ℂ)+(U T:ℂ)),(hw.2.2.2.2.2.2.1 T (by
    simpa only [upperHalfPlane,mem_ofPred_eq,Complex.add_im,Complex.ofReal_im,add_zero]
      using z.property)).1.1⟩

lemma currentGreen_measurable
    {U : ℝ≥0 → ℝ} {γ : ℝ≥0 → ℂ} {G F : ℝ≥0 → ℂ → ℂ}
    (hw : IsCapacityTwoWitness U γ G F) (hU : Continuous U)
    {κ : ℝ} (hκ : 0 < κ) (T : ℝ≥0) : Measurable (greenDensity κ U γ G T) := by
  have h : Measurable (fun p : ℝ≥0 × ℂ => greenDensity κ U γ G p.1 p.2) :=
    hw.killed_green_measurable (κ := κ) hU hκ
  have hp : Measurable (fun z : ℂ => (T,z)) := measurable_const.prodMk measurable_id
  simpa only [Function.comp_def] using h.comp hp

lemma halfPlane_realDensity_lintegral (ρ : ℂ → ℝ) (hρ : Measurable ρ)
    (f : upperHalfPlane → ℝ≥0∞) :
    (∫⁻ z, f z ∂(volume.withDensity (fun x => ENNReal.ofReal (ρ x))).comap Subtype.val) =
      ∫⁻ z in upperHalfPlane, extendHalfPlaneENN f z * ENNReal.ofReal (ρ z) := by
  calc
    _ = ∫⁻ z : upperHalfPlane, extendHalfPlaneENN f z
        ∂(volume.withDensity (fun x => ENNReal.ofReal (ρ x))).comap Subtype.val := by
      apply lintegral_congr
      intro z
      exact (extendHalfPlaneENN_apply f z).symm
    _ = ∫⁻ z in upperHalfPlane, extendHalfPlaneENN f z
        ∂volume.withDensity (fun x => ENNReal.ofReal (ρ x)) :=
      lintegral_subtype_comap isOpen_upperHalfPlane.measurableSet _
    _ = _ := by
      rw [setLIntegral_withDensity_eq_setLIntegral_mul_non_measurable volume hρ.ennreal_ofReal _
        isOpen_upperHalfPlane.measurableSet (ae_of_all _ (fun _ => ENNReal.ofReal_lt_top))]
      apply lintegral_congr
      intro z
      exact mul_comm _ _

theorem restart_halfPlane_green_test
    {U : ℝ≥0 → ℝ} {γ β : ℝ≥0 → ℂ} {G F G' F' : ℝ≥0 → ℂ → ℂ}
    (hw : IsCapacityTwoWitness U γ G F) (hU : Continuous U) (T : ℝ≥0)
    (hb : IsCapacityTwoWitness (fun t => U (T+t)-U T) β G' F')
    {κ : ℝ} (hκ : 0 < κ) (f : upperHalfPlane → ℝ≥0∞) :
    (∫⁻ z : upperHalfPlane, ENNReal.ofReal (‖deriv (F T) ((z:ℂ)+(U T:ℂ))‖^dimension κ) *
      f (halfPlaneInversePoint hw T z)
        ∂initialGreenMeasure κ) =
      ∫⁻ x, f x ∂(volume.withDensity (fun x =>
        ENNReal.ofReal (greenDensity κ U γ G T x))).comap Subtype.val := by
  let e := extendHalfPlaneENN f
  have he (z : upperHalfPlane) : f (halfPlaneInversePoint hw T z) =
      e (F T ((z:ℂ)+(U T:ℂ))) := by
    change f (halfPlaneInversePoint hw T z) = extendHalfPlaneENN f (halfPlaneInversePoint hw T z)
    exact (extendHalfPlaneENN_apply f _).symm
  simp_rw [he]
  rw [restart_initialGreen_test hw hU T hb κ e]
  have hρ : Measurable (greenDensity κ U γ G T) :=
    currentGreen_measurable hw hU hκ T
  rw [halfPlane_realDensity_lintegral _ hρ f]
  have hs : Function.support (fun z => e z * ENNReal.ofReal (greenDensity κ U γ G T z)) ⊆
      survivingDomain γ T := by
    intro z hz
    by_contra hn
    exact hz (by simp only [greenDensity,ite_eq_right hn,ENNReal.ofReal_zero,mul_zero])
  rw [setLIntegral_eq_of_support_subset hs,
    setLIntegral_eq_of_support_subset (hs.trans (fun _ hz => hz.1.1))]

end SLEExactGauge.Multipoint

end

end OAI
