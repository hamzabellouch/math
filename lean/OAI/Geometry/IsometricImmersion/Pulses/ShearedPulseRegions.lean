import OAI.Geometry.IsometricImmersion.Pulses.PulseCurvaturePrincipal
import OAI.Geometry.IsometricImmersion.Caps.PulseCapSeparation
import OAI.Geometry.IsometricImmersion.Energy.MovingSlabEnergy

namespace OAI

noncomputable section
open Set Filter Function
open scoped ContDiff Topology Matrix

namespace SmoothLocal.Pulse
open SmoothLocal.Geometry SmoothLocal.Flow SmoothLocal.ODE SmoothLocal.Weighted
open SmoothLocal.Hyperbolic

def shearedModelSquare (q0 : ℝ) : Set Coord :=
  inverseShearCoordinates q0 ⁻¹' modelSquare

theorem shearedModelSquare_eq_image (q0 : ℝ) :
    shearedModelSquare q0 = shearCoordinates q0 '' modelSquare := by
  ext p
  constructor
  · intro hp
    exact ⟨inverseShearCoordinates q0 p, hp, shear_inverse q0 p⟩
  · rintro ⟨x,hx,rfl⟩
    simpa only [shearedModelSquare, mem_preimage, inverse_shear] using hx

theorem shearedModelSquare_isCompact (q0 : ℝ) : IsCompact (shearedModelSquare q0) := by
  rw [shearedModelSquare_eq_image]
  exact modelSquare_isCompact.image (shearCoordinates_contDiff q0).continuous

theorem shearedModelSquare_subset_domain {U : Set Coord} (hSU : modelSquare ⊆ U) (q0 : ℝ) :
    shearedModelSquare q0 ⊆ inverseShearCoordinates q0 ⁻¹' U := fun _ hp => hSU hp

theorem sheared_reference_metric_smoothPositive {g : MetricField} {U : Set Coord}
    (hg : SmoothPositiveOn g U) (q0 : ℝ) :
    SmoothPositiveOn (metricInShearCoordinates g q0) (inverseShearCoordinates q0 ⁻¹' U) := by
  simpa only [metricInShearCoordinates, inverseShearCoordinates_eq_affine] using
    affinePullbackMetric_smoothPositive hg 0 (inverseShearMatrix q0)
      (Matrix.mulVec_injective_of_isUnit (inverseShearMatrix_isUnit q0))

theorem shearedModelDomain_isOpen {U : Set Coord} (hU : IsOpen U) (q0 : ℝ) :
    IsOpen (inverseShearCoordinates q0 ⁻¹' U) :=
  hU.preimage (inverseShearCoordinates_contDiff q0).continuous

def sectionFourClosedSlab (L r : ℝ) : Set Coord :=
  {p | |p 0| ≤ L*r ∧ |p 1| ≤ r}

theorem sectionFourClosedSlab_mem_shearedModelSquare
    {q0 L r : ℝ} (_hr : 0 < r) (hrhalf : r < 1/2)
    (hLr : L*r ≤ 1/20) (hq0 : |q0| ≤ 1/20)
    {p : Coord} (hp : p ∈ sectionFourClosedSlab L r) :
    p ∈ shearedModelSquare q0 := by
  have hx : |p 0| ≤ (1/20 : ℝ) := hp.1.trans hLr
  have hmul : |q0 * p 0| ≤ (1/20 : ℝ) * (1/20) := by
    rw [abs_mul]
    exact mul_le_mul hq0 hx (abs_nonneg _) (by norm_num)
  have hy : |p 1 - q0 * p 0| ≤ r + (1/20 : ℝ)*(1/20) :=
    (abs_sub _ _).trans (add_le_add hp.2 hmul)
  have hx3 : |p 0| ≤ 3 := hx.trans (by norm_num)
  have hy3 : |p 1 - q0*p 0| ≤ 3 := hy.trans (by linarith)
  constructor <;> intro i <;> fin_cases i
  · exact (abs_le.mp hx3).1
  · exact (abs_le.mp hy3).1
  · exact (abs_le.mp hx3).2
  · exact (abs_le.mp hy3).2

theorem pulseRectangle_mem_shearedModelSquare
    {q0 L r delta tau x t : ℝ} (hL : 0 < L) (hr : 0 < r) (hrhalf : r < 1/2)
    (hLr : L*r ≤ 1/20) (hq0 : |q0| ≤ 1/20)
    (hwidth : delta/tau ≤ r) (hx : |x| ≤ L*r/2)
    (ht : t ∈ Icc (-delta/tau) (delta/tau)) :
    (![x,t] : Coord) ∈ shearedModelSquare q0 := by
  apply sectionFourClosedSlab_mem_shearedModelSquare hr hrhalf hLr hq0
  constructor
  · exact hx.trans (by nlinarith [mul_pos hL hr])
  · exact (abs_le.mpr ⟨by simpa only [neg_div] using ht.1, ht.2⟩).trans hwidth

theorem pulseRectangle_eventually_in_shearedModelSquare
    {q0 L r : ℝ} (hL : 0 < L) (hr : 0 < r) (hrhalf : r < 1/2)
    (hLr : L*r ≤ 1/20) (hq0 : |q0| ≤ 1/20) (delta : ℝ) :
    ∀ᶠ tau : ℕ in atTop, 1 ≤ tau ∧
      ∀ x : ℝ, |x| ≤ L*r/2 → ∀ t ∈ Icc (-delta/(tau : ℝ)) (delta/(tau : ℝ)),
        (![x,t] : Coord) ∈ shearedModelSquare q0 := by
  have hw : ∀ᶠ tau : ℕ in atTop, 1 ≤ (tau : ℝ) ∧ delta/(2*(tau : ℝ)) ≤ r/4 :=
    (tendsto_natCast_atTop_atTop : Tendsto (fun tau : ℕ => (tau : ℝ)) atTop atTop).eventually
      (pulse_width_eventually hr delta)
  filter_upwards [hw, eventually_ge_atTop (1 : ℕ)] with tau htau htauN
  refine ⟨htauN,?_⟩
  intro x hx t ht
  have hwidth : delta / (tau : ℝ) ≤ r := by
    have hhalf := htau.2
    have he : delta / (tau : ℝ) = 2 * (delta / (2*(tau : ℝ))) := by ring
    rw [he]
    linarith
  exact pulseRectangle_mem_shearedModelSquare hL hr hrhalf hLr hq0 hwidth hx ht

theorem shrinkingSlab_subset_sectionFourClosedSlab
    {L r b speed : ℝ} (_hr : 0 < r) (hspeed : 0 ≤ speed)
    (hb : b ∈ Icc (-r) r) :
    shrinkingSlab (-(L*r)) (L*r) (-r) b speed ⊆ sectionFourClosedSlab L r := by
  intro p hp
  have hs : 0 ≤ speed*(p 1 - (-r)) := mul_nonneg hspeed (sub_nonneg.mpr hp.1.1)
  have hx0 := hp.2.1
  have hx1 := hp.2.2
  change -(L*r)+speed*(p 1-(-r)) ≤ p 0 at hx0
  change p 0 ≤ L*r-speed*(p 1-(-r)) at hx1
  refine ⟨abs_le.mpr ⟨by linarith, by linarith⟩, abs_le.mpr ⟨hp.1.1, hp.1.2.trans hb.2⟩⟩

end SmoothLocal.Pulse

end

end OAI
