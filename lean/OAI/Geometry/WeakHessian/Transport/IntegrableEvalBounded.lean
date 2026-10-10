import Mathlib
import OAI.Geometry.WeakHessian.LocalBounds.GammaNatMulLeft
import OAI.Geometry.WeakHessian.LocalBounds.AscendingSlope
import OAI.Geometry.WeakHessian.Geodesics.SquareControl

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

noncomputable section
open scoped ENNReal NNReal Topology BoundedContinuousFunction CompactlySupported
open scoped ENNReal NNReal Topology BoundedContinuousFunction
open scoped NNReal
open MeasureTheory Set Filter
open scoped Topology NNReal ENNReal
open scoped ENNReal NNReal Topology InnerProductSpace
open Set Filter Bornology
open MeasureTheory
open scoped ENNReal InnerProductSpace ComplexConjugate
open Set Filter
open scoped Topology ENNReal NNReal
open Set
open Set MeasureTheory CompactlySupported CompactlySupportedContinuousMap
open scoped Topology ENNReal NNReal InnerProductSpace
open scoped BoundedContinuousFunction
open Set MeasureTheory Filter
open Set Filter MeasureTheory Topology TopologicalSpace
open scoped ENNReal NNReal
open Set MeasureTheory ProbabilityTheory
open scoped ENNReal MeasureTheory ProbabilityTheory
open Set Filter Topology Bornology
open scoped InnerProductSpace
open Filter
open scoped Topology
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

attribute [local instance] Classical.propDecidable
namespace WeakHessian
open MeasureTheory Filter Set
open scoped Topology ENNReal NNReal

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] {m : Measure X}

lemma IsTestPlan.integrable_eval_bounded {π : Measure (Curve X)} (hπ : IsTestPlan m π)
    {f : X → ℝ} (hf : AEMeasurable f m) {B : ℝ} (hB : ∀ᵐ x ∂m, |f x| ≤ B) (t : Time) :
    Integrable (fun γ => f (γ t)) π := by
  let : IsProbabilityMeasure π := hπ.1
  exact (integrable_const B).mono' (hπ.aemeasurable_eval hf t).aestronglyMeasurable
    ((hπ.ae_eval_of_ae hB t).mono fun γ hγ => by simpa only [Real.norm_eq_abs] using hγ)

omit [MeasurableSpace X] [BorelSpace X] in
lemma BoundedTracks.integrable_lipschitz_eval {π : Measure (Curve X)} [IsFiniteMeasure π]
    (hb : BoundedTracks π) {f : X → ℝ} {L : ℝ≥0} (hf : LipschitzWith L f) (t : Time) :
    Integrable (fun γ => f (γ t)) π := by
  obtain ⟨o,R,_hR,hb⟩ := hb
  apply (integrable_const (|f o|+L*R)).mono'
    (hf.continuous.comp (continuous_eval_const t)).aestronglyMeasurable
  filter_upwards [hb] with γ hγ
  dsimp only [Function.comp_def]
  rw [Real.norm_eq_abs]
  have H := hf.dist_le_mul (γ t) o
  rw [Real.dist_eq] at H
  have J := abs_add_le (f (γ t)-f o) (f o)
  rw [sub_add_cancel] at J
  have T := mul_le_mul_of_nonneg_left (hγ t) L.coe_nonneg
  linarith

variable [CompleteSpace X] [TopologicalSpace.SeparableSpace X]

lemma IsTestPlan.integrable_gradient_energy (hfin : FiniteOnBoundedSets m)
    {π : Measure (Curve X)} (hπ : IsTestPlan m π)
    {f : X → ℝ} {L : ℝ≥0} (hf : LipschitzWith L f) (t : Time) :
    Integrable (fun γ => (weakGradient m f (γ t))^2) π := by
  have hS := localSobolev_of_lipschitz hfin hf
  apply hπ.integrable_eval_bounded
    ((weakGradient_isMinimal hS.2).1.1.aestronglyMeasurable.pow 2).aemeasurable
    (B := (L:ℝ)^2)
  filter_upwards [weakGradient_nonneg (m := m) f,weakGradient_le_lipschitz hfin hf] with x hn hx
  rw [abs_of_nonneg (sq_nonneg _)]
  exact (sq_le_sq₀ hn L.coe_nonneg).mpr hx

lemma IsTestPlan.integrable_gamma_eval (hfin : FiniteOnBoundedSets m)
    (hpar : LocalGradientParallelogram m) {π : Measure (Curve X)} (hπ : IsTestPlan m π)
    {f g : X → ℝ} {L T : ℝ≥0} (hf : LipschitzWith L f) (hg : LipschitzWith T g) (t : Time) :
    Integrable (fun γ => gamma m f g (γ t)) π := by
  have hfS := localSobolev_of_lipschitz hfin hf
  have hgS := localSobolev_of_lipschitz hfin hg
  apply hπ.integrable_eval_bounded (gamma_aestronglyMeasurable hfin hfS hgS).aemeasurable (B := (L:ℝ)*T)
  filter_upwards [abs_gamma_le hfin hpar hfS hgS,weakGradient_le_lipschitz hfin hf,
    weakGradient_le_lipschitz hfin hg,weakGradient_nonneg (m := m) g] with x h hx hy hn
  exact h.trans (mul_le_mul hx hy hn L.coe_nonneg)

lemma IsTestPlan.perturbation_energy (hfin : FiniteOnBoundedSets m)
    (hpar : LocalGradientParallelogram m) {π : Measure (Curve X)} (hπ : IsTestPlan m π)
    {f g : X → ℝ} {L T : ℝ≥0} (hf : LipschitzWith L f) (hg : LipschitzWith T g)
    (t : Time) (a : ℝ) :
    (∫ γ, (weakGradient m (fun x => f x+a*g x) (γ t))^2 ∂π) =
      (∫ γ, (weakGradient m f (γ t))^2 ∂π)+2*a*(∫ γ,gamma m f g (γ t) ∂π)+
      a^2*(∫ γ, (weakGradient m g (γ t))^2 ∂π) := by
  rw [integral_congr_ae (hπ.ae_eval_of_ae
    (weakGradient_linear_combination_sq hfin hpar
      (localSobolev_of_lipschitz hfin hf) (localSobolev_of_lipschitz hfin hg) a) t)]
  have hi1 := hπ.integrable_gradient_energy hfin hf t
  have hi2 := (hπ.integrable_gamma_eval hfin hpar hf hg t).const_mul (2*a)
  have hi3 := (hπ.integrable_gradient_energy hfin hg t).const_mul (a^2)
  have hi12 := hi1.add hi2
  change Integrable (fun γ => (weakGradient m f (γ t))^2+2*a*gamma m f g (γ t)) π at hi12
  rw [integral_add hi12 hi3,integral_add hi1 hi2,integral_const_mul,integral_const_mul]

lemma IsTestPlan.contact_gradient_energy_le (hfin : FiniteOnBoundedSets m)
    {π : Measure (Curve X)} (hπ : IsTestPlan m π) (hb : BoundedTracks π)
    {φ ψ : X → ℝ} {L : ℝ≥0} (hφ : LipschitzWith L φ)
    (hdual : ∀ x y, φ x+ψ y ≤ dist x y^2/2)
    (hcontact : ∀ᵐ γ ∂π, φ (γ timeZero)+ψ (γ timeOne) = dist (γ timeZero) (γ timeOne)^2/2) :
    (∫ γ, (weakGradient m φ (γ timeZero))^2 ∂π) ≤ ∫ γ, dist (γ timeZero) (γ timeOne)^2 ∂π := by
  let : IsProbabilityMeasure π := hπ.1
  apply integral_mono_ae (hπ.integrable_gradient_energy hfin hφ timeZero) hb.integrable_length_sq
  filter_upwards [hπ.ae_eval_of_ae (weakGradient_le_ascendingSlope hfin hφ) timeZero,
    hπ.ae_eval_of_ae (weakGradient_nonneg (m := m) φ) timeZero,hcontact] with γ hγ hn hc
  have H := (ENNReal.toReal_mono ENNReal.ofReal_ne_top (ascendingSlope_contact hdual hc)).trans_eq
    (ENNReal.toReal_ofReal dist_nonneg)
  exact (sq_le_sq₀ hn dist_nonneg).mpr (hγ.trans H)
end WeakHessian

namespace WeakHessianTransport
open Filter Set
open scoped Topology

lemma tendsto_of_quadratic_variations {ι : Type*} {l : Filter ι}
    {d : ι → ℝ} {B Q : ℝ}
    (h : ∀ a : ℝ, ∃ r : ι → ℝ, Tendsto r l (𝓝 (a*B+a^2*Q)) ∧
      ∀ᶠ i in l, a*d i ≤ r i) : Tendsto d l (𝓝 B) := by
  apply Metric.tendsto_nhds.mpr
  intro δ hδ
  let ε := δ/(2*(|Q|+1))
  have hε : 0 < ε := by dsimp [ε]; positivity
  have he : ε*|Q| < δ := by
    have H : |Q|/(2*(|Q|+1)) < 1 := (div_lt_one (by positivity)).mpr (by linarith [abs_nonneg Q])
    dsimp [ε]
    calc
      δ/(2*(|Q|+1))*|Q| = δ*(|Q|/(2*(|Q|+1))) := by ring
      _ < δ*1 := mul_lt_mul_of_pos_left H hδ
      _ = δ := mul_one _
  have heQ : ε^2*Q < ε*δ := by
    have H := mul_lt_mul_of_pos_left he hε
    have H' := mul_le_mul_of_nonneg_left (le_abs_self Q) (sq_nonneg ε)
    nlinarith
  obtain ⟨rp,hrp,hp⟩ := h ε
  obtain ⟨rn,hrn,hn⟩ := h (-ε)
  have ep := (tendsto_order.mp hrp).2 (ε*B+ε*δ) (by linarith)
  have en := (tendsto_order.mp hrn).2 (-ε*B+ε*δ) (by nlinarith)
  filter_upwards [ep,en,hp,hn] with i hip hin hip' hin'
  rw [Real.dist_eq,abs_lt]
  constructor <;> nlinarith
end WeakHessianTransport

end

end OAI
