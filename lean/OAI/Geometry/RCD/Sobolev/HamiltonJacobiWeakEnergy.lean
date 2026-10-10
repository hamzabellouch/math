import OAI.Geometry.RCD.Harmonic.CenteredHamiltonJacobiPairing
import OAI.Geometry.RCD.Heat.CompactSubsetTimePairing

namespace OAI

/-! # Exact integrated gradient energy of the viscous potentials

The local Sobolev representatives need no assumed time regularity. Their
weighted energy is identified with continuous value/source pairings.
-/

open Set Filter MeasureTheory Metric
open scoped Interval Topology ENNReal
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] (μ : Measure X) [IsFiniteMeasureOnCompacts μ] (Q : QuadraticCheegerEnergy μ)

omit [ProperSpace X] [IsFiniteMeasureOnCompacts μ] in
private theorem compact_set_pairing_continuous (H : ℝ → X → ℝ)
    (hH : ContinuousOn (Function.uncurry H) (Ioi 0 ×ˢ univ))
    {Ω : Set X} (hΩ : IsCompact Ω) (v : X → ℝ) (hv : IntegrableOn v Ω μ)
    {a b : ℝ} (ha : 0 < a) :
    ContinuousOn (fun t => ∫ x in Ω, v x*H t x ∂μ) (Icc a b) := by
  let : CompactSpace Ω := isCompact_iff_compactSpace.mp hΩ
  have hv' : Integrable (fun x : Ω => v x) (μ.comap Subtype.val) :=
    (integrableOn_iff_comap_subtypeVal hΩ.measurableSet).mp hv
  have hsub : Icc a b ×ˢ (univ : Set Ω) ⊆ Ioi 0 ×ˢ univ :=
    fun q hq => ⟨ha.trans_le hq.1.1,hq.2⟩
  have hh := compact_time_pairing_continuousOn (μ.comap Subtype.val)
    (fun t (x : Ω) => H t x) ((continuousOn_time_subtype hH Ω).mono hsub) (fun x => v x) hv'
  have he (t : ℝ) : (∫ x : Ω, v x*H t x ∂μ.comap Subtype.val) =
      ∫ x in Ω, v x*H t x ∂μ := integral_subtype_comap hΩ.measurableSet (fun x => v x*H t x)
  simpa only [he] using hh

theorem hamilton_jacobi_weak_energy
    (H D : ℝ → X → ℝ)
    (hH : ContinuousOn (Function.uncurry H) (Ioi 0 ×ˢ univ))
    (hD : ContinuousOn (Function.uncurry D) (Ioi 0 ×ˢ univ))
    (hd : ∀ t, 0 < t → ∀ x, HasDerivAt (fun s => H s x) (D t x) t)
    (w : ℝ → SobolevSpace μ Q) (q : ℝ → Lp ℝ 2 μ)
    (z : X) {r a b : ℝ} (hr : 0 < r) (ha : 0 < a) (hab : a ≤ b) (ε c : ℝ)
    (hlocal : ∀ t ∈ Icc a b, IsWeakLaplacian μ Q (w t) (q t) ∧
      (SobolevSpace.toLp μ Q (w t) =ᵐ[μ.restrict (closedBall z r)] H t) ∧
      (D t =ᵐ[μ.restrict (closedBall z r)] fun x => ε/2*q t x + localGamma μ Q (w t) (w t) x/2))
    (φ : SobolevSpace μ Q) (ξ : Lp ℝ 2 μ) (hξ : IsWeakLaplacian μ Q φ ξ)
    (hφs : ∀ᵐ x ∂μ, x ∉ closedBall z r → SobolevSpace.toLp μ Q φ x = 0)
    (hξs : ∀ᵐ x ∂μ, x ∉ closedBall z r → ξ x = 0)
    {B : ℝ} (hB : ∀ᵐ x ∂μ, |SobolevSpace.toLp μ Q φ x| ≤ B)
    (θ θ' : ℝ → ℝ) (hθ : ContinuousOn θ (Icc a b)) (hθ' : ContinuousOn θ' (Icc a b))
    (hder : ∀ t ∈ Ioo a b, HasDerivAt θ (θ' t) t) (hθa : θ a = 0) (hθb : θ b = 0) :
    (∫ t in a..b, θ t * ∫ x in closedBall z r,
      SobolevSpace.toLp μ Q φ x * localGamma μ Q (w t) (w t) x ∂μ) =
      -2*(∫ t in a..b, θ' t * ∫ x in closedBall z r,
        SobolevSpace.toLp μ Q φ x * (H t x-c) ∂μ) -
      ε*(∫ t in a..b, θ t * ∫ x in closedBall z r, ξ x * (H t x-c) ∂μ) := by
  let Ω := closedBall z r
  let Φ := SobolevSpace.toLp μ Q φ
  have hΩ : IsCompact Ω := isCompact_closedBall z r
  have hiΦ : IntegrableOn Φ Ω μ := lp_integrableOn_of_finite μ Φ Ω hΩ.measure_lt_top.ne
  have hiξ : IntegrableOn ξ Ω μ := lp_integrableOn_of_finite μ ξ Ω hΩ.measure_lt_top.ne
  have hcenter : ContinuousOn (fun tx : ℝ × X => H tx.1 tx.2-c) (Ioi 0 ×ˢ univ) :=
    hH.sub continuousOn_const
  have hPD := compact_set_pairing_continuous μ D hD hΩ Φ hiΦ (b := b) ha
  have hPV := compact_set_pairing_continuous μ (fun t x => H t x-c)
    hcenter hΩ ξ hiξ (b := b) ha
  have hiPD : IntervalIntegrable (fun t => θ t * ∫ x in Ω, Φ x*D t x ∂μ) volume a b :=
    (hθ.mul hPD).intervalIntegrable_of_Icc hab
  have hiPV : IntervalIntegrable (fun t => θ t * ∫ x in Ω, ξ x*(H t x-c) ∂μ) volume a b :=
    (hθ.mul hPV).intervalIntegrable_of_Icc hab
  have hpoint (t : ℝ) (ht : t ∈ Icc a b) :
      (∫ x in Ω, Φ x*localGamma μ Q (w t) (w t) x ∂μ) =
        2*(∫ x in Ω, Φ x*D t x ∂μ)-ε*(∫ x in Ω, ξ x*(H t x-c) ∂μ) :=
    local_centered_hamilton_jacobi_test_pairing μ Q (w t) φ (q t) ξ (hlocal t ht).1
      hξ z hr (H t) (D t) ε c (hlocal t ht).2.1 (hlocal t ht).2.2 hφs hξs hB
  have he : (∫ t in a..b, θ t * ∫ x in Ω, Φ x*localGamma μ Q (w t) (w t) x ∂μ) =
      2*(∫ t in a..b, θ t * ∫ x in Ω, Φ x*D t x ∂μ)-
        ε*(∫ t in a..b, θ t * ∫ x in Ω, ξ x*(H t x-c) ∂μ) := by
    calc
      _ = ∫ t in a..b, 2*(θ t * ∫ x in Ω, Φ x*D t x ∂μ)-
          ε*(θ t * ∫ x in Ω, ξ x*(H t x-c) ∂μ) := by
        apply intervalIntegral.integral_congr
        intro t ht
        rw [uIcc_of_le hab] at ht
        dsimp only
        rw [hpoint t ht]
        ring
      _ = _ := by
        rw [intervalIntegral.integral_sub (hiPD.const_mul 2) (hiPV.const_mul ε),
          intervalIntegral.integral_const_mul,intervalIntegral.integral_const_mul]
  have hiΦ' : Integrable (fun x : Ω => Φ x) (μ.comap Subtype.val) :=
    (integrableOn_iff_comap_subtypeVal hΩ.measurableSet).mp hiΦ
  have hwk := compact_subset_time_pairing_weak_equation (fun t x => H t x-c) D
    hcenter hD (fun t ht x => (hd t ht x).sub_const c) Ω hΩ (μ.comap Subtype.val)
    (fun x => Φ x) hiΦ' ha hab θ θ' hθ hθ' hder hθa hθb
  have heD (t : ℝ) : (∫ x : Ω, Φ x*D t x ∂μ.comap Subtype.val) =
      ∫ x in Ω, Φ x*D t x ∂μ := integral_subtype_comap hΩ.measurableSet (fun x => Φ x*D t x)
  have heH (t : ℝ) : (∫ x : Ω, Φ x*(H t x-c) ∂μ.comap Subtype.val) =
      ∫ x in Ω, Φ x*(H t x-c) ∂μ := integral_subtype_comap hΩ.measurableSet (fun x => Φ x*(H t x-c))
  simp only [heD,heH] at hwk
  rw [he,hwk]
  ring

end RegularPointCoordinates

end

end OAI
