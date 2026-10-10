import OAI.Geometry.RCD.Sobolev.HamiltonJacobiTimeBound
import OAI.Geometry.RCD.Sobolev.ScaledHamiltonJacobiGradient
import OAI.Geometry.RCD.Heat.ScaledHeatTimePairing
import OAI.Geometry.RCD.Metric.FixedGaugeScaledPotential

namespace OAI

/-! # Uniform time bounds for compact pairings of the actual heat potentials -/

open Set Filter MeasureTheory Metric TopologicalSpace
open scoped NNReal ENNReal Topology
noncomputable section
namespace RegularPointCoordinates.NoncollapsedRCD
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] {K : ℝ} {n : ℕ} (hX : NoncollapsedRCD K n X)
  (hn : 2 ≤ n) (p : X) [SeparableSpace X]
  [IsLocallyFiniteMeasure (hausdorff n X)] [(hausdorff n X).Regular]

theorem compact_heat_pairing_time_bound
    {S : Set X} [CompactSpace S] (ν : Measure S) [IsProbabilityMeasure ν]
    (ρ : X → ℝ) (hρ : Measurable ρ) (hρ0 : ∀ x, 0 ≤ ρ x) {B : ℝ≥0}
    (hB : ∀ᵐ x ∂hausdorff n X, |ρ x| ≤ B)
    (hν : ν.map Subtype.val = (hausdorff n X).withDensity (fun x => ENNReal.ofReal (ρ x)))
    {δ : ℝ} (hδ : 0 < δ) (z : X) {R r : ℝ} (hR : 0 ≤ R)
    (hdist : ∀ a : S, dist z a ≤ R) :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ (F : C(S, ℝ)), (∀ a, 0 < F a) →
      ∀ (ε : ℝ) (hε : 0 < ε), ε ≤ 1 →
      ∀ φ : SobolevSpace (hausdorff n X) hX.quadratic,
      (∀ᵐ x ∂hausdorff n X, x ∉ closedBall z r →
        SobolevSpace.toLp (hausdorff n X) hX.quadratic φ x = 0) →
      ∀ Bφ : ℝ, (∀ᵐ x ∂hausdorff n X,
        |SobolevSpace.toLp (hausdorff n X) hX.quadratic φ x| ≤ Bφ) →
      ∀ s ∈ Icc δ 1, ∀ t ∈ Icc δ 1,
      |(∫ x in closedBall z r, SobolevSpace.toLp (hausdorff n X) hX.quadratic φ x *
          hX.fixedGaugeScaledPotential hn p ν F ε hε δ hδ z t x ∂hausdorff n X) -
        (∫ x in closedBall z r, SobolevSpace.toLp (hausdorff n X) hX.quadratic φ x *
          hX.fixedGaugeScaledPotential hn p ν F ε hε δ hδ z s x ∂hausdorff n X)| ≤
      (ε/2 * (L * ∫ x, SobolevSpace.minimalSlope (hausdorff n X) hX.quadratic φ x ∂hausdorff n X) +
        L^2/2 * ∫ x in closedBall z r, |SobolevSpace.toLp (hausdorff n X) hX.quadratic φ x|
          ∂hausdorff n X) * |t-s| := by
  classical
  let μ := hausdorff n X
  let Q := hX.quadratic
  obtain ⟨C,D,hC,hD,hdata⟩ := hX.compact_heat_scaled_equation_gradient hn p
  let A := Real.exp |K| * (4*C/δ+16*D*(R+r)^2/δ^2)
  have hA : 0 ≤ A := by dsimp only [A]; positivity
  let L := Real.sqrt A
  have hL : 0 ≤ L := Real.sqrt_nonneg A
  refine ⟨L,hL,?_⟩
  intro F hF ε hε hε1 φ hφs Bφ hBφ s hs t ht
  let H := fun t x => ε * Real.log
    (∫ a, hX.canonicalHeatKernel hn p (ε*t/2) x a * F a ∂ν)
  obtain ⟨Dt,hH,hDt,hd⟩ := hX.compact_heat_scaled_time_data hn p ν ρ hρ hρ0 hB hν F hF hε
  choose v d hv hval hder hg using fun u : Icc δ 1 =>
    hdata ν ρ hρ hρ0 hB hν F hF hε hε1 hδ u.property.1 u.property.2
      z R hR hdist (closedBall z r) (isCompact_closedBall z r)
  let w := fun u => if hu : u ∈ Icc δ 1 then v ⟨u,hu⟩ else 0
  let q := fun u => if hu : u ∈ Icc δ 1 then d ⟨u,hu⟩ else 0
  have hG (u : Icc δ 1) : ∀ᵐ x ∂μ.restrict (closedBall z r),
      SobolevSpace.minimalSlope μ Q (v u) x ≤ L := by
    filter_upwards [hg u,ae_restrict_mem measurableSet_closedBall] with x hx hmem
    have hxD : dist z x ≤ r := by simpa only [dist_comm] using mem_closedBall.mp hmem
    have hpow : (R+dist z x)^2 ≤ (R+r)^2 :=
      pow_le_pow_left₀ (add_nonneg hR dist_nonneg) (by linarith) 2
    have hb : (SobolevSpace.minimalSlope μ Q (v u) x)^2 ≤ A := hx.trans (by
      apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
      have hpart : 16*D*(R+dist z x)^2/δ^2 ≤ 16*D*(R+r)^2/δ^2 :=
        div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_left hpow (show 0 ≤ 16*D by positivity)) (sq_nonneg δ)
      exact add_le_add le_rfl hpart)
    have hsq : L^2 = A := Real.sq_sqrt hA
    nlinarith
  have hlocal (u : ℝ) (hu : u ∈ Icc δ 1) : IsWeakLaplacian μ Q (w u) (q u) ∧
      (Dt u =ᵐ[μ.restrict (closedBall z r)] fun x =>
        ε/2*q u x + localGamma μ Q (w u) (w u) x/2) ∧
      ∀ᵐ x ∂μ.restrict (closedBall z r), SobolevSpace.minimalSlope μ Q (w u) x ≤ L := by
    simp only [w,q,dite_eq_left hu]
    refine ⟨hv ⟨u,hu⟩,?_,hG ⟨u,hu⟩⟩
    filter_upwards [hder ⟨u,hu⟩] with x hx
    exact (hd u (hδ.trans_le hu.1) x).unique hx
  let c := ε * Real.log (hX.compactHeatFactor hn p ν F ε hε z)
  have hcenter : ContinuousOn (fun tx : ℝ × X => H tx.1 tx.2-c) (Ioi 0 ×ˢ univ) :=
    hH.sub continuousOn_const
  have hh := hamilton_jacobi_pairing_time_bound μ Q (fun u x => H u x-c) Dt
    hcenter hDt (fun u hu x => (hd u hu x).sub_const c) (isCompact_closedBall z r) hδ
    w q ε L hlocal φ hφs hBφ hs ht
  have he (u : ℝ) (hu : u ∈ Icc δ 1) (x : X) :
      hX.fixedGaugeScaledPotential hn p ν F ε hε δ hδ z u x = H u x-c := by
    rw [hX.fixedGaugeScaledPotential_eq hn p ν F ε hε δ hδ z hu.1 x]
    rfl
  simpa only [abs_of_pos hε,← he t ht,← he s hs] using hh

end RegularPointCoordinates.NoncollapsedRCD

end

end OAI
