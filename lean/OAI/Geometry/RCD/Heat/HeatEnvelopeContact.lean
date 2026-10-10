import OAI.Geometry.RCD.Heat.FixedHeatEnvelope
import OAI.Geometry.RCD.Transport.CompactQuadraticContact

namespace OAI

/-! # Compact contact potentials for the actual interior heat envelope -/

open Set Filter MeasureTheory Metric TopologicalSpace
open scoped NNReal ENNReal Topology
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]

namespace HeatActionLimit

omit [BorelSpace X] in
theorem negative_slice_lipschitz {p : X} (H : HeatActionLimit p)
    {t : ℝ} (ht : t ∈ Ioo (0:ℝ) 1) {r : ℝ} (hr : 0 < r) :
    ∃ L : ℝ≥0, LipschitzOnWith L (fun x => -t*H.potential t x) (closedBall p r) := by
  obtain ⟨L,hL⟩ := H.local_lipschitz r hr (t/2) (half_pos ht.1)
  refine ⟨⟨t*(L:ℝ),mul_nonneg ht.1.le L.coe_nonneg⟩,?_⟩
  apply LipschitzOnWith.of_dist_le_mul
  intro x hx y hy
  have ht' : t ∈ Ioo (t/2) 1 := ⟨by linarith [ht.1],ht.2⟩
  have hh := hL.dist_le_mul (t,x) ⟨ht',hx⟩ (t,y) ⟨ht',hy⟩
  simp only [Function.uncurry_apply_pair,Prod.dist_eq,dist_self,max_eq_right dist_nonneg] at hh
  change dist (-t*H.potential t x) (-t*H.potential t y) ≤ (t*(L:ℝ))*dist x y
  rw [Real.dist_eq,show -t*H.potential t x- -t*H.potential t y =
    -t*(H.potential t x-H.potential t y) by ring,abs_mul,abs_neg,abs_of_pos ht.1]
  rw [Real.dist_eq] at hh
  calc
    _ ≤ t*((L:ℝ)*dist x y) := mul_le_mul_of_nonneg_left hh ht.1.le
    _ = _ := by ring

end HeatActionLimit

namespace NoncollapsedRCD.CompactHeatScalingData
variable [ProperSpace X] {K : ℝ} {n : ℕ} {hX : NoncollapsedRCD K n X}
  {hn : 2 ≤ n} {p : X} [SeparableSpace X]
  [IsLocallyFiniteMeasure (hausdorff n X)] [(hausdorff n X).Regular]
  {S T : Set X} [CompactSpace S] [CompactSpace T]
  {μ : Measure S} {ν : Measure T} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
  {ε : ℕ → ℝ} {hε : ∀ k, 0 < ε k}
  (D : hX.CompactHeatScalingData hn p μ ν ε hε)

theorem forward_compact_contacts (a₀ : S) (hK : K ≤ 0)
    (hε0 : Tendsto ε atTop (𝓝 0)) {R : ℝ} (hR : 0 ≤ R)
    (hdS : ∀ a : S, dist p a ≤ R) {t : ℝ} (ht : t ∈ Ioo (0:ℝ) 1)
    {r₀ : ℝ} (hr₀ : 0 ≤ r₀) :
    ∃ (M r : ℝ) (ψ : X → ℝ) (L : ℝ≥0),
      LipschitzWith L ψ ∧ HasCompactSupport ψ ∧
      (∀ x, r < dist p x → ψ x = 0) ∧
      LipschitzWith L (hopfLax (-ψ) 1) ∧ HasCompactSupport (hopfLax (-ψ) 1) ∧
      (∀ x y, hopfLax (-ψ) 1 x+ψ y ≤ dist x y^2/2) ∧
      (∀ x ∈ closedBall p r₀, hopfLax (-ψ) 1 x = -t*D.forward.potential t x-M) ∧
      ∀ x ∈ closedBall p r₀, ∀ a ∈ μ.support,
        D.forward.potential t x = D.leftPotential a₀ a-dist x (a:X)^2/(2*t)-
          D.forwardGauge a₀ hK hε0 hR hdS →
        hopfLax (-ψ) 1 x+ψ a = dist x (a:X)^2/2 := by
  have henv := D.forward_gauge_envelope a₀ hK hε0 hR hdS
  let A := D.forwardGauge a₀ hK hε0 hR hdS
  let point : μ.support → X := fun a => a.val.val
  let F : μ.support → ℝ := fun a => D.leftPotential a₀ a.val
  let Φ : X → ℝ := fun x => -t*D.forward.potential t x
  have hform (x : X) (a : S)
      (ha : D.forward.potential t x = D.leftPotential a₀ a-dist x (a:X)^2/(2*t)-A) :
      Φ x = dist x (a:X)^2/2-t*D.leftPotential a₀ a+t*A := by
    dsimp [Φ]
    rw [ha]
    field_simp [ht.1.ne']
    ring
  have hu (x : X) (a : μ.support) :
      Φ x ≤ dist x (point a)^2/2-t*F a+t*A := by
    obtain ⟨c,_,hmax,hc⟩ := henv t ht x
    have hh := hmax a.val a.property
    have he : dist x (point a)^2/2-t*F a+t*A =
        -t*(D.leftPotential a₀ a.val-dist x (a.val:X)^2/(2*t)-A) := by
      dsimp [point,F]
      field_simp [ht.1.ne']
      ring
    rw [he]
    dsimp [Φ]
    rw [hc]
    exact mul_le_mul_of_nonpos_left (sub_le_sub_right hh A) (neg_nonpos.mpr ht.1.le)
  have he (x : X) : ∃ a : μ.support, Φ x = dist x (point a)^2/2-t*F a+t*A := by
    obtain ⟨a,ha,_,hval⟩ := henv t ht x
    exact ⟨⟨a,ha⟩,hform x a hval⟩
  have hF (a : μ.support) : F a ≤ ‖D.leftPotential a₀‖ :=
    (le_abs_self _).trans ((D.leftPotential a₀).norm_coe_le_norm a.val)
  obtain ⟨M,r,ψ,L,hψ,hψs,hψ0,hχ,hχs,had,hlocal,hcontact⟩ :=
    compact_quadratic_contact hX.geodesic p point F hR ht.1 hF (fun a => hdS a.val)
      Φ hu he (fun _ hr => D.forward.negative_slice_lipschitz ht hr) hr₀
  refine ⟨M,r,ψ,L,hψ,hψs,hψ0,hχ,hχs,had,hlocal,?_⟩
  intro x hx a ha hav
  exact hcontact x hx ⟨a,ha⟩ (hform x a hav)

end NoncollapsedRCD.CompactHeatScalingData
end RegularPointCoordinates

end

end OAI
