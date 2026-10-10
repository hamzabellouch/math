import OAI.Geometry.RCD.Transport.DiagonalHopfRecoverySlope
import OAI.Geometry.RCD.Transport.CompactHopfDirichlet

namespace OAI

/-! # Actual compact Dirichlet sequences with the sharp local differential bound -/

open Set Metric Filter MeasureTheory
open scoped ContDiff Topology NNReal
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]

theorem NoncollapsedRCD.hopf_dirichlet_sequence_supported {K : ℝ} {n : ℕ}
    (hX : NoncollapsedRCD K n X) {S b c : ℝ} (hbc : b<c) (hcS : c<S)
    {ψ : Euclidean n → ℝ} {M : ℝ≥0}
    (hψ : ContDiff ℝ 1 ψ) (hψs : HasCompactSupport ψ) (hψL : LipschitzWith M ψ)
    (p : ℕ → X) (r ε : ℕ → ℝ) (v : ℕ → X → Euclidean n) (F : ℕ → X → ℝ)
    (hr : ∀ k, 0<r k) (hε : ∀ k, 0≤ε k) (hεlim : Tendsto ε atTop (𝓝 0))
    (hv : ∀ k, IsPointedApproximation (p k) 0 (r k) S (ε k) (v k))
    (hF : ∀ k, LipschitzWith ⟨(M:ℝ)/r k,div_nonneg M.coe_nonneg (hr k).le⟩ (F k))
    (hFs : ∀ k, tsupport (F k)⊆closedBall (p k) (b*r k))
    (hFe : ∀ k x, dist x (p k)≤S*r k → |F k x-ψ (v k x)|≤(M:ℝ)*ε k) :
    ∃ N : ℕ, ∃ w : ∀ k : ℕ, SobolevSpace.dirichlet (hausdorff n X) hX.quadratic
        (ball (p (k+N)) (S*r (k+N))),
      (∀ η : ℝ, 0<η → ∀ᶠ k in atTop,
        ∀ᵐ x ∂(hausdorff n X).restrict (ball (p (k+N)) (S*r (k+N))),
          |SobolevSpace.toLp (hausdorff n X) hX.quadratic (w k).val x-ψ (v (k+N) x)|≤η) ∧
      (∀ ρ : ℝ, 0≤ρ → ρ<S → ∀ η : ℝ, 0<η → ∀ᶠ k in atTop,
        ∀ᵐ x ∂(hausdorff n X).restrict (ball (p (k+N)) (ρ*r (k+N))),
          r (k+N)*SobolevSpace.minimalSlope (hausdorff n X) hX.quadratic (w k).val x≤
            ‖fderiv ℝ ψ (v (k+N) x)‖+η) ∧
      ∀ k, ∀ᵐ x ∂hausdorff n X, x∉ball (p (k+N)) (c*r (k+N)) →
        SobolevSpace.toLp (hausdorff n X) hX.quadratic (w k).val x=0 := by
  let μ := hausdorff n X
  let : IsLocallyFiniteMeasure μ := locallyFinite_of_finiteOnBounded μ hX.finiteOnBounded
  let t := hopfRecoveryTime ε
  have ht : ∀ k, 0<t k := hopfRecoveryTime_pos ε
  have htlim : Tendsto t atTop (𝓝 0) := hopfRecoveryTime_tendsto hεlim
  have hratio : Tendsto (fun k => ε k/t k) atTop (𝓝 0) := error_div_hopfRecoveryTime_tendsto hεlim hε
  have heratio : Tendsto (fun k => (M:ℝ)*ε k/t k) atTop (𝓝 0) := by
    simpa only [mul_div_assoc,mul_zero] using hratio.const_mul (M:ℝ)
  have hroomlim : Tendsto (fun k => b+2*t k*(M:ℝ)) atTop (𝓝 b) := by
    simpa only [mul_zero,zero_mul,add_zero] using ((htlim.const_mul 2).mul_const (M:ℝ)).const_add b
  obtain ⟨N,hN⟩ := eventually_atTop.mp (hroomlim.eventually (Iio_mem_nhds hbc))
  have hrec (k : ℕ) := compact_hopf_dirichlet μ hX.quadratic hX.geodesic
    (hr (k+N)) (ht (k+N)) ((hN (k+N) (Nat.le_add_left N k)).trans hcS) (hF (k+N)) (hFs (k+N))
  choose w hw hws using hrec
  refine ⟨N,w,?_,?_,?_⟩
  · have herrorlim : Tendsto (fun k => (M:ℝ)*ε k+t k*(M:ℝ)^2/2) atTop (𝓝 0) := by
      simpa only [mul_zero,zero_mul,zero_div,zero_add] using
        (hεlim.const_mul (M:ℝ)).add ((htlim.mul_const ((M:ℝ)^2)).div_const 2)
    intro η hη
    have hev := (tendsto_add_atTop_nat N).eventually (herrorlim.eventually (Iio_mem_nhds hη))
    filter_upwards [hev] with k hk
    filter_upwards [ae_restrict_of_ae (hw k),ae_restrict_mem measurableSet_ball] with x hx hball
    rw [hx]
    obtain ⟨hlo,hhi⟩ := hopfLax_bounds (hF (k+N)) (mul_pos (ht (k+N)) (sq_pos_of_pos (hr (k+N)))) x
    have he := abs_le.mp (hFe (k+N) x hball.le)
    have hid : (t (k+N)*r (k+N)^2)*((M:ℝ)/r (k+N))^2/2=t (k+N)*(M:ℝ)^2/2 := by
      field_simp [(hr (k+N)).ne']
    change F (k+N) x-(t (k+N)*r (k+N)^2)*((M:ℝ)/r (k+N))^2/2≤_ at hlo
    rw [hid] at hlo
    exact abs_le.mpr ⟨by linarith,by linarith⟩
  · intro ρ hρ hρS η hη
    have hbase := diagonal_hopf_recovery_slope hψ hψs hψL hρ hρS p r ε
      (fun k => (M:ℝ)*ε k) t v F hr hε (fun k => mul_nonneg M.coe_nonneg (hε k)) ht
      hεlim htlim hratio heratio hv hF hFe η hη
    filter_upwards [(tendsto_add_atTop_nat N).eventually hbase] with k hk
    filter_upwards [ae_restrict_of_ae (hws k),ae_restrict_mem measurableSet_ball] with x hx hball
    exact (mul_le_mul_of_nonneg_left hx (hr (k+N)).le).trans (hk x hball.le)

  · intro k
    filter_upwards [hw k] with x hx hnot
    rw [hx]
    apply hopfLax_zero_outside (hF (k+N)) (p (k+N)) (b*r (k+N))
      (fun y hy => ?_) (mul_pos (ht (k+N)) (sq_pos_of_pos (hr (k+N))))
    · have hd : c*r (k+N)≤dist (p (k+N)) x := by
        simpa only [mem_ball,dist_comm,not_lt] using hnot
      have hb := mul_lt_mul_of_pos_right (hN (k+N) (Nat.le_add_left N k)) (hr (k+N))
      have heq : b*r (k+N)+2*(t (k+N)*r (k+N)^2)*((M:ℝ)/r (k+N))=
          (b+2*t (k+N)*(M:ℝ))*r (k+N) := by field_simp
      change b*r (k+N)+2*(t (k+N)*r (k+N)^2)*((M:ℝ)/r (k+N))<dist (p (k+N)) x
      rw [heq]
      exact hb.trans_le hd
    · by_contra hne
      have hh := hFs (k+N) (subset_tsupport (F (k+N)) hne)
      rw [mem_closedBall,dist_comm] at hh
      linarith

end RegularPointCoordinates

end

end OAI
