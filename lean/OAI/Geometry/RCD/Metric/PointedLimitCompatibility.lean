import OAI.Geometry.RCD.Metric.PointedFunctionCompactness

namespace OAI

/-! # Compatibility of local limits through a pointed approximation

Density of the prescribed coordinate maps identifies two continuous limits
whenever the source representatives coincide on the interior ball.
-/

open Set Metric Filter
open scoped NNReal Topology
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X]

theorem pointed_limits_eqOn {n : ℕ} {S T : ℝ} (hTS : T≤S)
    (p : ℕ → X) (r ε : ℕ → ℝ) (v : ℕ → X → Euclidean n)
    (hr : ∀ k, 0<r k) (_hε : ∀ k, 0≤ε k) (hεlim : Tendsto ε atTop (𝓝 0))
    (hv : ∀ k, IsPointedApproximation (p k) 0 (r k) S (ε k) (v k))
    (u w : ℕ → X → ℝ) {g h : Euclidean n → ℝ} {L M : ℝ≥0}
    (hg : LipschitzWith L g) (hh : LipschitzWith M h)
    (heq : ∀ k x, dist x (p k)<T*r k → u k x=w k x)
    (hu : ∀ η : ℝ, 0<η → ∀ᶠ k in atTop, ∀ x, dist x (p k)≤S*r k →
      |u k x-g (v k x)|<η)
    (hw : ∀ η : ℝ, 0<η → ∀ᶠ k in atTop, ∀ x, dist x (p k)≤S*r k →
      |w k x-h (v k x)|<η) : EqOn g h (ball 0 T) := by
  intro z hz
  have hzT : ‖z‖<T := by simpa only [mem_ball,dist_zero_right] using hz
  apply sub_eq_zero.mp
  apply abs_eq_zero.mp
  apply le_antisymm _ (abs_nonneg _)
  apply le_of_forall_pos_le_add
  intro η hη
  have hbound : ∀ᶠ k in atTop,
      |g z-h z|≤((L:ℝ)+M)*ε k+2*(η/2) := by
    filter_upwards [hu (η/2) (half_pos hη),hw (η/2) (half_pos hη),
      hεlim.eventually (Iio_mem_nhds (show 0<(T-‖z‖)/4 by linarith))] with k huk hwk hek
    have hzs : dist z (0:Euclidean n)≤S-ε k := by
      rw [dist_zero_right]
      linarith
    obtain ⟨x,hx,hxz⟩ := (hv k).2.2 z hzs
    have hratio : dist x (p k)/r k<T := by
      have hab := (abs_le.mp ((hv k).2.1 x (p k) hx
        (by simpa only [dist_self] using mul_nonneg (by linarith [norm_nonneg z]) (hr k).le))).1
      have ht := dist_triangle (v k x) z 0
      have ht' := dist_triangle (v k x) 0 (v k (p k))
      have hcen := (hv k).1
      rw [dist_comm 0 (v k (p k))] at ht'
      simp only [dist_zero_right] at ht ht' hcen
      nlinarith
    have he := heq k x ((div_lt_iff₀ (hr k)).mp hratio)
    have hug := huk x hx
    have hwh := hwk x hx
    have hgz : |g z-g (v k x)|≤(L:ℝ)*ε k := by
      have ht := hg.dist_le_mul z (v k x)
      rw [Real.dist_eq] at ht
      exact ht.trans (mul_le_mul_of_nonneg_left (by simpa only [dist_comm] using hxz) L.coe_nonneg)
    have hhz : |h (v k x)-h z|≤(M:ℝ)*ε k := by
      have ht := hh.dist_le_mul (v k x) z
      rw [Real.dist_eq] at ht
      exact ht.trans (mul_le_mul_of_nonneg_left hxz M.coe_nonneg)
    have hmid : |g (v k x)-h (v k x)|≤2*(η/2) := by
      rw [he] at hug
      have ht := abs_sub_le (g (v k x)) (w k x) (h (v k x))
      rw [abs_sub_comm] at hug
      linarith
    have ht := abs_sub_le (g z) (g (v k x)) (h z)
    have ht' := abs_sub_le (g (v k x)) (h (v k x)) (h z)
    nlinarith only [hgz,hhz,hmid,ht,ht']
  have hlim : Tendsto (fun k => ((L:ℝ)+M)*ε k+2*(η/2)) atTop (𝓝 η) := by
    convert (hεlim.const_mul ((L:ℝ)+M)).add_const (2*(η/2)) using 1; ring_nf
  simpa only [zero_add] using ge_of_tendsto hlim hbound

end RegularPointCoordinates

end

end OAI
