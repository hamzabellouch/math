import OAI.Geometry.RCD.Sobolev.LipschitzCompactSubsequence

namespace OAI

/-! # Function compactness over the actual pointed metric maps -/

open Set Metric Filter
open scoped NNReal Topology
noncomputable section
namespace RegularPointCoordinates
variable {X Y : Type*} [MetricSpace X] [MetricSpace Y]

theorem pointed_metric_function_transfer {p : X} {q : Y} {r S ε T A : ℝ}
    (hr : 0<r) (hS : 0≤S) (hε : 0≤ε) (hε1 : ε≤1)
    {v : X → Y} (hv : IsPointedApproximation p q r S ε v)
    (u : X → ℝ) (L : ℝ≥0)
    (hu : ∀ x, dist x p ≤ S*r → |u x| ≤ A)
    (hl : ∀ x z, dist x p ≤ S*r → dist z p ≤ S*r →
      |u x-u z| ≤ (L:ℝ)*(dist x z/r)) :
    ∃ g : Y → ℝ, LipschitzWith L g ∧
      (∀ x, dist x p ≤ S*r → |g (v x)-u x| ≤ L*ε) ∧
      (∀ y, dist y q ≤ T → |g y| ≤ A+L*(T+2)) := by
  let s := closedBall p (S*r)
  have hp : p ∈ s := mem_closedBall_self (mul_nonneg hS hr.le)
  have hApprox : ∀ x ∈ s, ∀ z ∈ s, |u x-u z| ≤ L*dist (v x) (v z)+L*ε := by
    intro x hx z hz
    have hd := (abs_le.mp (hv.2.1 x z hx hz)).1
    have hm := mul_le_mul_of_nonneg_left (show dist x z/r ≤ dist (v x) (v z)+ε by linarith) L.coe_nonneg
    exact (hl x z hx hz).trans (by nlinarith only [hm])
  obtain ⟨g,hg,hgu⟩ := exists_lipschitz_metric_transfer ⟨p,hp⟩ u v L
    (mul_nonneg L.coe_nonneg hε) (fun x hx => (neg_le_neg (hu x hx)).trans (neg_abs_le (u x)))
    hApprox
  refine ⟨g,hg,hgu,?_⟩
  intro y hy
  have hgp : |g (v p)| ≤ A+L := by
    have ht := abs_add_le (g (v p)-u p) (u p)
    have hb := hgu p hp
    have hc := mul_le_mul_of_nonneg_left hε1 L.coe_nonneg
    have hpA := hu p hp
    simp only [sub_add_cancel] at ht
    linarith
  have hd : dist y (v p) ≤ T+1 := by
    have hvp : dist (v p) q ≤ ε := hv.1
    calc dist y (v p) ≤ dist y q+dist q (v p) := dist_triangle _ _ _
      _ ≤ T+1 := by simpa only [dist_comm q (v p)] using add_le_add hy (hvp.trans hε1)
  have hgd : |g y-g (v p)| ≤ L*dist y (v p) := by
    simpa only [Real.dist_eq] using hg.dist_le_mul y (v p)
  have hgdist : |g y-g (v p)| ≤ L*(T+1) :=
    hgd.trans (mul_le_mul_of_nonneg_left hd L.coe_nonneg)
  have ht := abs_add_le (g y-g (v p)) (g (v p))
  simp only [sub_add_cancel] at ht
  nlinarith only [ht,hgdist,hgp]


theorem pointed_metric_function_compactness [ProperSpace Y] {q : Y} {S A : ℝ} (hS : 0≤S)
    (p : ℕ → X) (r ε : ℕ → ℝ) (v : ℕ → X → Y)
    (hr : ∀ k, 0<r k) (hε : ∀ k, 0≤ε k) (hε1 : ∀ k, ε k≤1)
    (hεlim : Tendsto ε atTop (𝓝 0))
    (hv : ∀ k, IsPointedApproximation (p k) q (r k) S (ε k) (v k))
    (u : ℕ → X → ℝ) (L : ℝ≥0)
    (hu : ∀ k x, dist x (p k)≤S*r k → |u k x|≤A)
    (hl : ∀ k x z, dist x (p k)≤S*r k → dist z (p k)≤S*r k →
      |u k x-u k z|≤(L:ℝ)*(dist x z/r k)) :
    ∃ (g : Y → ℝ) (a : ℕ → ℕ), StrictMono a ∧ LipschitzWith L g ∧
      ∀ η : ℝ, 0<η → ∀ᶠ k in atTop, ∀ x, dist x (p (a k))≤S*r (a k) →
        |u (a k) x-g (v (a k) x)|<η := by
  choose F hF hFu hFb using fun k => pointed_metric_function_transfer (hr k) hS
    (hε k) (hε1 k) (T := S+2) (hv k) (u k) L (hu k) (hl k)
  obtain ⟨g,a,ha,hg,_,hlim⟩ := exists_lipschitz_subsequence_on_compact
    (isCompact_closedBall q (S+2)) F L (A+L*(S+4)) hF
    (fun k z hz => by
      have hz' : dist z q≤S+2 := hz
      simpa only [show S+2+2=S+4 by ring] using hFb k z hz')
  have hsmall : Tendsto (fun k => (L:ℝ)*ε (a k)) atTop (𝓝 0) := by
    simpa only [mul_zero,Function.comp_def] using (hεlim.comp ha.tendsto_atTop).const_mul (L:ℝ)
  refine ⟨g,a,ha,hg,?_⟩
  intro η hη
  filter_upwards [hlim (η/2) (half_pos hη),hsmall.eventually (Iio_mem_nhds (half_pos hη))]
    with k hk he
  intro x hx
  have hnorm : dist (v (a k) x) q≤S+2 := by
    have hcenter := (hv (a k)).1
    have hd := (abs_le.mp ((hv (a k)).2.1 x (p (a k)) hx
      (by simpa only [dist_self] using mul_nonneg hS (hr (a k)).le))).2
    have hx' : dist x (p (a k))/r (a k) ≤ S := (div_le_iff₀ (hr (a k))).mpr hx
    have htri := dist_triangle (v (a k) x) (v (a k) (p (a k))) q
    linarith [hε1 (a k)]
  have hclose := hk (v (a k) x) hnorm
  have hsource := hFu (a k) x hx
  have ht := abs_add_le (u (a k) x-F (a k) (v (a k) x))
    (F (a k) (v (a k) x)-g (v (a k) x))
  rw [abs_sub_comm] at hsource
  simp only [sub_add_sub_cancel] at ht
  linarith

end RegularPointCoordinates

end

end OAI
