import OAI.Probability.SLE.Gauge.RibbonCoordinateGeometry
import OAI.Probability.SLE.Geometry.RobustTransverseCrossing

namespace OAI

/-! Physical perturbations of a transverse ribbon route admit continuous
coordinate lifts. The fixed inverse Lipschitz bound then turns a physical
tube event into a forced hit of the actual stopped past. -/

noncomputable section
open Set Metric Function
open scoped Topology NNReal

namespace SLEExactGauge.RibbonCoordinates
open RectangleCrossing

theorem inverse_coordinate_lipschitz
    (P : ℂ → ℂ) (S : Set ℂ) (K : ℝ≥0)
    (hlower : ∀ u ∈ S, ∀ v ∈ S, dist u v ≤ K * dist (P u) (P v)) :
    LipschitzOnWith K (invFunOn P S) (P '' S) := by
  apply lipschitzOnWith_iff_dist_le_mul.mpr
  intro u hu v hv
  have hh := hlower _ (invFunOn_mem hu) _ (invFunOn_mem hv)
  simpa only [invFunOn_eq hu, invFunOn_eq hv] using hh

/-- Invariance of domain supplies a physical tube; the patch inverse is
continuous with exactly the given inverse Lipschitz bound. -/
theorem physical_tube_has_coordinate_lift
    (hpublished : PublishedPlanarDiskOpenness)
    (P : ℂ → ℂ) (S : Set ℂ) (hP : ContinuousOn P S) (hi : InjOn P S)
    (K : ℝ≥0) (hK : 0 < (K : ℝ))
    (hlower : ∀ u ∈ S, ∀ v ∈ S, dist u v ≤ K * dist (P u) (P v))
    (ξ ζ : ℝ → ℂ) (I : Set ℝ) {r : ℝ} (hr : 0 < r)
    (hξ : ∀ t ∈ I, closedBall (ξ t) r ⊆ S)
    (hζ : ContinuousOn ζ I)
    (hnear : ∀ t ∈ I, dist (ζ t) (P (ξ t)) < r / K) :
    let q := invFunOn P S ∘ ζ
    ContinuousOn q I ∧ MapsTo q I S ∧ EqOn (P ∘ q) ζ I ∧
      ∀ t ∈ I, dist (q t) (ξ t) < r := by
  have hlift t (ht : t ∈ I) :
      ∃ z ∈ ball (ξ t) r, P z = ζ t := by
    apply ball_subset_image_ball P (ξ t) hr hK (hP.mono (hξ t ht))
      (hpublished P _ _ hr (hP.mono (ball_subset_closedBall.trans (hξ t ht)))
        (hi.mono (ball_subset_closedBall.trans (hξ t ht))))
      (fun z hz => hlower z (hξ t ht hz) _ (hξ t ht (mem_closedBall_self hr.le)))
    exact hnear t ht
  have hζS : MapsTo ζ I (P '' S) := by
    intro t ht
    obtain ⟨z, hz, he⟩ := hlift t ht
    exact ⟨z, hξ t ht (ball_subset_closedBall hz), he⟩
  dsimp only
  refine ⟨(inverse_coordinate_lipschitz P S K hlower).continuousOn.comp hζ hζS,
    (fun t ht => invFunOn_mem (hζS ht)), (fun t ht => invFunOn_eq (hζS ht)), ?_⟩
  intro t ht
  obtain ⟨z, hz, he⟩ := hlift t ht
  have hzS := hξ t ht (ball_subset_closedBall hz)
  have heq : invFunOn P S (ζ t) = z :=
    hi (invFunOn_mem (hζS ht)) hzS ((invFunOn_eq (hζS ht)).trans he.symm)
  simpa only [Function.comp_apply, heq, mem_ball] using hz

def crossingPatch (k : ℝ) : Set ℂ :=
  {z | k - 1 ≤ z.re ∧ z.re ≤ k + 1 ∧ |z.im| ≤ 1}

theorem crossingPatch_subset_closedRibbon {k : ℝ} (hk : 1 ≤ k) :
    crossingPatch k ⊆ closedRibbon := by
  intro z hz
  exact ⟨by linarith [hz.1], hz.2.2⟩

theorem transverse_template_ball_subset_patch (k : ℝ) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    closedBall (transverseTemplate k t) (1 / 8) ⊆ crossingPatch k := by
  intro z hz
  have hn : ‖z - transverseTemplate k t‖ ≤ 1 / 8 := by
    simpa only [mem_closedBall, dist_eq_norm] using hz
  have hre := (Complex.abs_re_le_norm (z - transverseTemplate k t)).trans hn
  have him := (Complex.abs_im_le_norm (z - transverseTemplate k t)).trans hn
  simp only [Complex.sub_re, Complex.sub_im, transverseTemplate, Complex.add_re,
    Complex.add_im, Complex.ofReal_re, Complex.ofReal_im, Complex.mul_re,
    Complex.mul_im, Complex.I_re, Complex.I_im, mul_zero, mul_one,
    add_zero, zero_add, sub_zero] at hre him
  have hr := abs_le.mp hre
  have hi := abs_le.mp him
  refine ⟨by linarith, by linarith, abs_le.mpr ⟨by linarith [ht.1], by linarith [ht.2]⟩⟩

/-- A single physical tube radius, independent of the past, forces a hit.
Every coordinate and continuity condition for the perturbed route is
derived from the actual patch embedding rather than assumed. -/
theorem physical_transverse_tube_hits_past
    (hpublished : PublishedPlanarDiskOpenness)
    (P : ℂ → ℂ) (hP : ContinuousOn P closedRibbon) (hi : InjOn P closedRibbon)
    (K : ℝ≥0) (hK : 0 < (K : ℝ)) {k ε T : ℝ}
    (hk : 1 ≤ k) (hε : 0 < ε) (hεsmall : ε ≤ 1 / 8) (hT : 0 < T)
    (hlower : ∀ u ∈ crossingPatch k, ∀ v ∈ crossingPatch k,
      dist u v ≤ K * dist (P u) (P v))
    (γ xp ζ : ℝ → ℂ) (hxp : ContinuousOn xp (Icc 0 T))
    (hγ : EqOn γ (P ∘ xp) (Icc 0 T))
    (hxp0 : (xp 0).re = 0) (hxpT : (xp T).re = k)
    (hcore : ∀ t ∈ Icc (0 : ℝ) T, |(xp t).im| ≤ ε)
    (hζ : ContinuousOn ζ (Icc 0 1))
    (hnear : ∀ t ∈ Icc (0 : ℝ) 1,
      dist (ζ t) (P (transverseTemplate k t)) < (1 / 8 : ℝ) / K) :
    ∃ s ∈ Icc (0 : ℝ) T, ∃ t ∈ Icc (0 : ℝ) 1, γ s = ζ t := by
  have hsub := crossingPatch_subset_closedRibbon hk
  obtain ⟨hq, _, hmap, hnearq⟩ := physical_tube_has_coordinate_lift hpublished
    P (crossingPatch k) (hP.mono hsub) (hi.mono hsub) K hK hlower
    (transverseTemplate k) ζ (Icc 0 1) (by norm_num : (0 : ℝ) < 1 / 8)
    (fun _ ht => transverse_template_ball_subset_patch k ht) hζ hnear
  obtain ⟨s, hs, t, ht, he⟩ := near_transverse_template_hits_past xp
    (invFunOn P (crossingPatch k) ∘ ζ) hT hk hε hεsmall le_rfl hxp hq
    hxp0 hxpT hcore hnearq
  exact ⟨s, hs, t, ht, (hγ hs).trans ((congrArg P he).trans (hmap ht))⟩

end SLEExactGauge.RibbonCoordinates

end

end OAI
