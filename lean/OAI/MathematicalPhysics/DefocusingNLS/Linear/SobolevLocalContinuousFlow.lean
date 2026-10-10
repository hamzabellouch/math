import OAI.MathematicalPhysics.DefocusingNLS.Nonlinear.MaximalStrongSolution

namespace OAI

/-! # A jointly continuous local Sobolev solution map -/

open Filter Topology Set Metric
open scoped NNReal

namespace DefocusingNLS

/-- Every bounded ball of initial data has a jointly continuous interaction flow on a common
positive time interval. The flow solves the actual polynomial interaction equation. -/
theorem exists_continuous_sobolevInteractionFlow_on_ball
    (k : ℝ) (hk : 6 < k) (m : ℕ) (R : ℝ) (hR : 0 ≤ R) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ α : FourierL2 × ℝ → FourierL2,
      ContinuousOn α (closedBall 0 R ×ˢ Icc (-δ) δ) ∧
      ∀ f : FourierL2, ‖f‖ ≤ R → α (f, 0) = f ∧
        ∀ t ∈ Ioo (-δ) δ, HasDerivAt (fun s => α (f, s))
          (schrodingerInteractionField k hk m t (α (f, t))) t := by
  obtain ⟨A, K, hA, hK, hbound, hlip⟩ :=
    exists_schrodingerInteractionField_ball_bounds k hk m (R + 1) (by linarith)
  let δ : ℝ := 1 / (A + 1)
  have hδ : 0 < δ := by dsimp [δ]; positivity
  let τ₀ : Icc (-δ) δ := ⟨0, by constructor <;> linarith⟩
  have hpl : IsPicardLindelof (schrodingerInteractionField k hk m)
      τ₀ 0 ⟨R + 1, by linarith⟩ ⟨R, hR⟩ ⟨A, hA⟩ ⟨K, hK⟩ := by
    constructor
    · intro t ht
      apply LipschitzOnWith.of_dist_le_mul
      intro f hf g hg
      rw [dist_eq_norm, dist_eq_norm]
      change ‖schrodingerInteractionField k hk m t f -
        schrodingerInteractionField k hk m t g‖ ≤ K * ‖f - g‖
      have hfn : ‖f‖ ≤ R + 1 := by
        rw [mem_closedBall, dist_zero_right] at hf
        change ‖f‖ ≤ R + 1 at hf
        exact hf
      have hgn : ‖g‖ ≤ R + 1 := by
        rw [mem_closedBall, dist_zero_right] at hg
        change ‖g‖ ≤ R + 1 at hg
        exact hg
      exact hlip t f g hfn hgn
    · intro f hf
      exact ((continuous_schrodingerInteractionField k hk m).comp
        (continuous_id.prodMk continuous_const)).continuousOn
    · intro t ht f hf
      apply hbound t f
      rw [mem_closedBall, dist_zero_right] at hf
      change ‖f‖ ≤ R + 1 at hf
      exact hf
    · change A * max (δ - 0) (0 - (-δ)) ≤ (R + 1) - R
      simp only [sub_zero, sub_neg_eq_add, zero_add, max_self]
      have hr : (R + 1) - R = 1 := by ring
      rw [hr]
      dsimp [δ]
      rw [mul_one_div]
      apply (div_le_iff₀ (by positivity : 0 < A + 1)).2
      linarith
  obtain ⟨α, hsol, hcont⟩ := hpl.exists_forall_mem_closedBall_eq_hasDerivWithinAt_continuousOn
  refine ⟨δ, hδ, α, hcont, ?_⟩
  intro f hf
  have hfball : f ∈ closedBall (0 : FourierL2) (⟨R, hR⟩ : ℝ≥0) := by simpa using hf
  refine ⟨(hsol f hfball).1, ?_⟩
  intro t ht
  exact ((hsol f hfball).2 t (Ioo_subset_Icc_self ht)).hasDerivAt (Icc_mem_nhds ht.1 ht.2)

/-- The local interaction map agrees with the maximal interaction flow on the common interval. -/
theorem exists_continuous_maximalSobolevInteractionFlow_on_ball
    (k : ℝ) (hk : 6 < k) (m : ℕ) (R : ℝ) (hR : 0 ≤ R) :
    ∃ δ : ℝ, 0 < δ ∧
      (∀ f : FourierL2, ‖f‖ ≤ R →
        Ioo (-δ) δ ⊆ maximalSobolevInteractionDomain k hk m f) ∧
      ContinuousOn (fun p : FourierL2 × ℝ => maximalSobolevInteractionFlow k hk m p.1 p.2)
        (closedBall 0 R ×ˢ Ioo (-δ) δ) := by
  obtain ⟨δ, hδ, α, hcont, hsol⟩ :=
    exists_continuous_sobolevInteractionFlow_on_ball k hk m R hR
  let P (f : FourierL2) (hf : ‖f‖ ≤ R) : SobolevInteractionPatch k hk m f :=
    { left := -δ
      right := δ
      left_neg := by linarith
      right_pos := hδ
      curve := fun t => α (f, t)
      initial := (hsol f hf).1
      solves := (hsol f hf).2 }
  have heq : EqOn (fun p : FourierL2 × ℝ => maximalSobolevInteractionFlow k hk m p.1 p.2)
      α (closedBall 0 R ×ˢ Ioo (-δ) δ) := by
    intro p hp
    exact maximalSobolevInteractionFlow_eq_patch (P p.1 (by simpa using hp.1)) hp.2
  have hV : ContinuousOn
      (fun p : FourierL2 × ℝ => maximalSobolevInteractionFlow k hk m p.1 p.2)
      (closedBall 0 R ×ˢ Ioo (-δ) δ) :=
    hcont.congr_mono heq (fun p hp => ⟨hp.1, Ioo_subset_Icc_self hp.2⟩)
  exact ⟨δ, hδ, fun f hf => (P f hf).subset_maximalDomain, hV⟩

/-- The actual maximal physical flow is jointly continuous in the datum and time on one
common interval for every bounded ball of initial data. -/
theorem exists_continuous_maximalSobolevSchrodingerFlow_on_ball
    (k : ℝ) (hk : 6 < k) (m : ℕ) (R : ℝ) (hR : 0 ≤ R) :
    ∃ δ : ℝ, 0 < δ ∧
      (∀ f : FourierL2, ‖f‖ ≤ R →
        Ioo (-δ) δ ⊆ maximalSobolevInteractionDomain k hk m f) ∧
      ContinuousOn (fun p : FourierL2 × ℝ => maximalSobolevSchrodingerFlow k hk m p.1 p.2)
        (closedBall 0 R ×ˢ Ioo (-δ) δ) := by
  obtain ⟨δ, hδ, hdom, hV⟩ :=
    exists_continuous_maximalSobolevInteractionFlow_on_ball k hk m R hR
  refine ⟨δ, hδ, hdom, ?_⟩
  intro p hp
  have hpair : ContinuousWithinAt
      (fun q : FourierL2 × ℝ => (q.2, maximalSobolevInteractionFlow k hk m q.1 q.2))
      (closedBall 0 R ×ˢ Ioo (-δ) δ) p :=
    continuous_snd.continuousWithinAt.prodMk (hV p hp)
  exact ContinuousAt.comp_continuousWithinAt
    (f := fun q : FourierL2 × ℝ => (q.2, maximalSobolevInteractionFlow k hk m q.1 q.2))
    (g := fun q : ℝ × FourierL2 => schrodingerFlow q.1 q.2)
    (continuous_schrodingerFlow_uncurry.continuousAt
      (x := (p.2, maximalSobolevInteractionFlow k hk m p.1 p.2))) hpair

end DefocusingNLS

end OAI
