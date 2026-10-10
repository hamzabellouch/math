import OAI.MathematicalPhysics.DefocusingNLS.Linear.SobolevRestartExtension

namespace OAI

/-! # Neighborhoods of the maximal Sobolev flow -/

open Filter Topology Set Metric

namespace DefocusingNLS

/-- Existence for nearby data and times, together with joint continuity of the maximal flow. -/
def HasSobolevFlowNeighborhood (k : ℝ) (hk : 6 < k) (m : ℕ)
    (f : FourierL2) (t : ℝ) : Prop :=
  {p : FourierL2 × ℝ | p.2 ∈ maximalSobolevInteractionDomain k hk m p.1} ∈ 𝓝 (f, t) ∧
    ContinuousAt (fun p : FourierL2 × ℝ => maximalSobolevSchrodingerFlow k hk m p.1 p.2) (f, t)

theorem hasSobolevFlowNeighborhood_zero (k : ℝ) (hk : 6 < k) (m : ℕ) (f : FourierL2) :
    HasSobolevFlowNeighborhood k hk m f 0 := by
  obtain ⟨δ, hδ, hdom, hcont⟩ :=
    exists_continuous_maximalSobolevSchrodingerFlow_on_ball k hk m (‖f‖ + 1) (by positivity)
  have hb : closedBall (0 : FourierL2) (‖f‖ + 1) ∈ 𝓝 f :=
    mem_of_superset (isOpen_ball.mem_nhds (by simp : f ∈ ball (0 : FourierL2) (‖f‖ + 1)))
      ball_subset_closedBall
  have hi : Ioo (-δ) δ ∈ 𝓝 (0 : ℝ) := Ioo_mem_nhds (by linarith) hδ
  have hrect := prod_mem_nhds hb hi
  refine ⟨mem_of_superset hrect ?_, hcont.continuousAt hrect⟩
  intro p hp
  exact hdom p.1 (by simpa using hp.1) hp.2

/-- A common local flow on a ball propagates an existence/continuity neighborhood forward. -/
theorem HasSobolevFlowNeighborhood.advance
    (k : ℝ) (hk : 6 < k) (m : ℕ) (R δ : ℝ) (hδ : 0 < δ)
    (hdom : ∀ g : FourierL2, ‖g‖ ≤ R →
      Ioo (-δ) δ ⊆ maximalSobolevInteractionDomain k hk m g)
    (hcont : ContinuousOn
      (fun p : FourierL2 × ℝ => maximalSobolevSchrodingerFlow k hk m p.1 p.2)
      (closedBall 0 R ×ˢ Ioo (-δ) δ))
    (f : FourierL2) (s τ : ℝ) (hs : 0 ≤ s)
    (hf : HasSobolevFlowNeighborhood k hk m f s)
    (hR : ‖maximalSobolevSchrodingerFlow k hk m f s‖ < R)
    (hτ : τ ∈ Ioo 0 δ) : HasSobolevFlowNeighborhood k hk m f (s + τ) := by
  let v : FourierL2 → FourierL2 := fun g => maximalSobolevSchrodingerFlow k hk m g s
  have hstate : ContinuousAt v f := by
    have hp : ContinuousAt (fun g : FourierL2 => (g, s)) f :=
      (continuous_id.prodMk continuous_const).continuousAt
    exact ContinuousAt.comp
      (f := fun g : FourierL2 => (g, s))
      (g := fun p : FourierL2 × ℝ => maximalSobolevSchrodingerFlow k hk m p.1 p.2)
      hf.2 hp
  have hgdom : ∀ᶠ g : FourierL2 in 𝓝 f,
      s ∈ maximalSobolevInteractionDomain k hk m g :=
    (continuous_id.prodMk continuous_const).continuousAt.tendsto.eventually hf.1
  have hgnorm : ∀ᶠ g : FourierL2 in 𝓝 f, ‖v g‖ ≤ R := by
    have h := hstate.norm.tendsto.eventually (isOpen_Iio.mem_nhds hR)
    exact h.mono (fun g hg => le_of_lt hg)
  have hb : closedBall (0 : FourierL2) R ∈ 𝓝 (v f) :=
    mem_of_superset (isOpen_ball.mem_nhds (by simpa [v] using hR)) ball_subset_closedBall
  have hi : Ioo (-δ) δ ∈ 𝓝 τ := Ioo_mem_nhds (by linarith [hτ.1]) hτ.2
  have hlocal := hcont.continuousAt (prod_mem_nhds hb hi)
  have hparam : ContinuousAt (fun p : FourierL2 × ℝ => (v p.1, p.2 - s)) (f, s + τ) := by
    have hfirst : ContinuousAt (fun p : FourierL2 × ℝ => v p.1) (f, s + τ) :=
      ContinuousAt.comp (f := fun p : FourierL2 × ℝ => p.1) (g := v)
        hstate continuous_fst.continuousAt
    exact hfirst.prodMk (continuous_snd.sub continuous_const).continuousAt
  have hresult : ContinuousAt
      (fun p : FourierL2 × ℝ => maximalSobolevSchrodingerFlow k hk m (v p.1) (p.2 - s))
      (f, s + τ) := by
    have hlocal' : ContinuousAt
        (fun p : FourierL2 × ℝ => maximalSobolevSchrodingerFlow k hk m p.1 p.2)
        (v f, (s + τ) - s) := by simpa using hlocal
    exact ContinuousAt.comp
      (f := fun p : FourierL2 × ℝ => (v p.1, p.2 - s))
      (g := fun p : FourierL2 × ℝ => maximalSobolevSchrodingerFlow k hk m p.1 p.2)
      hlocal' hparam
  have hfst : Tendsto (fun p : FourierL2 × ℝ => p.1) (𝓝 (f, s + τ)) (𝓝 f) :=
    continuous_fst.tendsto (f, s + τ)
  have hgdom' : ∀ᶠ p : FourierL2 × ℝ in 𝓝 (f, s + τ),
      s ∈ maximalSobolevInteractionDomain k hk m p.1 :=
    hfst.eventually hgdom
  have hgnorm' : ∀ᶠ p : FourierL2 × ℝ in 𝓝 (f, s + τ), ‖v p.1‖ ≤ R :=
    hfst.eventually hgnorm
  have htime : ∀ᶠ p : FourierL2 × ℝ in 𝓝 (f, s + τ), p.2 - s ∈ Ico 0 δ := by
    have hmem : (s + τ) - s ∈ Ioo 0 δ := by simpa using hτ
    have hc : Continuous (fun p : FourierL2 × ℝ => p.2 - s) :=
      continuous_snd.sub continuous_const
    have h := (hc.tendsto (f, s + τ)).eventually (isOpen_Ioo.mem_nhds hmem)
    exact h.mono (fun p hp => ⟨hp.1.le, hp.2⟩)
  have hext : ∀ᶠ p : FourierL2 × ℝ in 𝓝 (f, s + τ),
      p.2 ∈ maximalSobolevInteractionDomain k hk m p.1 ∧
        maximalSobolevSchrodingerFlow k hk m p.1 p.2 =
          maximalSobolevSchrodingerFlow k hk m (v p.1) (p.2 - s) := by
    filter_upwards [hgdom', hgnorm', htime] with p hpd hpn hpt
    have hsub := hdom (v p.1) hpn
    have h := maximalSobolevSchrodingerFlow_restart_extension k hk m p.1 s δ hpd hs hδ
      (maximalSobolevSchrodingerFlow k hk m (v p.1))
      (maximalSobolevSchrodingerFlow_initial k hk m (v p.1))
      ((continuousOn_maximalSobolevSchrodingerFlow k hk m (v p.1)).mono hsub)
      (fun t ht => hasDerivAt_maximalSobolevSchrodingerFlow k hk m (v p.1) (hsub ht))
      (p.2 - s) hpt
    have hshift : s + (p.2 - s) = p.2 := by ring
    simpa only [hshift] using h
  exact ⟨hext.mono (fun p hp => hp.1), hresult.congr_of_eventuallyEq (hext.mono (fun p hp => hp.2))⟩

end DefocusingNLS

end OAI
