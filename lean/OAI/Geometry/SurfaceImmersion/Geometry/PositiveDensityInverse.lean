import OAI.Geometry.SurfaceImmersion.Geometry.PositiveDensityClock

namespace OAI

/-! A positive density's circle diffeomorphism has a jointly smooth inverse. -/
noncomputable section
open Filter Set
open scoped ContDiff Topology

namespace ClosedSurfaceR4.PositiveDensity

variable {B : Type} [NormedAddCommGroup B] [NormedSpace ℝ B] [FiniteDimensional ℝ B]
  {ρ : B × ℝ → ℝ} {U : Set B}

def inverseClock (ρ : B × ℝ → ℝ) (b : B) (θ : ℝ) : ℝ :=
  Function.invFun (clock ρ b) θ

omit [FiniteDimensional ℝ B] in
lemma clock_inverseClock (hU : IsOpen U) (hρ : ContDiffOn ℝ ∞ ρ (U ×ˢ univ))
    (hper : ∀ b ∈ U, Function.Periodic (fun t => ρ (b, t)) 1)
    (hmass : ∀ b ∈ U, (∫ t in 0..1, ρ (b, t)) = 1) {b : B} (hb : b ∈ U) (θ : ℝ) :
    clock ρ b (inverseClock ρ b θ) = θ :=
  Function.rightInverse_invFun (clock_surjective hU hρ hper hmass hb) θ

omit [FiniteDimensional ℝ B] in
lemma inverseClock_clock (hU : IsOpen U) (hρ : ContDiffOn ℝ ∞ ρ (U ×ˢ univ))
    (hpos : ∀ b ∈ U, ∀ t, 0 < ρ (b, t)) {b : B} (hb : b ∈ U) (t : ℝ) :
    inverseClock ρ b (clock ρ b t) = t :=
  Function.leftInverse_invFun (clock_strictMono hU hρ hpos hb).injective t

omit [FiniteDimensional ℝ B] in
lemma inverseClock_period (hU : IsOpen U) (hρ : ContDiffOn ℝ ∞ ρ (U ×ˢ univ))
    (hpos : ∀ b ∈ U, ∀ t, 0 < ρ (b, t))
    (hper : ∀ b ∈ U, Function.Periodic (fun t => ρ (b, t)) 1)
    (hmass : ∀ b ∈ U, (∫ t in 0..1, ρ (b, t)) = 1) {b : B} (hb : b ∈ U) (θ : ℝ) :
    inverseClock ρ b (θ + 1) = inverseClock ρ b θ + 1 := by
  apply (clock_strictMono hU hρ hpos hb).injective
  rw [clock_inverseClock hU hρ hper hmass hb, clock_period hU hρ hper hmass hb,
    clock_inverseClock hU hρ hper hmass hb]

private def equation (ρ : B × ℝ → ℝ) (z : (B × ℝ) × ℝ) : ℝ :=
  clock ρ z.1.1 z.2 - z.1.2

private lemma equation_smoothOn (hU : IsOpen U) (hρ : ContDiffOn ℝ ∞ ρ (U ×ˢ univ)) :
    ContDiffOn ℝ ∞ (equation ρ) ((U ×ˢ univ) ×ˢ univ) := by
  exact ((clock_smoothOn hU hρ).comp
    (contDiffOn_fst.fst.prodMk contDiffOn_snd) (fun z hz => ⟨hz.1.1, mem_univ _⟩)).sub
    contDiffOn_fst.snd

private lemma equation_partial (hU : IsOpen U) (hρ : ContDiffOn ℝ ∞ ρ (U ×ˢ univ))
    {b : B} (hb : b ∈ U) (θ t : ℝ) :
    fderiv ℝ (equation ρ) ((b, θ), t) ∘L ContinuousLinearMap.inr ℝ (B × ℝ) ℝ =
      ContinuousLinearMap.toSpanSingleton ℝ (ρ (b, t)) := by
  have hc : ContDiffAt ℝ ∞ (equation ρ) ((b, θ), t) :=
    (equation_smoothOn hU hρ).contDiffAt
      (((hU.prod isOpen_univ).prod isOpen_univ).mem_nhds ⟨⟨hb, mem_univ θ⟩, mem_univ t⟩)
  have hi : HasFDerivAt (fun s : ℝ => ((b, θ), s))
      (ContinuousLinearMap.inr ℝ (B × ℝ) ℝ) t := hasFDerivAt_prodMk_right (b, θ) t
  have hcomp := (hc.differentiableAt (by simp)).hasFDerivAt.comp t hi
  exact hcomp.unique ((hasDerivAt_clock hU hρ hb t).sub_const θ).hasFDerivAt

private lemma equation_partial_invertible (hU : IsOpen U)
    (hρ : ContDiffOn ℝ ∞ ρ (U ×ˢ univ))
    (hpos : ∀ b ∈ U, ∀ t, 0 < ρ (b, t)) {b : B} (hb : b ∈ U) (θ t : ℝ) :
    (fderiv ℝ (equation ρ) ((b, θ), t) ∘L ContinuousLinearMap.inr ℝ (B × ℝ) ℝ).IsInvertible := by
  rw [equation_partial hU hρ hb]
  apply ContinuousLinearMap.IsInvertible.of_inverse
    (g := ContinuousLinearMap.toSpanSingleton ℝ (ρ (b, t))⁻¹)
  · ext
    simp [ContinuousLinearMap.toSpanSingleton_apply, (hpos b hb t).ne']
  · ext
    simp [ContinuousLinearMap.toSpanSingleton_apply, (hpos b hb t).ne']

/-- No regularity of the inverse is assumed: it follows from positivity and the IFT. -/
theorem inverseClock_smoothOn (hU : IsOpen U) (hρ : ContDiffOn ℝ ∞ ρ (U ×ˢ univ))
    (hpos : ∀ b ∈ U, ∀ t, 0 < ρ (b, t))
    (hper : ∀ b ∈ U, Function.Periodic (fun t => ρ (b, t)) 1)
    (hmass : ∀ b ∈ U, (∫ t in 0..1, ρ (b, t)) = 1) :
    ContDiffOn ℝ ∞ (fun z : B × ℝ => inverseClock ρ z.1 z.2) (U ×ˢ univ) := by
  apply (hU.prod isOpen_univ).contDiffOn_iff.mpr
  intro z hz
  let u : (B × ℝ) × ℝ := (z, inverseClock ρ z.1 z.2)
  have hu : u ∈ (U ×ˢ univ) ×ˢ univ := ⟨hz, mem_univ _⟩
  have hc := (equation_smoothOn hU hρ).contDiffAt
    (((hU.prod isOpen_univ).prod isOpen_univ).mem_nhds hu)
  have hn : (∞ : ℕ∞ω) ≠ 0 := by simp
  have hi := equation_partial_invertible hU hρ hpos hz.1 z.2 (inverseClock ρ z.1 z.2)
  have hs := hc.contDiffAt_implicitFunction hn hi
  have he := hc.eventually_apply_implicitFunction hn hi
  have hnear : ∀ᶠ w : B × ℝ in 𝓝 z, w.1 ∈ U :=
    continuous_fst.continuousAt.eventually (hU.mem_nhds hz.1)
  have heq : (fun w : B × ℝ => inverseClock ρ w.1 w.2) =ᶠ[𝓝 z]
      hc.implicitFunction hn hi := by
    filter_upwards [he, hnear] with w hw hwu
    apply (clock_strictMono hU hρ hpos hwu).injective
    rw [clock_inverseClock hU hρ hper hmass hwu]
    change clock ρ w.1 (hc.implicitFunction hn hi w) - w.2 =
      clock ρ z.1 (inverseClock ρ z.1 z.2) - z.2 at hw
    rw [clock_inverseClock hU hρ hper hmass hz.1, sub_self] at hw
    exact (sub_eq_zero.mp hw).symm
  exact hs.congr_of_eventuallyEq heq

end ClosedSurfaceR4.PositiveDensity

end

end OAI
