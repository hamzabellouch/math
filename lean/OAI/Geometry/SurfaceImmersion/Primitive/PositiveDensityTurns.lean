import OAI.Geometry.SurfaceImmersion.Geometry.PositiveDensityReparam

namespace OAI

/-! Positive changes of circle coordinate preserve stationary points and their spatial jets. -/
noncomputable section
open Set
open scoped ContDiff Topology

namespace ClosedSurfaceR4.PositiveDensity

variable {B : Type} [NormedAddCommGroup B] [NormedSpace ℝ B] [FiniteDimensional ℝ B]
  {ρ : B × ℝ → ℝ} {U : Set B}

lemma hasDerivAt_inverseClock (hU : IsOpen U) (hρ : ContDiffOn ℝ ∞ ρ (U ×ˢ univ))
    (hpos : ∀ b ∈ U, ∀ t, 0 < ρ (b, t))
    (hper : ∀ b ∈ U, Function.Periodic (fun t => ρ (b, t)) 1)
    (hmass : ∀ b ∈ U, (∫ t in 0..1, ρ (b, t)) = 1) {b : B} (hb : b ∈ U) (θ : ℝ) :
    HasDerivAt (inverseClock ρ b) (ρ (b, inverseClock ρ b θ))⁻¹ θ := by
  have hi : Differentiable ℝ (inverseClock ρ b) :=
    (LocalPeriodicCalculus.smooth_slice hU
      (inverseClock_smoothOn hU hρ hpos hper hmass) hb).differentiable (by simp)
  have hc := (hasDerivAt_clock hU hρ hb (inverseClock ρ b θ)).comp θ (hi θ).hasDerivAt
  have hid : (fun x => clock ρ b (inverseClock ρ b x)) = id :=
    funext (clock_inverseClock hU hρ hper hmass hb)
  change HasDerivAt (fun x => clock ρ b (inverseClock ρ b x)) _ θ at hc
  rw [hid] at hc
  have heq : ρ (b, inverseClock ρ b θ) * deriv (inverseClock ρ b) θ = 1 :=
    hc.unique (hasDerivAt_id θ)
  convert (hi θ).hasDerivAt using 1
  apply mul_left_cancel₀ (hpos b hb (inverseClock ρ b θ)).ne'
  rw [mul_inv_cancel₀ (hpos b hb (inverseClock ρ b θ)).ne', heq]

lemma deriv_reparametrize_eq_zero_iff
    (hU : IsOpen U) (hρ : ContDiffOn ℝ ∞ ρ (U ×ˢ univ))
    (hpos : ∀ b ∈ U, ∀ t, 0 < ρ (b, t))
    (hper : ∀ b ∈ U, Function.Periodic (fun t => ρ (b, t)) 1)
    (hmass : ∀ b ∈ U, (∫ t in 0..1, ρ (b, t)) = 1)
    {F : B × ℝ → ℝ} (hF : ContDiffOn ℝ ∞ F (U ×ˢ univ))
    {b : B} (hb : b ∈ U) (θ : ℝ) :
    deriv (fun t => reparametrize ρ F (b, t)) θ = 0 ↔
      deriv (fun t => F (b, t)) (inverseClock ρ b θ) = 0 := by
  have hf := (LocalPeriodicCalculus.smooth_slice hU hF hb).differentiable (by simp)
  have hd := (hf (inverseClock ρ b θ)).hasDerivAt.comp θ
    (hasDerivAt_inverseClock hU hρ hpos hper hmass hb θ)
  change deriv ((fun t => F (b, t)) ∘ inverseClock ρ b) θ = 0 ↔ _
  rw [hd.deriv]
  simp [(hpos b hb (inverseClock ρ b θ)).ne']

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- At a turn, the extra spatial chain-rule term from the inverse clock is zero. -/
theorem spatial_derivative_at_turn
    (hU : IsOpen U) (hρ : ContDiffOn ℝ ∞ ρ (U ×ˢ univ))
    (hpos : ∀ b ∈ U, ∀ t, 0 < ρ (b, t))
    (hper : ∀ b ∈ U, Function.Periodic (fun t => ρ (b, t)) 1)
    (hmass : ∀ b ∈ U, (∫ t in 0..1, ρ (b, t)) = 1)
    {F : B × ℝ → E} (hF : ContDiffOn ℝ ∞ F (U ×ˢ univ))
    {b : B} (hb : b ∈ U) (θ : ℝ)
    (hzero : fderiv ℝ F (b, inverseClock ρ b θ) (0, 1) = 0) (v : B) :
    fderiv ℝ (fun x => reparametrize ρ F (x, θ)) b v =
      fderiv ℝ (fun x => F (x, inverseClock ρ b θ)) b v := by
  have hInv : ContDiffAt ℝ ∞ (fun z : B × ℝ => inverseClock ρ z.1 z.2) (b, θ) :=
    (inverseClock_smoothOn hU hρ hpos hper hmass).contDiffAt
    ((hU.prod isOpen_univ).mem_nhds ⟨hb, mem_univ θ⟩)
  have hi : DifferentiableAt ℝ (fun x => inverseClock ρ x θ) b :=
    (hInv.comp b (contDiff_id.prodMk contDiff_const).contDiffAt).differentiableAt (by simp)
  have hF' : DifferentiableAt ℝ F (b, inverseClock ρ b θ) :=
    (hF.contDiffAt ((hU.prod isOpen_univ).mem_nhds ⟨hb, mem_univ _⟩)).differentiableAt (by simp)
  have hd := hF'.hasFDerivAt.comp b ((hasFDerivAt_id b).prodMk hi.hasFDerivAt)
  have hf := hF'.hasFDerivAt.comp b (hasFDerivAt_prodMk_left (𝕜 := ℝ) b (inverseClock ρ b θ))
  simp only [id_eq] at hd
  change fderiv ℝ (F ∘ fun x => (x, inverseClock ρ x θ)) b v =
    fderiv ℝ (F ∘ fun x => (x, inverseClock ρ b θ)) b v
  rw [hd.fderiv, hf.fderiv]
  change fderiv ℝ F (b, inverseClock ρ b θ)
    (v, fderiv ℝ (fun x => inverseClock ρ x θ) b v) =
      fderiv ℝ F (b, inverseClock ρ b θ) (v, 0)
  rw [show (v, fderiv ℝ (fun x => inverseClock ρ x θ) b v) =
    (v, 0) + (fderiv ℝ (fun x => inverseClock ρ x θ) b v) • (0, 1) by simp]
  rw [map_add, map_smul, hzero, smul_zero, add_zero]

end ClosedSurfaceR4.PositiveDensity

end

end OAI
