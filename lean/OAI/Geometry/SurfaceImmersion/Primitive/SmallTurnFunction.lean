import OAI.Geometry.SurfaceImmersion.Geometry.LocalDefiningFunction
import OAI.Geometry.SurfaceImmersion.Primitive.BlendedSpatialTurns

namespace OAI

/-! Choose the small translation of the angle with a large derivative at both
turns. Compactness bounds the endpoint-amplitude derivative before this choice. -/
noncomputable section
open Set
open scoped ContDiff

namespace ClosedSurfaceR4.CollarVelocity
open TransverseSmallFunction

/-- The two endpoint derivatives can be made arbitrarily large while the
translation itself is arbitrarily small. The geometric input is the checked
local curve-equation form of the finite-curve correction lemma. -/
theorem exists_small_turn_function {K O P : Set Base}
    (hK : IsCompact K) (hO : IsOpen O) (hKO : K ⊆ O)
    (hP : P.Finite) (hPK : P ⊆ K)
    (hlocal : ∀ p ∈ K \ P, ∃ U : Set Base, IsOpen U ∧ p ∈ U ∧
      ∃ f : Base → ℝ, ContDiffOn ℝ ∞ f U ∧ (∀ x ∈ K ∩ U, f x = 0) ∧
        fderiv ℝ f p (0, 1) ≠ 0)
    {a A s : Base → ℝ} (ha : ContDiff ℝ ∞ a)
    (hA : ContDiff ℝ ∞ A) (hs : ContDiff ℝ ∞ s) (T : ℝ)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ h : Base → ℝ, ContDiff ℝ ∞ h ∧ HasCompactSupport h ∧ tsupport h ⊆ O ∧
      (∀ x, |h x| < ε) ∧ ∀ x ∈ K,
        T < fderiv ℝ (fun y => h y + blendedAmplitude (a y) (A y) (s y)) x (0, 1) ∧
        T < fderiv ℝ (fun y => h y - blendedAmplitude (a y) (A y) (s y)) x (0, 1) := by
  let amp := fun y => blendedAmplitude (a y) (A y) (s y)
  have hamp : ContDiff ℝ ∞ amp := blendedAmplitude_smooth ha hA hs
  have hD : Continuous (fun x => fderiv ℝ amp x (0, 1)) :=
    ((hamp.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const).continuous
  obtain ⟨M, hM⟩ := hK.exists_bound_of_continuousOn hD.continuousOn
  obtain ⟨h, hh, hhc, hhs, hhb, hhd⟩ := small_value_prescribed_derivative
    hK hO hKO hP hPK hlocal (M + T + 1) hε
  refine ⟨h, hh, hhc, hhs, hhb, ?_⟩
  intro x hx
  have hb : |fderiv ℝ amp x (0, 1)| ≤ M := hM x hx
  have hlow := (abs_le.mp hb).1
  have hupp := (abs_le.mp hb).2
  have hp := hhd x hx
  have hd₁ := fderiv_fun_add (hh.differentiable (by simp) x)
    (hamp.differentiable (by simp) x)
  have hd₂ := fderiv_fun_sub (hh.differentiable (by simp) x)
    (hamp.differentiable (by simp) x)
  constructor
  · change T < fderiv ℝ (fun y => h y + amp y) x (0, 1)
    rw [hd₁, add_apply, hp]
    linarith
  · change T < fderiv ℝ (fun y => h y - amp y) x (0, 1)
    rw [hd₂, sub_apply, hp]
    linarith

/-- Any subsequently chosen positive density retains the large spatial derivatives. -/
theorem large_turns_after_reparametrization
    {a A s h : Base → ℝ} {K U : Set Base} {T : ℝ}
    (ha : ContDiff ℝ ∞ a) (hA : ContDiff ℝ ∞ A)
    (hs : ContDiff ℝ ∞ s) (hh : ContDiff ℝ ∞ h)
    (hU : IsOpen U) (hKU : K ⊆ U) {ρ : Base × ℝ → ℝ}
    (hρ : ContDiffOn ℝ ∞ ρ (U ×ˢ univ))
    (hpos : ∀ b ∈ U, ∀ t, 0 < ρ (b, t))
    (hper : ∀ b ∈ U, Function.Periodic (fun t => ρ (b, t)) 1)
    (hmass : ∀ b ∈ U, (∫ t in 0..1, ρ (b, t)) = 1)
    (hlarge : ∀ x ∈ K,
      T < fderiv ℝ (fun y => h y + blendedAmplitude (a y) (A y) (s y)) x (0, 1) ∧
      T < fderiv ℝ (fun y => h y - blendedAmplitude (a y) (A y) (s y)) x (0, 1)) :
    let F := fun z : Base × ℝ => unitAngle (a z.1) (A z.1) (s z.1) (h z.1) z.2
    ∀ x ∈ K,
      T < fderiv ℝ (fun y => PositiveDensity.reparametrize ρ F (y, 0)) x (0, 1) ∧
      T < fderiv ℝ (fun y => PositiveDensity.reparametrize ρ F
        (y, PositiveDensity.clock ρ x (1 / 2))) x (0, 1) := by
  intro F x hx
  obtain ⟨hd₁, hd₂⟩ := reparametrized_spatial_turns ha hA hs hh hU hρ hpos hper hmass
    (hKU hx) (0, 1)
  obtain ⟨h₁, h₂⟩ := hlarge x hx
  rw [fderiv_fun_add (hh.differentiable (by simp) x)
    ((blendedAmplitude_smooth ha hA hs).differentiable (by simp) x), add_apply] at h₁
  rw [fderiv_fun_sub (hh.differentiable (by simp) x)
    ((blendedAmplitude_smooth ha hA hs).differentiable (by simp) x), sub_apply] at h₂
  exact ⟨hd₁.symm ▸ h₁, hd₂.symm ▸ h₂⟩

end ClosedSurfaceR4.CollarVelocity

end

end OAI
