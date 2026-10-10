import OAI.Geometry.SurfaceImmersion.Primitive.CalibratedControlledAngle
import OAI.Geometry.SurfaceImmersion.Primitive.VelocityCoordinateData

namespace OAI

/-! Construct the actual four-dimensional velocity with exact mean and
metric, from its smooth geometric frame. -/
noncomputable section
open Set
open scoped ContDiff Matrix

namespace ClosedSurfaceR4.VelocityFrame
open NormalFrame RealModes TransverseSmallFunction

lemma scaled_coordinates_reconstruct {e₁ e₂ v : Vec} {R : ℝ} (hR : R ≠ 0)
    (hr : planeLift e₁ e₂ (planeCoordinates e₁ e₂ v) = v) :
    R • planeLift e₁ e₂ ![(v ⬝ᵥ e₁) / R, (v ⬝ᵥ e₂) / R] = v := by
  calc
    _ = planeLift e₁ e₂ (planeCoordinates e₁ e₂ v) := by
      ext i
      simp only [planeLift_apply, planeCoordinates, Matrix.cons_val_zero, Matrix.cons_val_one,
        Pi.smul_apply, Pi.add_apply, smul_eq_mul]
      field_simp
    _ = v := hr

theorem geometric_controlled_velocity {C₀ K L U Ω P : Set Base}
    (hC₀ : IsCompact C₀) (hK : IsCompact K) (hL : IsCompact L)
    (hCL : C₀ ⊆ L) (hKL : K ⊆ L) (hKU : Disjoint K (closure U))
    (hU : IsOpen U) (hΩ : IsOpen Ω) (hCU : C₀ ⊆ U) (hUΩ : U ⊆ Ω) (hLΩ : L ⊆ Ω)
    (hP : P.Finite) (hPK : P ⊆ K)
    (hlocal : ∀ p ∈ K \ P, ∃ N : Set Base, IsOpen N ∧ p ∈ N ∧
      ∃ f : Base → ℝ, ContDiffOn ℝ ∞ f N ∧ (∀ x ∈ K ∩ N, f x = 0) ∧
        fderiv ℝ f p (0, 1) ≠ 0)
    {X Y C v e₁ e₂ : Base → Vec} {a : Base → ℝ}
    (hv : ContDiffOn ℝ ∞ v Ω) (he₁ : ContDiffOn ℝ ∞ e₁ Ω)
    (he₂ : ContDiffOn ℝ ∞ e₂ Ω) (ha : ContDiffOn ℝ ∞ a Ω)
    (hD : ∀ x ∈ Ω, gramDet (Y x) (C x) ≠ 0)
    (hframe : ∀ x ∈ Ω, e₁ x ⬝ᵥ e₁ x = 1 ∧ e₂ x ⬝ᵥ e₂ x = 1 ∧ e₁ x ⬝ᵥ e₂ x = 0 ∧
      Y x ⬝ᵥ e₁ x = 0 ∧ C x ⬝ᵥ e₁ x = 0 ∧ Y x ⬝ᵥ e₂ x = 0 ∧ C x ⬝ᵥ e₂ x = 0)
    (hvproj : ∀ x ∈ Ω, v x = realNormalPart (Y x) (C x) (X x))
    (hcollar : ∀ x ∈ U, v x ≠ 0 ∧ e₁ x = normalize (v x))
    (hn : ∀ x ∈ Ω, v x ≠ 0 ∨ a x ≠ 0)
    (hap : ∀ x ∈ L \ C₀, 0 < a x) (T : ℝ) :
    ∃ Z : Set Base, IsOpen Z ∧ L ⊆ Z ∧ Z ⊆ Ω ∧
      ∃ α : Base × ℝ → ℝ, ContDiffOn ℝ ∞ α (Z ×ˢ univ) ∧
        (∀ x ∈ Z, Function.Periodic (fun t => α (x, t)) 1) ∧
        ∃ V : Base × ℝ → Vec, ContDiffOn ℝ ∞ V (Z ×ˢ univ) ∧
          (∀ z, V z = velocityRadius (v z.1) (a z.1) • direction (e₁ z.1) (e₂ z.1) (α z)) ∧
          (∀ x ∈ Z, (∫ t in 0..1, V (x, t)) = v x) ∧
          (∀ x ∈ Z, ∀ t, V (x, t) ⬝ᵥ V (x, t) = v x ⬝ᵥ v x + a x ^ 2) ∧
          (∀ x ∈ Z, ∀ t,
            (X x - v x + V (x, t)) ⬝ᵥ (X x - v x + V (x, t)) = X x ⬝ᵥ X x + a x ^ 2 ∧
            (X x - v x + V (x, t)) ⬝ᵥ Y x = X x ⬝ᵥ Y x) ∧
          (∃ W : Set Base, IsOpen W ∧ C₀ ⊆ W ∧ W ⊆ U ∧
            ∀ x ∈ W, a x = 0 → ∀ t, V (x, t) = v x) ∧
          ∃ τ : Base → ℝ,
            (∀ x ∈ K, ∀ θ ∈ Ico (0 : ℝ) 1,
              deriv (fun t => α (x, t)) θ = 0 ↔ θ = 0 ∨ θ = τ x) ∧
            ∀ x ∈ K, T < fderiv ℝ (fun y => α (y, 0)) x (0, 1) ∧
              T < fderiv ℝ (fun y => α (y, τ x)) x (0, 1) := by
  let R := fun x => velocityRadius (v x) (a x)
  let u := fun x => v x ⬝ᵥ e₁ x
  let w := fun x => v x ⬝ᵥ e₂ x
  have hR := velocityRadius_smoothOn hv ha hn
  have hRp : ∀ x ∈ Ω, 0 < R x := fun x hx => velocityRadius_pos (hn x hx)
  have hvperp (x : Base) (hx : x ∈ Ω) : Y x ⬝ᵥ v x = 0 ∧ C x ⬝ᵥ v x = 0 := by
    rw [hvproj x hx]
    exact realNormalPart_perp (Y x) (C x) (X x) (hD x hx)
  have hreconstruct (x : Base) (hx : x ∈ Ω) :
      planeLift (e₁ x) (e₂ x) (planeCoordinates (e₁ x) (e₂ x) (v x)) = v x := by
    obtain ⟨h1, h2, h12, hy1, hc1, hy2, hc2⟩ := hframe x hx
    exact plane_coordinates_reconstruct (hD x hx) h1 h2 h12 hy1 hy2 hc1 hc2
      (hvperp x hx).1 (hvperp x hx).2
  have hquad (x : Base) (hx : x ∈ Ω) : R x ^ 2 = u x ^ 2 + w x ^ 2 + a x ^ 2 := by
    obtain ⟨h1, h2, h12, hy1, hc1, hy2, hc2⟩ := hframe x hx
    have hlen := plane_coordinates_length (hD x hx) h1 h2 h12 hy1 hy2 hc1 hc2
      (hvperp x hx).1 (hvperp x hx).2
    change velocityRadius (v x) (a x) ^ 2 = _
    rw [velocityRadius_sq, ← hlen]
  have huc (x : Base) (hx : x ∈ U) : 0 < u x ∧ w x = 0 := by
    exact collar_coordinates (hcollar x hx).1 (hcollar x hx).2 (hframe x (hUΩ hx)).2.2.1
  obtain ⟨Z, hZ, hLZ, hZΩ, α, hα, hper, hmean, ⟨W, hW, hCW, hWU, hzero⟩, τ, ht, hlarge⟩ :=
    CollarVelocity.calibrated_controlled_angle hC₀ hK hL hCL hKL hKU hU hΩ hCU hUΩ hLΩ
      hP hPK hlocal hR (dot_smoothOn hv he₁) (dot_smoothOn hv he₂) ha hRp hquad
      (fun x hx => (huc x hx).1) (fun x hx => (huc x hx).2) hap T
  let V : Base × ℝ → Vec := fun z => R z.1 • direction (e₁ z.1) (e₂ z.1) (α z)
  have hVs : ContDiffOn ℝ ∞ V (Z ×ˢ univ) :=
    ((hR.mono hZΩ).comp contDiffOn_fst (fun z hz => hz.1)).smul
      ((hα.cos.smul ((he₁.mono hZΩ).comp contDiffOn_fst (fun z hz => hz.1))).add
        (hα.sin.smul ((he₂.mono hZΩ).comp contDiffOn_fst (fun z hz => hz.1))))
  have hVl (x : Base) (hx : x ∈ Z) (t : ℝ) :
      V (x, t) ⬝ᵥ V (x, t) = v x ⬝ᵥ v x + a x ^ 2 := by
    obtain ⟨h1, h2, h12, _, _, _, _⟩ := hframe x (hZΩ hx)
    exact (planeLift_scaled_length (p := ![Real.cos (α (x, t)), Real.sin (α (x, t))])
      h1 h2 h12 (Real.cos_sq_add_sin_sq (α (x, t))) (R x)).trans
      (velocityRadius_sq (v x) (a x))
  refine ⟨Z, hZ, hLZ, hZΩ, α, hα, hper, V, hVs, (fun _ => rfl), ?_, hVl, ?_,
    ⟨W, hW, hCW, hWU, ?_⟩, τ, ht, hlarge⟩
  · intro x hx
    have hcont := (LocalPeriodicCalculus.smooth_slice hZ hα hx).continuous
    have hp : Continuous (fun t => ![Real.cos (α (x, t)), Real.sin (α (x, t))]) := by
      apply continuous_pi
      intro i
      fin_cases i
      · exact Real.continuous_cos.comp hcont
      · exact Real.continuous_sin.comp hcont
    exact (planeLift_mean (e₁ x) (e₂ x) (R x) hp (hmean x hx)).trans
      (scaled_coordinates_reconstruct (hRp x (hZΩ hx)).ne' (hreconstruct x (hZΩ hx)))
  · intro x hx t
    have hf := hframe x (hZΩ hx)
    have hpY : Y x ⬝ᵥ V (x, t) = 0 := by
      dsimp [V]
      rw [dotProduct_smul]
      simp [direction, dotProduct_add, dotProduct_smul, hf.2.2.2.1, hf.2.2.2.2.2.1]
    have hpC : C x ⬝ᵥ V (x, t) = 0 := by
      dsimp [V]
      rw [dotProduct_smul]
      simp [direction, dotProduct_add, dotProduct_smul, hf.2.2.2.2.1, hf.2.2.2.2.2.2]
    have hq := real_leading_metric (hD x (hZΩ hx)) hpY hpC (by rw [← hvproj x (hZΩ hx)]; exact hVl x hx t)
    simpa only [leadingTangent, ← hvproj x (hZΩ hx)] using hq
  · intro x hx haz t
    change R x • direction (e₁ x) (e₂ x) (α (x, t)) = v x
    rw [hzero x hx haz t]
    simp only [direction, Real.cos_zero, Real.sin_zero, one_smul, zero_smul, add_zero]
    change velocityRadius (v x) (a x) • e₁ x = v x
    rw [haz, (hcollar x (hWU hx)).2]
    simpa only [velocityRadius, zero_pow (by decide : 2 ≠ 0), add_zero] using
      norm_smul_normalize (hcollar x (hWU hx)).1

end ClosedSurfaceR4.VelocityFrame

end

end OAI
