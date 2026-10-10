import OAI.MeasureTheory.Falconer.Estimates.QuadraticBudget
import OAI.MeasureTheory.Falconer.Angular.RadialStationaryProfile

namespace OAI

/-! # Radial decay for spherical stationary coefficients

Scalar compact-support integration by parts gives decay for the stationary
coefficient, with the dimensional gain of the full ambient sphere.
-/

namespace Falconer
open Set MeasureTheory
open scoped ContDiff

 theorem actualStationaryCoefficient_bound (m j : ℕ) :
    ∃ H : ℝ, 0 ≤ H ∧ ∀ (B : Space (m+3) → ℂ), ContDiff ℝ ∞ B →
      ∀ C D : ℝ, 0 ≤ C → 1 ≤ D →
      (∀ t ≤ 2*j, ∀ w : Sphere (m+3), ‖iteratedFDeriv ℝ t B w‖ ≤ C*D^t) →
      ∀ e : Sphere (m+3), ‖actualStationaryCoefficient m j B e‖ ≤ H*C*D^(2*j) := by
  obtain ⟨L,hL,hbound⟩ := pole_quadratic_amplitude_budget m (2*j)
  let q : ℂ := sphereStationaryConstant (m+2)/((2*Complex.I)^j*(j.factorial:ℂ))
  refine ⟨‖q‖*((m+2:ℕ):ℝ)^j*L,by positivity,?_⟩
  intro B hB C D hC hD hb e
  let a : Space (m+2) → ℂ := quadraticAmplitude m
    (fun w => poleLocalizedAmbient e B (sphereMap (stationaryPoleRotation e) w))
  have ha : ContDiff ℝ ∞ a := poleLocalized_quadratic_contDiff m e hB
  have hc : actualStationaryCoefficient m j B e = quadraticJetCoefficient j a := by
    dsimp [a]
    rw [← actualStationaryCoefficient_eq m j (poleLocalizedAmbient e B) e,
      poleLocalizedAmbient_coefficient]
  have hΔ := euclidean_iterated_laplacian_derivative_bound ha j 0 (0:Space (m+2))
  simp only [norm_iteratedFDeriv_zero] at hΔ
  have h0 := hbound e B hB C D hC hD hb (0+2*j) (by omega) 0
  have htotal := hΔ.trans (mul_le_mul_of_nonneg_left h0 (by positivity))
  rw [hc,quadraticJetCoefficient,norm_mul]
  exact (mul_le_mul_of_nonneg_left htotal (norm_nonneg q)).trans_eq (by ring)

noncomputable def normalizedStationaryCoefficient (m j : ℕ) (Λ : ℝ)
    (B : Space (m+3) → ℂ) (e : Sphere (m+3)) : ℂ :=
  ((Λ^j)⁻¹:ℝ)*actualStationaryCoefficient m j B e

 theorem normalizedStationaryCoefficient_bound (m j : ℕ) :
    ∃ H : ℝ, 0 ≤ H ∧ ∀ (B : Space (m+3) → ℂ), ContDiff ℝ ∞ B →
      ∀ C D Λ : ℝ, 0 ≤ C → 1 ≤ D → 0 < Λ → D^2 ≤ Λ →
      (∀ t ≤ 2*j, ∀ w : Sphere (m+3), ‖iteratedFDeriv ℝ t B w‖ ≤ C*D^t) →
      ∀ e : Sphere (m+3), ‖normalizedStationaryCoefficient m j Λ B e‖ ≤ H*C := by
  obtain ⟨H,hH,hb⟩ := actualStationaryCoefficient_bound m j
  refine ⟨H,hH,?_⟩
  intro B hB C D Λ hC hD hΛ hscale hder e
  rw [normalizedStationaryCoefficient,norm_mul,Complex.norm_real,Real.norm_eq_abs,
    abs_of_nonneg (inv_nonneg.mpr (pow_nonneg hΛ.le _))]
  have hpow : D^(2*j) ≤ Λ^j := by
    rw [pow_mul]
    exact pow_le_pow_left₀ (sq_nonneg _) hscale j
  calc
    _ ≤ (Λ^j)⁻¹*(H*C*D^(2*j)) :=
      mul_le_mul_of_nonneg_left (hb B hB C D hC hD hder e) (by positivity)
    _ ≤ (Λ^j)⁻¹*(H*C*Λ^j) := by gcongr
    _ = H*C := by field_simp

noncomputable def sphericalRadialCoefficient (m j k : ℕ) (Ψ : ℝ → ℝ)
    (B G : Space (m+3) → ℂ) (e f : Sphere (m+3)) (R d₁ d₂ s : ℝ) : ℂ :=
  (((R*d₁)^(-((m+2:ℕ):ℝ)/2)*(R*d₂)^(-((m+2:ℕ):ℝ)/2):ℝ):ℂ)*
    (normalizedStationaryCoefficient m j (R*d₁) B e*
      star (normalizedStationaryCoefficient m k (R*d₂) G f))*
    PlanarFalconer.radialStationaryProfile Ψ (-((m+2:ℕ):ℝ)-(j:ℝ)-(k:ℝ)) s

 theorem spherical_radial_kernel (m j k : ℕ) {Ψ : ℝ → ℝ}
    (hΨ : ContDiff ℝ ∞ Ψ) (hs : ∀ t, Ψ t ≠ 0 → t ∈ Ioo (1/4:ℝ) 4) :
    ∃ H : ℝ, 0 ≤ H ∧ ∀ (B G : Space (m+3) → ℂ),
      ContDiff ℝ ∞ B → ContDiff ℝ ∞ G →
      ∀ C E D R d₁ d₂ : ℝ, 0 ≤ C → 0 ≤ E → 1 ≤ D →
      0 < R → 0 < d₁ → 0 < d₂ → D^2 ≤ R*d₁ → D^2 ≤ R*d₂ →
      (∀ t ≤ 2*j, ∀ w : Sphere (m+3), ‖iteratedFDeriv ℝ t B w‖ ≤ C*D^t) →
      (∀ t ≤ 2*k, ∀ w : Sphere (m+3), ‖iteratedFDeriv ℝ t G w‖ ≤ E*D^t) →
      ∀ (e f : Sphere (m+3)) (s₁ s₂ : ℝ),
      (s₁ = 1 ∨ s₁ = -1) → (s₂ = 1 ∨ s₂ = -1) →
      ‖PlanarFalconer.radialPhaseIntegral (sphericalRadialCoefficient m j k Ψ B G e f R d₁ d₂)
        (R*(s₁*d₁+s₂*d₂))‖ ≤
      H*C*E*((R*d₁)^(-((m+2:ℕ):ℝ)/2)*(R*d₂)^(-((m+2:ℕ):ℝ)/2))/
        (1+R*|d₁-d₂|)^2 := by
  obtain ⟨Hj,hHj,hj⟩ := normalizedStationaryCoefficient_bound m j
  obtain ⟨Hk,hHk,hk⟩ := normalizedStationaryCoefficient_bound m k
  obtain ⟨P,hP,hprofile⟩ := PlanarFalconer.radialStationaryProfile_derivatives hΨ hs
    (-((m+2:ℕ):ℝ)-(j:ℝ)-(k:ℝ)) 2
  refine ⟨15*(Hj*Hk*P),by positivity,?_⟩
  intro B G hB hG C E D R d₁ d₂ hC hE hD hR hd₁ hd₂ hD₁ hD₂ hb hg e f s₁ s₂ hs₁ hs₂
  let S := (R*d₁)^(-((m+2:ℕ):ℝ)/2)*(R*d₂)^(-((m+2:ℕ):ℝ)/2)
  have hS : 0 ≤ S := by dsimp [S]; positivity
  let a := sphericalRadialCoefficient m j k Ψ B G e f R d₁ d₂
  have ha : ContDiff ℝ ∞ a := contDiff_const.mul
    (PlanarFalconer.radialStationaryProfile_contDiff hΨ hs _)
  have has : tsupport a ⊆ Icc (1/4:ℝ) 4 :=
    tsupport_mul_subset_right.trans (PlanarFalconer.radialStationaryProfile_tsupport hs _)
  have hcoeff : ‖normalizedStationaryCoefficient m j (R*d₁) B e*
      star (normalizedStationaryCoefficient m k (R*d₂) G f)‖ ≤ (Hj*C)*(Hk*E) := by
    rw [norm_mul,norm_star]
    exact mul_le_mul (hj B hB C D (R*d₁) hC hD (mul_pos hR hd₁) hD₁ hb e)
      (hk G hG E D (R*d₂) hE hD (mul_pos hR hd₂) hD₂ hg f)
      (norm_nonneg _) (mul_nonneg hHj hC)
  have hab (l : ℕ) (hl : l ≤ 2) (s : ℝ) :
      ‖iteratedDeriv l a s‖ ≤ (Hj*Hk*P*C*E)*S := by
    change ‖iteratedDeriv l (fun t => ((S:ℂ)*
      (normalizedStationaryCoefficient m j (R*d₁) B e*
        star (normalizedStationaryCoefficient m k (R*d₂) G f)))*
          PlanarFalconer.radialStationaryProfile Ψ _ t) s‖ ≤ _
    rw [iteratedDeriv_const_mul_field,norm_mul,norm_mul,Complex.norm_real,
      Real.norm_eq_abs,abs_of_nonneg hS]
    calc
      _ ≤ (S*((Hj*C)*(Hk*E)))*P :=
        mul_le_mul (mul_le_mul_of_nonneg_left hcoeff hS)
          (hprofile l hl s) (norm_nonneg _) (mul_nonneg hS (mul_nonneg (mul_nonneg hHj hC) (mul_nonneg hHk hE)))
      _ = _ := by ring
  have hzero (s : ℝ) : ‖a s‖ ≤ (Hj*Hk*P*C*E)*S := by
    simpa only [iteratedDeriv_zero] using hab 0 (by omega) s
  have h := PlanarFalconer.angular_radial_kernel_bound ha has (by positivity) hS hR.le hd₁.le hd₂.le
    hs₁ hs₂ hzero (hab 2 le_rfl)
  apply h.trans_eq
  dsimp [S]
  ring

end Falconer

end OAI
