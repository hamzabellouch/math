import OAI.MeasureTheory.Falconer.Fourier.SignedStationary

namespace OAI

/-! # Radial decay with both actual stationary signs

The two Boolean indices are the outgoing and incoming terms of the full
sphere expansion. The original amplitude remains the argument in all
four cases; antipodal conjugation is internal to its signed coefficient.
-/

namespace Falconer
open Set MeasureTheory
open scoped ContDiff

def stationarySign (outgoing : Bool) : ℝ := if outgoing then 1 else -1

theorem stationarySign_cases (outgoing : Bool) :
    stationarySign outgoing = 1 ∨ stationarySign outgoing = -1 := by
  cases outgoing <;> simp [stationarySign]

noncomputable def signedRadialCoefficient (m j k : ℕ) (Ψ : ℝ → ℝ)
    (B G : Space (m+3) → ℂ) (e f : Sphere (m+3))
    (R d₁ d₂ : ℝ) (ε η : Bool) (s : ℝ) : ℂ :=
  (((R*d₁)^(-((m+2:ℕ):ℝ)/2)*(R*d₂)^(-((m+2:ℕ):ℝ)/2):ℝ):ℂ)*
    (signedStationaryCoefficient m j (R*d₁) B e ε*
      signedStationaryCoefficient m k (R*d₂) G f η)*
    PlanarFalconer.radialStationaryProfile Ψ (-((m+2:ℕ):ℝ)-(j:ℝ)-(k:ℝ)) s

theorem signed_radial_kernel (m j k : ℕ) {Ψ : ℝ → ℝ}
    (hΨ : ContDiff ℝ ∞ Ψ) (hs : ∀ t, Ψ t ≠ 0 → t ∈ Ioo (1/4:ℝ) 4) :
    ∃ H : ℝ, 0 ≤ H ∧ ∀ (B G : Space (m+3) → ℂ),
      ContDiff ℝ ∞ B → ContDiff ℝ ∞ G →
      ∀ C E D R d₁ d₂ : ℝ, 0 ≤ C → 0 ≤ E → 1 ≤ D →
      0 < R → 0 < d₁ → 0 < d₂ → D^2 ≤ R*d₁ → D^2 ≤ R*d₂ →
      (∀ t ≤ 2*j, ∀ w : Sphere (m+3), ‖iteratedFDeriv ℝ t B w‖ ≤ C*D^t) →
      (∀ t ≤ 2*k, ∀ w : Sphere (m+3), ‖iteratedFDeriv ℝ t G w‖ ≤ E*D^t) →
      ∀ (e f : Sphere (m+3)) (ε η : Bool),
      ‖PlanarFalconer.radialPhaseIntegral (signedRadialCoefficient m j k Ψ B G e f R d₁ d₂ ε η)
        (R*(stationarySign ε*d₁+stationarySign η*d₂))‖ ≤
      H*C*E*((R*d₁)^(-((m+2:ℕ):ℝ)/2)*(R*d₂)^(-((m+2:ℕ):ℝ)/2))/
        (1+R*|d₁-d₂|)^2 := by
  obtain ⟨Hj,hHj,hj⟩ := signedStationaryCoefficient_bound m j
  obtain ⟨Hk,hHk,hk⟩ := signedStationaryCoefficient_bound m k
  obtain ⟨P,hP,hprofile⟩ := PlanarFalconer.radialStationaryProfile_derivatives hΨ hs
    (-((m+2:ℕ):ℝ)-(j:ℝ)-(k:ℝ)) 2
  refine ⟨15*(Hj*Hk*P),by positivity,?_⟩
  intro B G hB hG C E D R d₁ d₂ hC hE hD hR hd₁ hd₂ hD₁ hD₂ hb hg e f ε η
  let S := (R*d₁)^(-((m+2:ℕ):ℝ)/2)*(R*d₂)^(-((m+2:ℕ):ℝ)/2)
  have hS : 0 ≤ S := by dsimp [S]; positivity
  let a := signedRadialCoefficient m j k Ψ B G e f R d₁ d₂ ε η
  have ha : ContDiff ℝ ∞ a := contDiff_const.mul
    (PlanarFalconer.radialStationaryProfile_contDiff hΨ hs _)
  have has : tsupport a ⊆ Icc (1/4:ℝ) 4 :=
    tsupport_mul_subset_right.trans (PlanarFalconer.radialStationaryProfile_tsupport hs _)
  have hcoeff : ‖signedStationaryCoefficient m j (R*d₁) B e ε*
      signedStationaryCoefficient m k (R*d₂) G f η‖ ≤ (Hj*C)*(Hk*E) := by
    rw [norm_mul]
    exact mul_le_mul (hj B hB C D (R*d₁) hC hD (mul_pos hR hd₁) hD₁ hb e ε)
      (hk G hG E D (R*d₂) hE hD (mul_pos hR hd₂) hD₂ hg f η)
      (norm_nonneg _) (mul_nonneg hHj hC)
  have hab (l : ℕ) (hl : l ≤ 2) (s : ℝ) :
      ‖iteratedDeriv l a s‖ ≤ (Hj*Hk*P*C*E)*S := by
    change ‖iteratedDeriv l (fun t => ((S:ℂ)*
      (signedStationaryCoefficient m j (R*d₁) B e ε*
        signedStationaryCoefficient m k (R*d₂) G f η))*
          PlanarFalconer.radialStationaryProfile Ψ _ t) s‖ ≤ _
    rw [iteratedDeriv_const_mul_field,norm_mul,norm_mul,Complex.norm_real,
      Real.norm_eq_abs,abs_of_nonneg hS]
    calc
      _ ≤ (S*((Hj*C)*(Hk*E)))*P :=
        mul_le_mul (mul_le_mul_of_nonneg_left hcoeff hS)
          (hprofile l hl s) (norm_nonneg _)
          (mul_nonneg hS (mul_nonneg (mul_nonneg hHj hC) (mul_nonneg hHk hE)))
      _ = _ := by ring
  have hzero (s : ℝ) : ‖a s‖ ≤ (Hj*Hk*P*C*E)*S := by
    simpa only [iteratedDeriv_zero] using hab 0 (by omega) s
  have h := PlanarFalconer.angular_radial_kernel_bound ha has (by positivity) hS
    hR.le hd₁.le hd₂.le (stationarySign_cases ε) (stationarySign_cases η) hzero (hab 2 le_rfl)
  apply h.trans_eq
  dsimp [S]
  ring

end Falconer

end OAI
