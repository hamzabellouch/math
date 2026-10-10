import OAI.MeasureTheory.Falconer.Radial.SignedRadialKernel

namespace OAI

/-! # One stationary sphere against an unexpanded small displacement

Only the large sphere is expanded. The second displacement remains an
arbitrary scalar projection, bounded by the smaller displacement length.
-/

namespace Falconer
open Set MeasureTheory
open scoped ContDiff

noncomputable def singleSignedRadialCoefficient (m j : ℕ) (Ψ : ℝ → ℝ)
    (B : Space (m+3) → ℂ) (e : Sphere (m+3)) (Λ : ℝ) (ε : Bool) (s : ℝ) : ℂ :=
  ((Λ^(-((m+2:ℕ):ℝ)/2):ℝ):ℂ)*signedStationaryCoefficient m j Λ B e ε *
    PlanarFalconer.radialStationaryProfile Ψ (-((m+2:ℕ):ℝ)/2-(j:ℝ)) s

theorem singleSignedRadial_derivatives (m j n : ℕ) {Ψ : ℝ → ℝ}
    (hΨ : ContDiff ℝ ∞ Ψ) (hs : ∀ s, Ψ s ≠ 0 → s ∈ Ioo (1/4:ℝ) 4) :
    ∃ H : ℝ, 0 ≤ H ∧ ∀ (B : Space (m+3) → ℂ), ContDiff ℝ ∞ B →
      ∀ C D Λ : ℝ, 0 ≤ C → 1 ≤ D → 0 < Λ → D^2 ≤ Λ →
      (∀ t ≤ 2*j, ∀ w : Sphere (m+3), ‖iteratedFDeriv ℝ t B w‖ ≤ C*D^t) →
      ∀ (e : Sphere (m+3)) (ε : Bool),
      ContDiff ℝ ∞ (singleSignedRadialCoefficient m j Ψ B e Λ ε) ∧
      tsupport (singleSignedRadialCoefficient m j Ψ B e Λ ε) ⊆ Icc (1/4:ℝ) 4 ∧
      ∀ t ≤ n, ∀ s, ‖iteratedDeriv t (singleSignedRadialCoefficient m j Ψ B e Λ ε) s‖ ≤
        H*C*Λ^(-((m+2:ℕ):ℝ)/2) := by
  obtain ⟨H,hH,hcoeff⟩ := signedStationaryCoefficient_bound m j
  obtain ⟨P,hP,hprofile⟩ := PlanarFalconer.radialStationaryProfile_derivatives hΨ hs
    (-((m+2:ℕ):ℝ)/2-(j:ℝ)) n
  refine ⟨H*P,mul_nonneg hH hP,?_⟩
  intro B hB C D Λ hC hD hΛ hDΛ hb e ε
  refine ⟨contDiff_const.mul (PlanarFalconer.radialStationaryProfile_contDiff hΨ hs _),
    tsupport_mul_subset_right.trans (PlanarFalconer.radialStationaryProfile_tsupport hs _),?_⟩
  intro t ht s
  change ‖iteratedDeriv t (fun s =>
    (((Λ^(-((m+2:ℕ):ℝ)/2):ℝ):ℂ)*signedStationaryCoefficient m j Λ B e ε)*
      PlanarFalconer.radialStationaryProfile Ψ _ s) s‖ ≤ _
  rw [iteratedDeriv_const_mul_field,norm_mul,norm_mul,Complex.norm_real,Real.norm_eq_abs,
    abs_of_pos (Real.rpow_pos_of_pos hΛ _)]
  calc
    _ ≤ (Λ^(-((m+2:ℕ):ℝ)/2)*(H*C))*P := mul_le_mul
      (mul_le_mul_of_nonneg_left (hcoeff B hB C D Λ hC hD hΛ hDΛ hb e ε)
        (Real.rpow_nonneg hΛ.le _)) (hprofile t ht s) (norm_nonneg _)
      (mul_nonneg (Real.rpow_nonneg hΛ.le _) (mul_nonneg hH hC))
    _ = _ := by ring

theorem singleSignedRadial_noncomparable (m j n : ℕ) {Ψ : ℝ → ℝ}
    (hΨ : ContDiff ℝ ∞ Ψ) (hs : ∀ s, Ψ s ≠ 0 → s ∈ Ioo (1/4:ℝ) 4) :
    ∃ H : ℝ, 0 ≤ H ∧ ∀ (B : Space (m+3) → ℂ), ContDiff ℝ ∞ B →
      ∀ C D R large small t : ℝ, 0 ≤ C → 1 ≤ D → 0 < R → 0 < large →
      2*small ≤ large → |t| ≤ small → D^2 ≤ R*large →
      (∀ k ≤ 2*j, ∀ w : Sphere (m+3), ‖iteratedFDeriv ℝ k B w‖ ≤ C*D^k) →
      ∀ (e : Sphere (m+3)) (ε : Bool),
      ‖PlanarFalconer.radialPhaseIntegral
        (singleSignedRadialCoefficient m j Ψ B e (R*large) ε)
        (R*(stationarySign ε*large+t))‖ ≤
        H*C*(R*large)^(-((m+2:ℕ):ℝ)/2)/(R*large/2)^n := by
  obtain ⟨H,hH,hder⟩ := singleSignedRadial_derivatives m j n hΨ hs
  refine ⟨H*(15/4),by positivity,?_⟩
  intro B hB C D R large small t hC hD hR hl hsep ht hDΛ hb e ε
  obtain ⟨ha,hsa,hba⟩ := hder B hB C D (R*large) hC hD (mul_pos hR hl) hDΛ hb e ε
  have hfreq : R*large/2 ≤ |R*(stationarySign ε*large+t)| := by
    rw [abs_mul,abs_of_pos hR]
    have hx := mul_le_mul_of_nonneg_left
      (PlanarFalconer.noncomparable_radial_frequency hsep ht (stationarySign_cases ε)) hR.le
    linarith
  have hpos : 0 < R*large/2 := by positivity
  have hne : R*(stationarySign ε*large+t) ≠ 0 := abs_pos.mp (hpos.trans_le hfreq)
  have h := PlanarFalconer.radialPhaseIntegral_nonzero ha hsa (by norm_num) hne n (hba n le_rfl)
  apply h.trans
  have he : H*C*(R*large)^(-((m+2:ℕ):ℝ)/2)*((4:ℝ)-1/4) =
      (H*(15/4))*C*(R*large)^(-((m+2:ℕ):ℝ)/2) := by ring
  rw [he]
  exact div_le_div_of_nonneg_left (by positivity) (pow_pos hpos n)
    (pow_le_pow_left₀ hpos.le hfreq n)

end Falconer

end OAI
