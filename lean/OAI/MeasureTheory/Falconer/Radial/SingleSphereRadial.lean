import OAI.MeasureTheory.Falconer.Radial.SingleStationaryRadial
import OAI.MeasureTheory.Falconer.Radial.StationaryRadialSum

namespace OAI

/-! # Radial decay of one stationary sphere with an exact scalar phase -/

namespace Falconer
open Set MeasureTheory
open scoped ContDiff

theorem singleStationaryPole_radial (m j : ℕ) (Ψ : ℝ → ℝ)
    (B : Space (m+3) → ℂ) (e : Sphere (m+3))
    {R d s : ℝ} (hR : 0 < R) (hd : 0 < d) (hs : 0 < s) (t : ℝ) (ε : Bool) :
    (Ψ s:ℂ)*stationaryPoleTerm m j (R*s*d) B e ε*stationaryPhase (R*s*t) =
      stationaryPhase ((R*(stationarySign ε*d+t))*s)*
        singleSignedRadialCoefficient m j Ψ B e (R*d) ε s := by
  let p : ℝ := ((m+2:ℕ):ℝ)/2
  have hpow : (R*s*d)^(-p) = (R*d)^(-p)*s^(-p) := by
    rw [show R*s*d = (R*d)*s by ring,Real.mul_rpow (mul_pos hR hd).le hs.le]
  have hpowers : s^(-p)*(s^j)⁻¹ = s^(-p-(j:ℝ)) := by
    rw [← Real.rpow_natCast s j,← Real.rpow_neg hs.le,← Real.rpow_add hs]
    congr 1
  have hphase : stationaryPhase (stationarySign ε*(R*s*d))*stationaryPhase (R*s*t) =
      stationaryPhase ((R*(stationarySign ε*d+t))*s) := by
    rw [stationaryPhase_mul]
    congr 1
    ring
  simp only [stationaryPoleTerm,neg_div]
  change (Ψ s:ℂ)*((((R*s*d)^(-p):ℝ):ℂ)*
    stationaryPhase (stationarySign ε*(R*s*d))*signedStationaryCoefficient m j (R*s*d) B e ε)*
    stationaryPhase (R*s*t) = _
  rw [hpow,signedStationaryCoefficient_scale]
  have halgebra : (Ψ s:ℂ)*((((R*d)^(-p)*s^(-p):ℝ):ℂ)*
      stationaryPhase (stationarySign ε*(R*s*d))*
      (((s^j)⁻¹:ℝ)*signedStationaryCoefficient m j (R*d) B e ε))*stationaryPhase (R*s*t) =
      (stationaryPhase (stationarySign ε*(R*s*d))*stationaryPhase (R*s*t))*
        ((R*d)^(-p):ℝ)*signedStationaryCoefficient m j (R*d) B e ε*
        ((Ψ s*(s^(-p)*(s^j)⁻¹):ℝ):ℂ) := by
    push_cast
    ring
  rw [halgebra,hphase,hpowers]
  dsimp only [singleSignedRadialCoefficient,PlanarFalconer.radialStationaryProfile,p]
  push_cast
  ring_nf

theorem singleSignedRadial_integrable {Ψ : ℝ → ℝ}
    (hΨ : ContDiff ℝ ∞ Ψ) (hs : ∀ s, Ψ s ≠ 0 → s ∈ Ioo (1/4:ℝ) 4)
    (m j : ℕ) (B : Space (m+3) → ℂ) (e : Sphere (m+3)) (Λ ξ : ℝ) (ε : Bool) :
    Integrable (fun s : ℝ => stationaryPhase (ξ*s)*
      singleSignedRadialCoefficient m j Ψ B e Λ ε s) := by
  have hc : HasCompactSupport
      (PlanarFalconer.radialStationaryProfile Ψ (-((m+2:ℕ):ℝ)/2-(j:ℝ))) :=
    isCompact_Icc.of_isClosed_subset isClosed_closure
      (PlanarFalconer.radialStationaryProfile_tsupport hs _)
  have hcont : Continuous (singleSignedRadialCoefficient m j Ψ B e Λ ε) :=
    continuous_const.mul (PlanarFalconer.radialStationaryProfile_contDiff hΨ hs _).continuous
  exact ((by unfold stationaryPhase; fun_prop :
    Continuous (fun s : ℝ => stationaryPhase (ξ*s))).mul hcont).integrable_of_hasCompactSupport
      hc.mul_left.mul_left

theorem single_sphere_radial_integral {Ψ : ℝ → ℝ}
    (hΨ : ContDiff ℝ ∞ Ψ) (hsupp : ∀ s, Ψ s ≠ 0 → s ∈ Ioo (1/4:ℝ) 4)
    (m J : ℕ) (B : Space (m+3) → ℂ) (e : Sphere (m+3))
    {R d : ℝ} (hR : 0 < R) (hd : 0 < d) (t : ℝ) :
    R⁻¹ • (∫ r : ℝ, (Ψ (r/R):ℂ)*stationarySphereApprox m J (r*d) B e*
      stationaryPhase (r*t)) =
    ∑ ε : Bool, ∑ j ∈ Finset.range J,
      PlanarFalconer.radialPhaseIntegral (singleSignedRadialCoefficient m j Ψ B e (R*d) ε)
        (R*(stationarySign ε*d+t)) := by
  let H := fun (ε : Bool) (j : ℕ) (s : ℝ) =>
    stationaryPhase ((R*(stationarySign ε*d+t))*s)*
      singleSignedRadialCoefficient m j Ψ B e (R*d) ε s
  have hi (ε : Bool) (j : ℕ) : Integrable (H ε j) :=
    singleSignedRadial_integrable hΨ hsupp m j B e (R*d) _ ε
  have he (s : ℝ) : (Ψ s:ℂ)*stationarySphereApprox m J (R*s*d) B e*
      stationaryPhase (R*s*t) = ∑ ε : Bool, ∑ j ∈ Finset.range J, H ε j s := by
    by_cases hs : 0 < s
    · rw [stationarySphereApprox_pole_sum m J (mul_pos (mul_pos hR hs) hd)]
      conv_lhs => lhs; rw [Finset.mul_sum]
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro ε _
      rw [Finset.mul_sum,Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro j _
      exact singleStationaryPole_radial m j Ψ B e hR hd hs t ε
    · have hz : Ψ s = 0 := by
        by_contra hn
        have hsp := (hsupp s hn).1
        linarith
      simp only [hz,Complex.ofReal_zero,zero_mul,H,singleSignedRadialCoefficient,
        PlanarFalconer.radialStationaryProfile,mul_zero,Finset.sum_const_zero]
  calc
    _ = ∫ s : ℝ, (Ψ s:ℂ)*stationarySphereApprox m J (R*s*d) B e*stationaryPhase (R*s*t) := by
      have h := Measure.integral_comp_mul_left
        (fun r : ℝ => (Ψ (r/R):ℂ)*stationarySphereApprox m J (r*d) B e*stationaryPhase (r*t)) R
      simpa only [mul_div_cancel_left₀ _ hR.ne',abs_of_pos hR,
        abs_of_pos (inv_pos.mpr hR)] using h.symm
    _ = ∫ s : ℝ, ∑ ε : Bool, ∑ j ∈ Finset.range J, H ε j s := by simp_rw [he]
    _ = _ := by
      rw [integral_finsetSum _ (fun ε _ => integrable_finsetSum _ (fun j _ => hi ε j))]
      apply Finset.sum_congr rfl
      intro ε _
      rw [integral_finsetSum _ (fun j _ => hi ε j)]
      apply Finset.sum_congr rfl
      intro j _
      apply integral_congr_ae
      filter_upwards with s
      dsimp [H,stationaryPhase,PlanarFalconer.radialPhaseIntegral]
      congr 2
      push_cast
      ring

theorem single_sphere_radial_bound {Ψ : ℝ → ℝ}
    (hΨ : ContDiff ℝ ∞ Ψ) (hs : ∀ s, Ψ s ≠ 0 → s ∈ Ioo (1/4:ℝ) 4)
    (m J q : ℕ) :
    ∃ H : ℝ, 0 ≤ H ∧ ∀ (B : Space (m+3) → ℂ), ContDiff ℝ ∞ B →
      ∀ C D R large small t : ℝ, 0 ≤ C → 1 ≤ D → 0 < R → 0 < large →
      2*small ≤ large → |t| ≤ small → D^2 ≤ R*large →
      (∀ k ≤ 2*J, ∀ w : Sphere (m+3), ‖iteratedFDeriv ℝ k B w‖ ≤ C*D^k) →
      ∀ e : Sphere (m+3),
      ‖R⁻¹ • (∫ r : ℝ, (Ψ (r/R):ℂ)*stationarySphereApprox m J (r*large) B e*
        stationaryPhase (r*t))‖ ≤
        H*C*(R*large)^(-((m+2:ℕ):ℝ)/2)/(R*large/2)^q := by
  choose H hH hbound using fun j => singleSignedRadial_noncomparable m j q hΨ hs
  let Htotal := ∑ _ε : Bool, ∑ j ∈ Finset.range J, H j
  refine ⟨Htotal,Finset.sum_nonneg (fun _ _ => Finset.sum_nonneg (fun j _ => hH j)),?_⟩
  intro B hB C D R large small t hC hD hR hl hsep ht hscale hb e
  rw [single_sphere_radial_integral hΨ hs m J B e hR hl t]
  calc
    _ ≤ ∑ _ε : Bool, ∑ j ∈ Finset.range J,
        H j*C*(R*large)^(-((m+2:ℕ):ℝ)/2)/(R*large/2)^q := by
      apply (norm_sum_le _ _).trans
      apply Finset.sum_le_sum
      intro ε _
      apply (norm_sum_le _ _).trans
      apply Finset.sum_le_sum
      intro j hj
      exact hbound j B hB C D R large small t hC hD hR hl hsep ht hscale
        (fun k hk => hb k (hk.trans (Nat.mul_le_mul_left 2 (Nat.le_of_lt (Finset.mem_range.mp hj))))) e ε
    _ = _ := by simp only [Htotal,Finset.sum_mul,Finset.sum_div]

end Falconer

end OAI
