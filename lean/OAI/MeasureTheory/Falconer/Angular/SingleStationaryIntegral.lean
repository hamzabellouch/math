import OAI.MeasureTheory.Falconer.Angular.SingleStationaryRadial
import OAI.MeasureTheory.Falconer.Angular.StationaryProductIntegral

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
open scoped ContDiff

theorem singleStationaryRadialCoefficient_eq (Ψ : ℝ → ℝ) (plus : Bool)
    (j : ℕ) (f : ℝ → ℂ) (θ : ℝ) {A s : ℝ} (hA : 0 < A) (hs : 0 < s) :
    singleStationaryRadialCoefficient Ψ plus j f θ A s =
      (Ψ s : ℂ) * (((A*s)^(-1/2:ℝ):ℝ):ℂ) * signedStationaryJet plus j f θ (A*s) := by
  have hj : (s⁻¹)^j = s^(-(j:ℝ)) := by
    rw [Real.rpow_neg hs.le,Real.rpow_natCast,inv_pow]
  have hp : s^(-((j:ℝ)+1/2)) = s^(-1/2:ℝ)*(s⁻¹)^j := by
    rw [hj,← Real.rpow_add hs]
    congr 1
    ring
  simp only [singleStationaryRadialCoefficient,radialStationaryProfile,
    signedStationaryJet_scale,Real.mul_rpow hA.le hs.le,Complex.ofReal_mul,hp]
  push_cast
  ring

theorem singleStationaryRadial_integrable {Ψ : ℝ → ℝ}
    (hΨ : ContDiff ℝ ∞ Ψ) (hs : ∀ t, Ψ t ≠ 0 → t ∈ Ioo (1/4:ℝ) 4)
    (plus : Bool) (j : ℕ) (f : ℝ → ℂ) (θ A ξ : ℝ) :
    Integrable (fun s : ℝ => Complex.exp (Complex.I*(ξ:ℂ)*(s:ℂ))*
      singleStationaryRadialCoefficient Ψ plus j f θ A s) := by
  have hc : HasCompactSupport (radialStationaryProfile Ψ (-((j:ℝ)+1/2))) :=
    isCompact_Icc.of_isClosed_subset isClosed_closure (radialStationaryProfile_tsupport hs _)
  have hcont : Continuous (singleStationaryRadialCoefficient Ψ plus j f θ A) :=
    continuous_const.mul (radialStationaryProfile_contDiff hΨ hs _).continuous
  exact ((by fun_prop : Continuous (fun s : ℝ => Complex.exp (Complex.I*(ξ:ℂ)*(s:ℂ)))).mul
    hcont).integrable_of_hasCompactSupport hc.mul_left.mul_left

theorem stationary_single_radial_integral {Ψ : ℝ → ℝ}
    (hΨ : ContDiff ℝ ∞ Ψ) (hs : ∀ t, Ψ t ≠ 0 → t ∈ Ioo (1/4:ℝ) 4)
    {f : ℝ → ℂ} (hf : ContDiff ℝ ∞ f) (n : ℕ) {R large : ℝ}
    (hR : 0 < R) (hl : 0 < large) (t : ℝ) :
    R⁻¹ • (∫ r : ℝ, Ψ (r/R) • (fullCircleStationaryExpansion (r*large) f n *
      Complex.exp (Complex.I*(r:ℂ)*(t:ℂ)))) =
    ∑ p ∈ stationarySignedIndices n,
      radialPhaseIntegral (singleStationaryRadialCoefficient Ψ p.1 p.2 f 0 (R*large))
        (R*(stationarySign p.1*large+t)) := by
  let H := fun (p : Bool × ℕ) (s : ℝ) =>
    Complex.exp (Complex.I*((R*(stationarySign p.1*large+t):ℝ):ℂ)*(s:ℂ))*
      singleStationaryRadialCoefficient Ψ p.1 p.2 f 0 (R*large) s
  have he (s : ℝ) : Ψ s • (fullCircleStationaryExpansion (R*s*large) f n *
      Complex.exp (Complex.I*((R*s:ℝ):ℂ)*(t:ℂ))) =
      ∑ p ∈ stationarySignedIndices n, H p s := by
    by_cases hn : Ψ s = 0
    · simp [hn,H,singleStationaryRadialCoefficient,radialStationaryProfile]
    · have hsp : 0 < s := lt_trans (by norm_num : (0:ℝ) < 1/4) (hs s hn).1
      rw [fullCircleStationaryExpansion_sum hf (by positivity)]
      simp only [Complex.real_smul,Finset.sum_mul,Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro p hp
      dsimp [H]
      rw [singleStationaryRadialCoefficient_eq Ψ p.1 p.2 f 0 (mul_pos hR hl) hsp]
      have hex : Complex.exp (Complex.I*((stationarySign p.1*(R*s*large):ℝ):ℂ)) *
          Complex.exp (Complex.I*((R*s:ℝ):ℂ)*(t:ℂ)) =
          Complex.exp (Complex.I*((R*(stationarySign p.1*large+t):ℝ):ℂ)*(s:ℂ)) := by
        rw [← Complex.exp_add]
        congr 1
        push_cast
        ring
      unfold signedStationaryTerm
      rw [← hex]
      simp only [mul_assoc]
      ring_nf
  calc
    _ = ∫ s : ℝ, Ψ s • (fullCircleStationaryExpansion (R*s*large) f n *
        Complex.exp (Complex.I*((R*s:ℝ):ℂ)*(t:ℂ))) := by
      have hh := Measure.integral_comp_mul_left (fun r : ℝ => Ψ (r/R) •
        (fullCircleStationaryExpansion (r*large) f n * Complex.exp (Complex.I*(r:ℂ)*(t:ℂ)))) R
      simpa only [mul_div_cancel_left₀ _ hR.ne',abs_of_pos hR,abs_of_pos (inv_pos.mpr hR)] using hh.symm
    _ = ∫ s : ℝ, ∑ p ∈ stationarySignedIndices n, H p s := by simp_rw [he]
    _ = _ := by
      rw [integral_finsetSum _ (fun p _ => singleStationaryRadial_integrable hΨ hs p.1 p.2 f 0 (R*large) _)]
      rfl

theorem stationary_single_radial_bound {Ψ : ℝ → ℝ}
    (hΨ : ContDiff ℝ ∞ Ψ) (hs : ∀ t, Ψ t ≠ 0 → t ∈ Ioo (1/4:ℝ) 4) (n q : ℕ) :
    ∃ H : ℝ, 0 ≤ H ∧ ∀ {f : ℝ → ℂ}, ContDiff ℝ ∞ f →
    ∀ {C D R large small t : ℝ}, 0 ≤ C → 1 ≤ D → 0 < R → 0 < large →
    2*small ≤ large → |t| ≤ small → D^2 ≤ R*large →
    (∀ l ≤ 2*n, ∀ u, ‖iteratedDeriv l f u‖ ≤ C*D^l) →
    ‖R⁻¹ • (∫ r : ℝ, Ψ (r/R) • (fullCircleStationaryExpansion (r*large) f n *
      Complex.exp (Complex.I*(r:ℂ)*(t:ℂ))))‖ ≤
      H*C*(R*large)^(-1/2:ℝ)/(R*large/2)^q := by
  choose H hH hb using fun j => singleStationaryRadial_noncomparable hΨ hs j q
  refine ⟨∑ p ∈ stationarySignedIndices n, H p.2,
    Finset.sum_nonneg (fun p _ => hH p.2),?_⟩
  intro f hf C D R large small t hC hD hR hl hsep ht hDA hbf
  rw [stationary_single_radial_integral hΨ hs hf n hR hl t]
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑ p ∈ stationarySignedIndices n, H p.2*C*(R*large)^(-1/2:ℝ)/(R*large/2)^q := by
      apply Finset.sum_le_sum
      intro p hp
      have hj : p.2 ≤ n := Nat.le_of_lt_succ (Finset.mem_range.mp (Finset.mem_product.mp hp).2)
      exact hb p.2 hf hC hD hR hl hsep ht
        (by cases p.1 <;> simp [stationarySign]) hDA p.1 0
        (fun l hl => hbf l (hl.trans (Nat.mul_le_mul_left 2 hj)))
    _ = _ := by simp only [Finset.sum_mul,Finset.sum_div]

end PlanarFalconer

end OAI
