import OAI.MeasureTheory.Falconer.Angular.SignedStationaryExpansion

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
open scoped ContDiff

noncomputable def stationarySignedIndices (n : ℕ) : Finset (Bool × ℕ) :=
  Finset.univ ×ˢ Finset.range (n+1)

theorem fullCircleStationaryExpansion_sum {f : ℝ → ℂ} (hf : ContDiff ℝ ∞ f)
    {Λ : ℝ} (hΛ : 0 < Λ) (n : ℕ) :
    fullCircleStationaryExpansion Λ f n =
      ∑ p ∈ stationarySignedIndices n, signedStationaryTerm p.1 p.2 f Λ := by
  rw [fullCircleStationaryExpansion_signed hΛ hf]
  simp [stationarySignedIndices,Finset.sum_product,add_comm]

theorem signedStationaryRadial_integrable {Ψ : ℝ → ℝ}
    (hΨ : ContDiff ℝ ∞ Ψ) (hs : ∀ t, Ψ t ≠ 0 → t ∈ Ioo (1/4:ℝ) 4)
    (plus₁ plus₂ : Bool) (j k : ℕ) (f g : ℝ → ℂ) (θ φ A B ξ : ℝ) :
    Integrable (fun s : ℝ => Complex.exp (Complex.I*(ξ:ℂ)*(s:ℂ))*
      signedStationaryRadialCoefficient Ψ plus₁ plus₂ j k f g θ φ A B s) := by
  have hc : HasCompactSupport (radialStationaryProfile Ψ (-((j:ℝ)+(k:ℝ)+1))) :=
    isCompact_Icc.of_isClosed_subset isClosed_closure (radialStationaryProfile_tsupport hs _)
  have hcont : Continuous (signedStationaryRadialCoefficient Ψ plus₁ plus₂ j k f g θ φ A B) :=
    continuous_const.mul (radialStationaryProfile_contDiff hΨ hs _).continuous
  exact (((by fun_prop : Continuous (fun s : ℝ => Complex.exp (Complex.I*(ξ:ℂ)*(s:ℂ)))).mul hcont)).integrable_of_hasCompactSupport hc.mul_left.mul_left

theorem stationary_product_radial_integral {Ψ : ℝ → ℝ}
    (hΨ : ContDiff ℝ ∞ Ψ) (hs : ∀ t, Ψ t ≠ 0 → t ∈ Ioo (1/4:ℝ) 4)
    {f g : ℝ → ℂ} (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g)
    (n : ℕ) {R d₁ d₂ : ℝ} (hR : 0 < R) (h1 : 0 < d₁) (h2 : 0 < d₂) :
    R⁻¹ • (∫ r : ℝ, Ψ (r/R) •
      (fullCircleStationaryExpansion (r*d₁) f n * fullCircleStationaryExpansion (r*d₂) g n)) =
      ∑ p ∈ stationarySignedIndices n, ∑ q ∈ stationarySignedIndices n,
        radialPhaseIntegral (signedStationaryRadialCoefficient Ψ p.1 q.1 p.2 q.2 f g 0 0 (R*d₁) (R*d₂))
          (R*(stationarySign p.1*d₁+stationarySign q.1*d₂)) := by
  let H := fun (p q : Bool × ℕ) (s : ℝ) => Complex.exp
    (Complex.I*((R*(stationarySign p.1*d₁+stationarySign q.1*d₂):ℝ):ℂ)*(s:ℂ))*
      signedStationaryRadialCoefficient Ψ p.1 q.1 p.2 q.2 f g 0 0 (R*d₁) (R*d₂) s
  have he (s : ℝ) : Ψ s •
      (fullCircleStationaryExpansion (R*s*d₁) f n * fullCircleStationaryExpansion (R*s*d₂) g n) =
      ∑ p ∈ stationarySignedIndices n, ∑ q ∈ stationarySignedIndices n, H p q s := by
    by_cases hn : Ψ s = 0
    · simp [hn,H,signedStationaryRadialCoefficient,radialStationaryProfile]
    · have hsp : 0 < s := lt_trans (by norm_num : (0:ℝ) < 1/4) (hs s hn).1
      rw [fullCircleStationaryExpansion_sum hf (by positivity),
        fullCircleStationaryExpansion_sum hg (by positivity)]
      simp only [Complex.real_smul,Finset.mul_sum,Finset.sum_mul]
      conv_lhs => rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro p hp
      apply Finset.sum_congr rfl
      intro q hq
      simpa only [H,mul_assoc,mul_right_comm R s] using
        signedStationaryTerm_product Ψ p.1 q.1 p.2 q.2 f g hR h1 h2 hsp
  have hi (p q : Bool × ℕ) : Integrable (H p q) :=
    signedStationaryRadial_integrable hΨ hs p.1 q.1 p.2 q.2 f g 0 0 (R*d₁) (R*d₂) _
  calc
    _ = ∫ s : ℝ, Ψ s •
        (fullCircleStationaryExpansion (R*s*d₁) f n * fullCircleStationaryExpansion (R*s*d₂) g n) := by
      have hh := Measure.integral_comp_mul_left
        (fun r : ℝ => Ψ (r/R) •
          (fullCircleStationaryExpansion (r*d₁) f n * fullCircleStationaryExpansion (r*d₂) g n)) R
      simpa only [mul_div_cancel_left₀ _ hR.ne',abs_of_pos hR,abs_of_pos (inv_pos.mpr hR)] using hh.symm
    _ = ∫ s : ℝ, ∑ p ∈ stationarySignedIndices n, ∑ q ∈ stationarySignedIndices n, H p q s := by
      simp_rw [he]
    _ = _ := by
      rw [integral_finsetSum _ (fun p _ => integrable_finsetSum _ (fun q _ => hi p q))]
      apply Finset.sum_congr rfl
      intro p hp
      rw [integral_finsetSum _ (fun q _ => hi p q)]
      rfl

end PlanarFalconer

end OAI
