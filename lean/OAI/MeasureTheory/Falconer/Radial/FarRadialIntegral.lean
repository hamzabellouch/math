import OAI.MeasureTheory.Falconer.Radial.StationaryRadialSum

namespace OAI

/-! # The radial integral of the full two-sphere stationary expansion

Every sign and coefficient is retained. Only finite sums and the scalar
change of radial variable are used to pass from the pointwise expansion
to the comparable-displacement kernel.
-/

namespace Falconer
open Set MeasureTheory
open scoped ContDiff

theorem signedRadialCoefficient_integrable {Ψ : ℝ → ℝ}
    (hΨ : ContDiff ℝ ∞ Ψ) (hs : ∀ t, Ψ t ≠ 0 → t ∈ Ioo (1/4:ℝ) 4)
    (m j k : ℕ) (B G : Space (m+3) → ℂ) (e f : Sphere (m+3))
    (R d₁ d₂ ξ : ℝ) (ε η : Bool) :
    Integrable (fun s : ℝ => stationaryPhase (ξ*s)*
      signedRadialCoefficient m j k Ψ B G e f R d₁ d₂ ε η s) := by
  have hc : HasCompactSupport
      (PlanarFalconer.radialStationaryProfile Ψ (-((m+2:ℕ):ℝ)-(j:ℝ)-(k:ℝ))) :=
    isCompact_Icc.of_isClosed_subset isClosed_closure
      (PlanarFalconer.radialStationaryProfile_tsupport hs _)
  have hcont : Continuous (signedRadialCoefficient m j k Ψ B G e f R d₁ d₂ ε η) :=
    continuous_const.mul (PlanarFalconer.radialStationaryProfile_contDiff hΨ hs _).continuous
  exact ((by unfold stationaryPhase; fun_prop :
    Continuous (fun s : ℝ => stationaryPhase (ξ*s))).mul hcont).integrable_of_hasCompactSupport
      hc.mul_left.mul_left

theorem full_stationary_radial_integral {Ψ : ℝ → ℝ}
    (hΨ : ContDiff ℝ ∞ Ψ) (hs : ∀ t, Ψ t ≠ 0 → t ∈ Ioo (1/4:ℝ) 4)
    (m J : ℕ) (B G : Space (m+3) → ℂ) (e f : Sphere (m+3))
    {R d₁ d₂ : ℝ} (hR : 0 < R) (hd₁ : 0 < d₁) (hd₂ : 0 < d₂) :
    R⁻¹ • (∫ r : ℝ, (Ψ (r/R):ℂ)*stationarySphereApprox m J (r*d₁) B e*
      stationarySphereApprox m J (r*d₂) G f) =
    ∑ ε : Bool, ∑ j ∈ Finset.range J, ∑ η : Bool, ∑ k ∈ Finset.range J,
      PlanarFalconer.radialPhaseIntegral (signedRadialCoefficient m j k Ψ B G e f R d₁ d₂ ε η)
        (R*(stationarySign ε*d₁+stationarySign η*d₂)) := by
  let H := fun (ε : Bool) (j : ℕ) (η : Bool) (k : ℕ) (s : ℝ) =>
    stationaryPhase ((R*(stationarySign ε*d₁+stationarySign η*d₂))*s)*
      signedRadialCoefficient m j k Ψ B G e f R d₁ d₂ ε η s
  have hi (ε : Bool) (j : ℕ) (η : Bool) (k : ℕ) : Integrable (H ε j η k) :=
    signedRadialCoefficient_integrable hΨ hs m j k B G e f R d₁ d₂ _ ε η
  calc
    _ = ∫ s : ℝ, (Ψ s:ℂ)*stationarySphereApprox m J (R*s*d₁) B e*
        stationarySphereApprox m J (R*s*d₂) G f := by
      have hh := Measure.integral_comp_mul_left
        (fun r : ℝ => (Ψ (r/R):ℂ)*stationarySphereApprox m J (r*d₁) B e*
          stationarySphereApprox m J (r*d₂) G f) R
      simpa only [mul_div_cancel_left₀ _ hR.ne',abs_of_pos hR,
        abs_of_pos (inv_pos.mpr hR)] using hh.symm
    _ = ∫ s : ℝ, ∑ ε : Bool, ∑ j ∈ Finset.range J,
        ∑ η : Bool, ∑ k ∈ Finset.range J, H ε j η k s := by
      apply integral_congr_ae
      filter_upwards with s
      exact stationarySphereApprox_radial_sum m J Ψ hs B G e f hR hd₁ hd₂ s
    _ = _ := by
      rw [integral_finsetSum _ (fun ε _ => integrable_finsetSum _ (fun j _ =>
        integrable_finsetSum _ (fun η _ => integrable_finsetSum _ (fun k _ => hi ε j η k))))]
      apply Finset.sum_congr rfl
      intro ε _
      rw [integral_finsetSum _ (fun j _ =>
        integrable_finsetSum _ (fun η _ => integrable_finsetSum _ (fun k _ => hi ε j η k)))]
      apply Finset.sum_congr rfl
      intro j _
      rw [integral_finsetSum _ (fun η _ => integrable_finsetSum _ (fun k _ => hi ε j η k))]
      apply Finset.sum_congr rfl
      intro η _
      rw [integral_finsetSum _ (fun k _ => hi ε j η k)]
      apply Finset.sum_congr rfl
      intro k _
      apply integral_congr_ae
      filter_upwards with s
      dsimp [H,stationaryPhase,PlanarFalconer.radialPhaseIntegral]
      congr 2
      push_cast
      ring

theorem full_stationary_radial_bound {Ψ : ℝ → ℝ}
    (hΨ : ContDiff ℝ ∞ Ψ) (hs : ∀ t, Ψ t ≠ 0 → t ∈ Ioo (1/4:ℝ) 4)
    (m J : ℕ) :
    ∃ H : ℝ, 0 ≤ H ∧ ∀ (B G : Space (m+3) → ℂ),
      ContDiff ℝ ∞ B → ContDiff ℝ ∞ G →
      ∀ C E D R d₁ d₂ : ℝ, 0 ≤ C → 0 ≤ E → 1 ≤ D →
      0 < R → 0 < d₁ → 0 < d₂ → D^2 ≤ R*d₁ → D^2 ≤ R*d₂ →
      (∀ t ≤ 2*J, ∀ w : Sphere (m+3), ‖iteratedFDeriv ℝ t B w‖ ≤ C*D^t) →
      (∀ t ≤ 2*J, ∀ w : Sphere (m+3), ‖iteratedFDeriv ℝ t G w‖ ≤ E*D^t) →
      ∀ e f : Sphere (m+3),
      ‖R⁻¹ • (∫ r : ℝ, (Ψ (r/R):ℂ)*stationarySphereApprox m J (r*d₁) B e*
        stationarySphereApprox m J (r*d₂) G f)‖ ≤
      H*C*E*((R*d₁)^(-((m+2:ℕ):ℝ)/2)*(R*d₂)^(-((m+2:ℕ):ℝ)/2))/
        (1+R*|d₁-d₂|)^2 := by
  choose H hH hb using fun j k => signed_radial_kernel m j k hΨ hs
  let Htotal := ∑ _ε : Bool, ∑ j ∈ Finset.range J, ∑ _η : Bool, ∑ k ∈ Finset.range J, H j k
  refine ⟨Htotal,Finset.sum_nonneg (fun _ _ => Finset.sum_nonneg (fun _ _ =>
    Finset.sum_nonneg (fun _ _ => Finset.sum_nonneg (fun _ _ => hH _ _)))),?_⟩
  intro B G hB hG C E D R d₁ d₂ hC hE hD hR hd₁ hd₂ hD₁ hD₂ hderB hderG e f
  rw [full_stationary_radial_integral hΨ hs m J B G e f hR hd₁ hd₂]
  calc
    _ ≤ ∑ _ε : Bool, ∑ j ∈ Finset.range J, ∑ _η : Bool, ∑ k ∈ Finset.range J,
        H j k*C*E*((R*d₁)^(-((m+2:ℕ):ℝ)/2)*(R*d₂)^(-((m+2:ℕ):ℝ)/2))/
          (1+R*|d₁-d₂|)^2 := by
      apply (norm_sum_le _ _).trans
      apply Finset.sum_le_sum
      intro ε _
      apply (norm_sum_le _ _).trans
      apply Finset.sum_le_sum
      intro j hj
      apply (norm_sum_le _ _).trans
      apply Finset.sum_le_sum
      intro η _
      apply (norm_sum_le _ _).trans
      apply Finset.sum_le_sum
      intro k hk
      exact hb j k B G hB hG C E D R d₁ d₂ hC hE hD hR hd₁ hd₂ hD₁ hD₂
        (fun t ht => hderB t (ht.trans (Nat.mul_le_mul_left 2 (Nat.le_of_lt (Finset.mem_range.mp hj)))))
        (fun t ht => hderG t (ht.trans (Nat.mul_le_mul_left 2 (Nat.le_of_lt (Finset.mem_range.mp hk))))) e f ε η
    _ = _ := by simp only [Htotal,Finset.sum_mul,Finset.sum_div]

end Falconer

end OAI
