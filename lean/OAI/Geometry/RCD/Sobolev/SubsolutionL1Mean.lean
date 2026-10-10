import OAI.Geometry.RCD.Sobolev.SubsolutionInterpolation
import OAI.Geometry.RCD.Metric.DyadicInteriorBalls

namespace OAI

/-! # Local L¹ mean bounds for nonnegative weak subsolutions -/

open Set Metric Filter MeasureTheory
open scoped ENNReal

noncomputable section
namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]

/-- Interior interpolation removes every dependence on the initially known
upper bound. The final estimate only uses the normalized L¹ mass. -/
theorem NoncollapsedRCD.subsolution_l1_mean_value {K : ℝ} {n : ℕ}
    (hX : NoncollapsedRCD K n X) (hn : 2 ≤ n) (Λ : ℝ) (hΛ : 0 ≤ Λ) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (p : X) (R : ℝ), 0 < R → -1 ≤ K*R^2 →
      ∀ (u : SobolevSpace (hausdorff n X) hX.quadratic) (a B : ℝ),
      0 ≤ a → a*R^2 ≤ Λ → 0 ≤ B →
      IsWeakSubsolutionOn (hausdorff n X) hX.quadratic (ball p R) u a →
      (∀ᵐ y ∂(hausdorff n X).restrict (ball p R),
        0 ≤ SobolevSpace.toLp _ _ u y ∧ SobolevSpace.toLp _ _ u y ≤ B) →
      ∀ᵐ y ∂(hausdorff n X).restrict (ball p (R/2)),
        SobolevSpace.toLp _ _ u y ≤ C*((hausdorff n X).real (ball p R))⁻¹*
          ∫ z in ball p R, SobolevSpace.toLp (hausdorff n X) hX.quadratic u z ∂hausdorff n X := by
  classical
  let := hX.separable
  obtain ⟨M,hM,hmean⟩ := hX.subsolution_unit_mean_value hn Λ hΛ
  let D := (8*Real.exp 4)^n
  let b : ℝ := 2^n
  let A := M*D
  let θ := 1/(2*b^2)
  let F := A^2/θ
  have hM0 : 0 ≤ M := zero_le_one.trans hM
  have hD : 1 ≤ D := one_le_pow₀ (by nlinarith [Real.one_le_exp (by norm_num : (0:ℝ) ≤ 4)])
  have hb : 1 ≤ b := one_le_pow₀ (by norm_num)
  have hb0 : 0 < b := zero_lt_one.trans_le hb
  have hθ : 0 < θ := by positivity
  have hθ1 : θ < 1 := by
    apply (div_lt_one (by positivity : 0 < 2*b^2)).mpr
    nlinarith
  have hF : 0 ≤ F := by positivity
  refine ⟨1+2*F,by linarith,?_⟩
  intro p R hR hcurv u a B ha haR hB hu hbound
  let μ := hausdorff n X
  let U := SobolevSpace.toLp μ hX.quadratic u
  let H := (μ.real (ball p R))⁻¹*∫ z in ball p R, U z ∂μ
  have hpos : ∀ᵐ z ∂μ.restrict (ball p R), 0 ≤ U z := hbound.mono fun _ h => h.1
  have hH : 0 ≤ H := mul_nonneg (inv_nonneg.mpr ENNReal.toReal_nonneg) (integral_nonneg_of_ae hpos)
  let S : ℕ → Set X := fun i => ball p (R-R/(2*2^i))
  have hS (i : ℕ) : S i ⊆ ball p R := ball_subset_ball (expanding_radii hR i).2.2.2.1.le
  have hstep (i : ℕ) (C : ℝ) (hC : 0 ≤ C)
      (hCb : ∀ᵐ z ∂μ.restrict (S (i+1)), U z ≤ C) :
      ∀ᵐ z ∂μ.restrict (S i), U z ≤ θ*C+F*(b^2)^i*H := by
    let t := R/(4*2^i)
    have ht : 0 < t := (expanding_radii hR i).1
    have htR : t ≤ R := (expanding_radii hR i).2.1
    have hcurvt : -1 ≤ K*t^2 := by
      by_cases hK : 0 ≤ K
      · exact (by norm_num : (-1:ℝ) ≤ 0).trans (mul_nonneg hK (sq_nonneg t))
      · exact hcurv.trans (mul_le_mul_of_nonpos_left (pow_le_pow_left₀ ht.le htR 2) (le_of_not_ge hK))
    have hat : a*t^2 ≤ Λ := (mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ ht.le htR 2) ha).trans haR
    have hlocal (q : S i) :
        ∀ᵐ z ∂μ.restrict (ball q.val (t/2)), U z ≤ θ*C+F*(b^2)^i*H := by
      have hq : dist q.val p < R-R/(2*2^i) := q.property
      have hqR : dist q.val p ≤ R := hq.le.trans (expanding_radii hR i).2.2.2.1.le
      have hsmall : ball q.val t ⊆ S (i+1) := by
        apply ball_subset_ball'
        dsimp only [t]
        linarith only [hq,(expanding_radii hR i).2.2.2.2]
      have hsub : ball q.val t ⊆ ball p R := hsmall.trans (hS (i+1))
      let Di := D*b^i
      have hDi : 1 ≤ Di := one_le_mul_of_one_le_of_one_le hD (one_le_pow₀ hb)
      have hv : μ.real (ball p R) ≤ Di*μ.real (ball q.val t) :=
        hX.expanding_volume_factor hn p R hR hcurv i q.val hqR
      have hnorm := hX.local_mean_interpolation hR ht (zero_le_one.trans hDi) hC hsub hv u hpos
        (ae_restrict_of_ae_restrict_of_subset hsmall hCb)
      have hnorm' : harmonicTargetNorm hX q.val t u ≤ Di*Real.sqrt (C*H) := by
        have hsqrt : Real.sqrt Di ≤ Di := by
          have hh := Real.sq_sqrt (zero_le_one.trans hDi)
          nlinarith [Real.sqrt_nonneg Di]
        calc
          _ ≤ Real.sqrt (Di*(C*H)) := by
            convert hnorm using 1
            dsimp only [H,μ,U]
            congr 1
            ring
          _ = Real.sqrt Di*Real.sqrt (C*H) := Real.sqrt_mul (zero_le_one.trans hDi) _
          _ ≤ Di*Real.sqrt (C*H) := mul_le_mul_of_nonneg_right hsqrt (Real.sqrt_nonneg _)
      have hyoung := sqrt_interpolation hθ (show 0 ≤ A*b^i by positivity) hC hH
      have halg : (A*b^i)^2/θ*H = F*(b^2)^i*H := by
        dsimp only [F]
        rw [mul_pow,pow_right_comm b i 2]
        ring
      filter_upwards [hmean q.val t ht hcurvt u a ha hat (hu.mono μ hX.quadratic hsub)] with z hz
      calc
        U z ≤ M*harmonicTargetNorm hX q.val t u := hz
        _ ≤ M*(Di*Real.sqrt (C*H)) := mul_le_mul_of_nonneg_left hnorm' hM0
        _ = (A*b^i)*Real.sqrt (C*H) := by dsimp only [A,Di]; ring
        _ ≤ θ*C+F*(b^2)^i*H := by simpa only [halg] using hyoung
    let V : S i → Set X := fun q => ball q.val (t/2)
    obtain ⟨s,hs,hcover⟩ := (HereditarilyLindelofSpace.isLindelof (S i)).elim_countable_subcover
      V (fun _ => isOpen_ball) (by
        intro z hz
        exact mem_iUnion.mpr ⟨⟨z,hz⟩,mem_ball_self (by positivity)⟩)
    exact ae_restrict_of_ae_restrict_of_subset hcover
      ((ae_restrict_biUnion_iff V hs _).mpr (fun q _ => hlocal q))
  have hh := geometric_mean_bootstrap μ U (ball p R) S hS hθ.le hθ1 hF hH hB
    (by dsimp only [θ]; field_simp)
    (hbound.mono fun _ h => h.2) hstep
  have hs0 : S 0 = ball p (R/2) := by dsimp only [S]; congr 1; norm_num; ring
  rw [hs0] at hh
  filter_upwards [hh] with z hz
  change U z ≤ (1+2*F)*(μ.real (ball p R))⁻¹*∫ z in ball p R, U z ∂μ
  calc
    U z ≤ 2*F*H := hz
    _ ≤ (1+2*F)*H := by nlinarith
    _ = _ := by dsimp only [H]; ring

end RegularPointCoordinates

end

end OAI
