import OAI.MeasureTheory.Falconer.Angular.SingleStationaryIntegral
import OAI.MeasureTheory.Falconer.Angular.AngularStationarySpatial

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
open scoped ContDiff

theorem single_radial_angular_fubini (a : ℝ → ℂ) (ha : Continuous a)
    (hs : tsupport a ⊆ Icc (1/4:ℝ) 4) (g : UnitCircle → ℂ)
    (hg : Measurable g) {E : ℝ} (hE : 0 ≤ E) (hb : ∀ u, ‖g u‖ ≤ E)
    (t : UnitCircle → ℝ) (ht : Measurable t) (R c : ℝ) :
    (∫ s : ℝ, ∫ u, (Complex.exp (Complex.I*((R*(c+t u):ℝ):ℂ)*(s:ℂ))*a s)*g u
      ∂sourceArcLength) =
    ∫ u, radialPhaseIntegral a (R*(c+t u))*g u ∂sourceArcLength := by
  have hc : HasCompactSupport a := isCompact_Icc.of_isClosed_subset isClosed_closure hs
  obtain ⟨C,hC⟩ := hc.exists_bound_of_continuous ha
  have hC0 : 0 ≤ C := (norm_nonneg (a 0)).trans (hC 0)
  have hi : Integrable (fun p : ℝ × UnitCircle =>
      (Complex.exp (Complex.I*((R*(c+t p.2):ℝ):ℂ)*(p.1:ℂ))*a p.1)*g p.2)
      (volume.prod sourceArcLength) := by
    apply compact_finite_spatial_integrable volume sourceArcLength measurableSet_Icc
      isCompact_Icc.measure_lt_top (by fun_prop) (mul_nonneg hC0 hE)
    · intro p
      have hn : ‖Complex.exp (Complex.I*((R*(c+t p.2):ℝ):ℂ)*(p.1:ℂ))‖ = 1 := by
        rw [Complex.norm_exp]
        simp
      simp only [norm_mul,hn,one_mul]
      exact mul_le_mul (hC p.1) (hb p.2) (norm_nonneg _) hC0
    · intro p hp
      apply hs
      apply subset_closure
      change a p.1 ≠ 0
      intro hz
      exact hp (by simp [hz])
  rw [integral_integral_swap hi]
  apply integral_congr_ae
  filter_upwards with u
  rw [integral_mul_const]
  rfl

theorem stationary_single_angular_integral {Ψ : ℝ → ℝ}
    (hΨ : ContDiff ℝ ∞ Ψ) (hs : ∀ t, Ψ t ≠ 0 → t ∈ Ioo (1/4:ℝ) 4)
    {f : ℝ → ℂ} (hf : ContDiff ℝ ∞ f) (n : ℕ) {R large : ℝ}
    (hR : 0 < R) (hl : 0 < large) (g : UnitCircle → ℂ)
    (hg : Measurable g) {E : ℝ} (hE : 0 ≤ E) (hb : ∀ u, ‖g u‖ ≤ E)
    (t : UnitCircle → ℝ) (ht : Measurable t) :
    R⁻¹ • (∫ r : ℝ, Ψ (r/R) • (fullCircleStationaryExpansion (r*large) f n *
      (∫ u, Complex.exp (Complex.I*(r:ℂ)*(t u:ℂ))*g u ∂sourceArcLength))) =
    ∫ u, (∑ p ∈ stationarySignedIndices n,
      radialPhaseIntegral (singleStationaryRadialCoefficient Ψ p.1 p.2 f 0 (R*large))
        (R*(stationarySign p.1*large+t u)))*g u ∂sourceArcLength := by
  let a := fun p : Bool × ℕ => singleStationaryRadialCoefficient Ψ p.1 p.2 f 0 (R*large)
  let H := fun (p : Bool × ℕ) (s : ℝ) (u : UnitCircle) =>
    (Complex.exp (Complex.I*((R*(stationarySign p.1*large+t u):ℝ):ℂ)*(s:ℂ))*a p s)*g u
  have ha (p : Bool × ℕ) : Continuous (a p) :=
    continuous_const.mul (radialStationaryProfile_contDiff hΨ hs _).continuous
  have hsa (p : Bool × ℕ) : tsupport (a p) ⊆ Icc (1/4:ℝ) 4 :=
    tsupport_mul_subset_right.trans (radialStationaryProfile_tsupport hs _)
  have hi (p : Bool × ℕ) : Integrable (fun z : ℝ × UnitCircle => H p z.1 z.2)
      (volume.prod sourceArcLength) := by
    have hc : HasCompactSupport (a p) := isCompact_Icc.of_isClosed_subset isClosed_closure (hsa p)
    obtain ⟨C,hC⟩ := hc.exists_bound_of_continuous (ha p)
    apply compact_finite_spatial_integrable volume sourceArcLength measurableSet_Icc
      isCompact_Icc.measure_lt_top (by dsimp [H]; fun_prop)
      (mul_nonneg ((norm_nonneg (a p 0)).trans (hC 0)) hE)
    · intro z
      have hn : ‖Complex.exp (Complex.I*((R*(stationarySign p.1*large+t z.2):ℝ):ℂ)*(z.1:ℂ))‖ = 1 := by
        rw [Complex.norm_exp]; simp
      dsimp [H]
      simp only [norm_mul,hn,one_mul]
      exact mul_le_mul (hC z.1) (hb z.2) (norm_nonneg _) ((norm_nonneg (a p 0)).trans (hC 0))
    · intro z hz
      apply hsa p
      apply subset_closure
      change a p z.1 ≠ 0
      intro he
      exact hz (by simp [H,he])
  have he (s : ℝ) (u : UnitCircle) :
      Ψ s • (fullCircleStationaryExpansion (R*s*large) f n *
        (Complex.exp (Complex.I*((R*s:ℝ):ℂ)*(t u:ℂ))*g u)) =
      ∑ p ∈ stationarySignedIndices n, H p s u := by
    by_cases hn : Ψ s = 0
    · simp [hn,H,a,singleStationaryRadialCoefficient,radialStationaryProfile]
    · have hsp : 0 < s := lt_trans (by norm_num : (0:ℝ) < 1/4) (hs s hn).1
      rw [fullCircleStationaryExpansion_sum hf (by positivity)]
      simp only [Complex.real_smul,Finset.sum_mul,Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro p hp
      dsimp [H,a]
      rw [singleStationaryRadialCoefficient_eq Ψ p.1 p.2 f 0 (mul_pos hR hl) hsp]
      have hex : Complex.exp (Complex.I*((stationarySign p.1*(R*s*large):ℝ):ℂ)) *
          Complex.exp (Complex.I*((R*s:ℝ):ℂ)*(t u:ℂ)) =
          Complex.exp (Complex.I*((R*(stationarySign p.1*large+t u):ℝ):ℂ)*(s:ℂ)) := by
        rw [← Complex.exp_add]; congr 1; push_cast; ring
      unfold signedStationaryTerm
      rw [← hex]
      simp only [mul_assoc]
      ring_nf
  calc
    _ = ∫ s : ℝ, Ψ s • (fullCircleStationaryExpansion (R*s*large) f n *
        (∫ u, Complex.exp (Complex.I*((R*s:ℝ):ℂ)*(t u:ℂ))*g u ∂sourceArcLength)) := by
      have hh := Measure.integral_comp_mul_left (fun r : ℝ => Ψ (r/R) •
        (fullCircleStationaryExpansion (r*large) f n *
          (∫ u, Complex.exp (Complex.I*(r:ℂ)*(t u:ℂ))*g u ∂sourceArcLength))) R
      simpa only [mul_div_cancel_left₀ _ hR.ne',abs_of_pos hR,abs_of_pos (inv_pos.mpr hR)] using hh.symm
    _ = ∫ s : ℝ, ∫ u, ∑ p ∈ stationarySignedIndices n, H p s u ∂sourceArcLength := by
      simp_rw [← he,integral_smul,integral_const_mul]
    _ = ∫ u, (∫ s : ℝ, ∑ p ∈ stationarySignedIndices n, H p s u) ∂sourceArcLength :=
      integral_integral_swap (integrable_finsetSum _ (fun p _ => hi p))
    _ = _ := by
      apply integral_congr_ae
      filter_upwards with u
      rw [integral_finsetSum _ (fun p _ =>
        (singleStationaryRadial_integrable hΨ hs p.1 p.2 f 0 (R*large) _).mul_const (g u))]
      simp only [H,integral_mul_const,Finset.sum_mul]
      rfl

theorem stationary_single_angular_bound {Ψ : ℝ → ℝ}
    (hΨ : ContDiff ℝ ∞ Ψ) (hs : ∀ t, Ψ t ≠ 0 → t ∈ Ioo (1/4:ℝ) 4) (n q : ℕ) :
    ∃ H : ℝ, 0 ≤ H ∧ ∀ {f : ℝ → ℂ}, ContDiff ℝ ∞ f →
    ∀ {C D R large small : ℝ}, 0 ≤ C → 1 ≤ D → 0 < R → 0 < large →
    2*small ≤ large → D^2 ≤ R*large →
    (∀ l ≤ 2*n, ∀ u, ‖iteratedDeriv l f u‖ ≤ C*D^l) →
    ∀ (g : UnitCircle → ℂ), Measurable g → ∀ {E : ℝ}, 0 ≤ E → (∀ u, ‖g u‖ ≤ E) →
    ∀ (t : UnitCircle → ℝ), Measurable t → (∀ u, |t u| ≤ small) →
    ‖R⁻¹ • (∫ r : ℝ, Ψ (r/R) • (fullCircleStationaryExpansion (r*large) f n *
      (∫ u, Complex.exp (Complex.I*(r:ℂ)*(t u:ℂ))*g u ∂sourceArcLength)))‖ ≤
      H*C*E*(R*large)^(-1/2:ℝ)/(R*large/2)^q := by
  obtain ⟨H,hH,hb⟩ := stationary_single_radial_bound hΨ hs n q
  refine ⟨H*sourceArcLength.real univ,by positivity,?_⟩
  intro f hf C D R large small hC hD hR hl hsep hDA hbf g hg E hE hbg t ht hbt
  rw [stationary_single_angular_integral hΨ hs hf n hR hl g hg hE hbg t ht]
  have hbound (u : UnitCircle) :
      ‖(∑ p ∈ stationarySignedIndices n,
        radialPhaseIntegral (singleStationaryRadialCoefficient Ψ p.1 p.2 f 0 (R*large))
          (R*(stationarySign p.1*large+t u)))*g u‖ ≤
        (H*C*(R*large)^(-1/2:ℝ)/(R*large/2)^q)*E := by
    rw [norm_mul,← stationary_single_radial_integral hΨ hs hf n hR hl (t u)]
    exact mul_le_mul (hb hf hC hD hR hl hsep (hbt u) hDA hbf) (hbg u) (norm_nonneg _) (by positivity)
  have hh := norm_integral_le_of_norm_le_const (μ := sourceArcLength) (Filter.Eventually.of_forall hbound)
  apply hh.trans_eq
  ring

end PlanarFalconer

end OAI
