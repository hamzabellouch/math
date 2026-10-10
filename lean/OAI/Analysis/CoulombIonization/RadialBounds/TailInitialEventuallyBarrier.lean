import Mathlib
import OAI.Analysis.CoulombIonization.RadialBounds.BarrierDataSelectionBarrier
import OAI.Analysis.CoulombIonization.Localization.OriginalPosteriorMomentBarrier
import OAI.Analysis.CoulombIonization.RadialBounds.TailInitialPointwiseBarrier

namespace OAI

noncomputable section

namespace CoulombBarrier

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
section Work_TailInitialEventually_barrier_scope

open MeasureTheory Filter Set Metric
open scoped Topology ContDiff

open CoulombAtom CoulombAnalysis CoulombObservation

def tailPolynomialThreshold (r : ℝ) {K : ℕ} (j : Fin (K+1)) : ℝ :=
  min 1 (((2:ℝ)^j.val*r)^40)

lemma tailPolynomialThreshold_pos {r : ℝ} (hr : 0 < r) {K : ℕ} (j : Fin (K+1)) :
    0 < tailPolynomialThreshold r j := by
  unfold tailPolynomialThreshold
  positivity

lemma tailPolynomialThreshold_le_one (r : ℝ) {K : ℕ} (j : Fin (K+1)) :
    tailPolynomialThreshold r j ≤ 1 := min_le_left _ _

lemma tailPolynomialThreshold_zero {r : ℝ} (hr : 0 ≤ r) (hr1 : r ≤ 1) (K : ℕ) :
    tailPolynomialThreshold r (0 : Fin (K+1)) = r^40 := by
  simp only [tailPolynomialThreshold,Fin.val_zero,pow_zero,one_mul]
  exact min_eq_right (pow_le_one₀ hr hr1)

def HasTailInitialBarrier (Z : ℕ) (s ε k B c δ : ℝ) (g : Space → ℝ) : Prop :=
  let r₀ := ε*(Z:ℝ)^(-1/3:ℝ)
  ∀ N : ℕ, PriceMinimizes (energy Z) (s^(-4:ℝ)) N →
    ∀ K : ℕ, ∃ F : fermionGraph N,
      TailTiltState Z (s^(-4:ℝ)) r₀ K (tailPolynomialThreshold r₀) δ F ∧
      ∃ a p : OriginalDatum N K (fun k => dyadicObservationWidth r₀ k) 0 → TFSpace → ℝ,
        IsNuclearBarrier
          ((physicalObservationLaw (graphRawLaw F) K).map
            (originalDatum (fun k => dyadicObservationWidth r₀ k) 0))
          (jointMasterPosterior (graphRawLaw F) (fun k => dyadicObservationWidth r₀ k) 0 c r₀ s g)
          (Z:ℝ) k B (max B (32*ε^3)) r₀ 2 (5184*r₀^32) a p

lemma hasTailInitialBarrier_of_numerics {Z : ℕ} {s ε k B c δ G : ℝ}
    (hn : InitialNumerics Z s ε G c δ) (hc : 0 < c) (hc1 : c ≤ 1/2)
    (hε : 0 < ε) (hε1 : ε ≤ 1) (hk : 0 ≤ k) (hB : 0 < B) (hδ : 0 < δ)
    (hed : initialDensityConstant*ε^(6/5:ℝ) < 1/20)
    (hq : 4*initialQuadraticConstant k*ε^(3/2:ℝ) ≤ 1/20)
    (hBs : B ≤ ε^3/10) (hsub : 4*Real.pi*k*Real.sqrt B ≤ 19/2)
    {g : Space → ℝ} (hg : ContDiff ℝ ∞ g) (hcg : HasCompactSupport g)
    (hG : ∀ z, (g z)^2 ≤ G) (hgn : ∫ z, (g z)^2 = 1)
    (hrad : IsRadial g) (hgs : tsupport g ⊆ ball 0 1) :
    HasTailInitialBarrier Z s ε k B c δ g := by
  intro N hN K
  let r₀ := ε*(Z:ℝ)^(-1/3:ℝ)
  obtain ⟨F,hF⟩ := exists_actual_tail_tilt_state (Nat.cast_nonneg Z) hn.radius_pos hN K
    (tailPolynomialThreshold r₀) (tailPolynomialThreshold_pos hn.radius_pos)
    (tailPolynomialThreshold_le_one r₀) hδ
  refine ⟨F,hF,?_⟩
  have hp := tailPolynomialThreshold_zero hn.radius_pos.le hn.radius_le K
  apply tail_initial_barrier hn.charge (Real.rpow_pos_of_pos hn.scale_pos _)
    hn.radius_pos hn.radius_le hn.scale_pos hn.scale_le hn.radius_scale hc hc1
    hε hε1 hk hB hn.radius_relation hed hq hBs hsub hN hF (0 : Fin (K+1))
    (tailPolynomialThreshold_pos hn.radius_pos 0) hp.le _ hn.interpolation
    hg hcg hG hgn hrad hgs
  simp only [Fin.val_zero,pow_zero,one_mul,dyadicUniformEventBudget]
  dsimp only [r₀]
  rw [hp]
  linarith only [hn.budget]

theorem same_state_initial_barrier_eventually {ι : Type*} {l : Filter ι}
    (Z : ι → ℕ) (s : ι → ℝ) (hZ : ∀ᶠ i in l, 1 ≤ Z i)
    (hs : ∀ᶠ i in l, 0 < s i) (hs0 : Tendsto s l (𝓝 0))
    (hscale : Tendsto (fun i => (Z i:ℝ)*(s i)^3) l atTop)
    {c₁ k δ : ℝ} (hc : 0 < c₁) (hc1 : c₁ ≤ 1/2) (hk : 0 ≤ k) (hδ : 0 < δ)
    {g : Space → ℝ} (hg : ContDiff ℝ ∞ g) (hcg : HasCompactSupport g)
    (hgn : ∫ z, (g z)^2 = 1) (hrad : IsRadial g) (hgs : tsupport g ⊆ ball 0 1) :
    ∃ ε B : ℝ, 0 < ε ∧ ε < 1 ∧ 0 < B ∧
      ∀ᶠ i in l, HasTailInitialBarrier (Z i) (s i) ε k B c₁ δ g := by
  obtain ⟨ε,hε,hε1,hed,hq⟩ := exists_barrier_epsilon k
  obtain ⟨B,hB,hBs,hsub⟩ := exists_barrier_B (k := k) hε
  refine ⟨ε,B,hε,hε1,hB,?_⟩
  obtain ⟨z,hz⟩ := (hg.continuous.pow 2).norm.exists_forall_ge_of_hasCompactSupport hcg.mul_left.norm
  let G : ℝ := ‖(g z)^2‖
  have hG (y : Space) : (g y)^2 ≤ G := by
    rw [←Real.norm_of_nonneg (sq_nonneg (g y))]
    exact hz y
  filter_upwards [initial_numerics_eventually Z s hZ hs hs0 hscale hε G c₁ δ] with i hi
  exact hasTailInitialBarrier_of_numerics hi hc hc1 hε hε1.le hk hB hδ hed hq hBs hsub
    hg hcg hG hgn hrad hgs

end Work_TailInitialEventually_barrier_scope

open MeasureTheory ProbabilityTheory Filter Set Metric
open scoped BigOperators Topology

open CoulombAtom CoulombObservation
attribute [local instance] physicalObservationLaw_probability
attribute [local irreducible] masterWidth masterKernel originalRawKernel physicalObservationLaw
  originalDatum jointMasterPosterior

lemma masterWidth_inverse_cube_radius {c₁ r₀ s r : ℝ} (hc : 0 < c₁) (hr : 0 < r)
    (hrs : r ≤ s) {y : Space} (hy : r ≤ ‖y‖) :
    (masterWidth c₁ r₀ s y)⁻¹^3 ≤ c₁⁻¹^3*r^(-3-3*masterExponent) := by
  have hl := masterWidth_radius_lower (r₀ := r₀) hc.le hr hrs hy
  have hp : 0 < c₁*r^(1+masterExponent) := mul_pos hc (Real.rpow_pos_of_pos hr _)
  have hinv := inv_anti₀ hp hl
  have he : (c₁*r^(1+masterExponent))⁻¹^3 = c₁⁻¹^3*r^(-3-3*masterExponent) := by
    rw [mul_inv_rev,mul_pow,←Real.rpow_neg hr.le,←Real.rpow_mul_natCast hr.le]
    have hex : -(1+masterExponent)*(3:ℝ) = -3-3*masterExponent := by ring
    norm_num only [Nat.cast_ofNat]
    rw [hex]
    ring
  exact (pow_le_pow_left₀ (inv_nonneg.mpr (hp.le.trans hl)) hinv 3).trans_eq he

theorem original_master_annular_second_moment {g : Space → ℝ} (hg : Continuous g)
    (hgs : tsupport g ⊆ ball 0 1) {c₁ : ℝ} (hc : 0 < c₁)
    (hcL : c₁ < (10*(100000:ℝ))⁻¹) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ {N K : ℕ} (μ : Measure (Configuration N)),
      ∀ [IsProbabilityMeasure μ] (ell : Fin K → ℝ) (j : ℕ) {r₀ s r Q : ℝ},
      0 < r₀ → 0 < s → s ≤ 1 → r₀ ≤ r → r ≤ s → 0 ≤ Q →
      (∫ x, (rawAnnularCount (r/2) (3*r) x)^2 ∂μ) ≤ Q*r^(-6:ℝ) →
      ∀ y : Space, r ≤ ‖y‖ → ‖y‖ ≤ 2*r →
      (∫ z, (jointMasterPosterior μ ell j c₁ r₀ s g (originalDatum ell j z) y)^2
        ∂physicalObservationLaw μ K) ≤ D*Q*r^(-12-6*masterExponent) := by
  obtain ⟨A,hAn,hA⟩ := masterKernel_amplitude hg hgs
  refine ⟨(A*c₁⁻¹^3)^2,sq_nonneg _,?_⟩
  intro N K μ hμ ell j r₀ s r Q hr₀ hs hs1 hrr hrs hQ hcount y hy hy2
  have hr : 0 < r := hr₀.trans_le hrr
  let B := A*c₁⁻¹^3*r^(-3-3*masterExponent)
  have hBn : 0 ≤ B := by dsimp only [B]; positivity
  have hb (x) : masterKernel c₁ r₀ s g x y ≤ B :=
    (hA hc hcL hr₀ hs hs1 x y).trans (by
      simpa only [B,mul_assoc] using mul_le_mul_of_nonneg_left
        (masterWidth_inverse_cube_radius (r₀ := r₀) hc hr hrs hy) hAn)
  have ht := masterWidth_radius_upper hc.le hr₀ hs hs1 hrr hy hy2
  have hsmall : 2*masterWidth c₁ r₀ s y < r/2 := by
    have hc2 : c₁ < 1/8 := by norm_num at hcL ⊢; linarith
    nlinarith
  have hsupport : Function.support (fun x => masterKernel c₁ r₀ s g x y) ⊆ ball y (r/2) := by
    rw [masterKernel_eq_widthKernel hc hr₀ hs g]
    exact (widthKernel_support_local (masterWidth_small_lipschitz hc hcL hr₀ hs hs1)
      (masterWidth_pos hc hr₀ hs) (by norm_num) (masterProfile_support hgs) y).trans
      (closedBall_subset_ball hsmall)
  have hm := original_master_second_moment_from_count μ ell j hc hr₀ hs hg y hBn hb hsupport
  have hraw : (∫ x, (rawBallCount y (r/2) x)^2 ∂μ) ≤
      ∫ x, (rawAnnularCount (r/2) (3*r) x)^2 ∂μ := by
    apply integral_mono
      (bounded_integrable_square (rawBallCount_measurable y (r/2)) (fun x => by
        rw [Real.norm_of_nonneg (rawBallCount_nonneg _ _ _)]; exact rawBallCount_le _ _ _))
      (bounded_integrable_square (rawAnnularCount_measurable (r/2) (3*r)) (fun x => by
        rw [Real.norm_of_nonneg (rawAnnularCount_nonneg _ _ _)]; exact rawAnnularCount_le _ _ _))
    intro x
    exact pow_le_pow_left₀ (rawBallCount_nonneg _ _ _)
      (rawBallCount_le_annular hr.le hy hy2 le_rfl x) 2
  apply (hm.trans (mul_le_mul_of_nonneg_left (hraw.trans hcount) (sq_nonneg B))).trans_eq
  dsimp only [B]
  rw [mul_pow,←Real.rpow_mul_natCast hr.le]
  calc
    (A*c₁⁻¹^3)^2*r^((-3-3*masterExponent)*2)*(Q*r^(-6:ℝ)) =
        (A*c₁⁻¹^3)^2*Q*(r^((-3-3*masterExponent)*2)*r^(-6:ℝ)) := by ring
    _ = _ := by rw [←Real.rpow_add hr]; congr 2; ring

end CoulombBarrier

end

end OAI
