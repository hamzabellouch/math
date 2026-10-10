import OAI.Geometry.RCD.Harmonic.CompactRadialWeight

namespace OAI

/-! # The exact radial integral obtained from compact smooth recoveries -/

open Set Filter MeasureTheory Metric InnerProductSpace
open scoped BoundedContinuousFunction Topology ContDiff NNReal
noncomputable section
namespace RegularPointCoordinates

theorem compact_radial_pairing_identity {n : ℕ} {S R : ℝ} (hS : 0<S) (hRS : R<S)
    {g G ψ : Euclidean n → ℝ} (Q : Euclidean n →ᵇ ℝ)
    (hg : ∀ W<S, ∃ L : ℝ≥0, LipschitzOnWith L g (closedBall 0 W))
    (hweak : EuclideanWeakHarmonicOn g S) (hG : ContDiff ℝ ∞ G)
    (hd : EqOn (fderiv ℝ G) (fderiv ℝ g) (ball 0 R))
    (hQ : EqOn Q (fun x => ‖x‖^2/2) (closedBall 0 R))
    (hψ : InteriorSmoothTest n S ψ) (hs : tsupport ψ⊆ball 0 R) :
    (∫ x in ball 0 S, Q x*inner ℝ (gradient ψ x) (gradient G x))=
      -(∫ x in ball 0 S, ψ x*fderiv ℝ g x x) := by
  have hψc : Continuous (gradient ψ) :=
    (toDual ℝ (Euclidean n)).symm.continuous.comp (hψ.1.continuous_fderiv (by simp))
  have hGc : Continuous (gradient G) :=
    (toDual ℝ (Euclidean n)).symm.continuous.comp (hG.continuous_fderiv (by simp))
  have hgzero (x : Euclidean n) (hx : x∉tsupport ψ) : gradient ψ x=0 := by
    simp only [gradient,fderiv_of_notMem_tsupport ℝ hx,map_zero]
  have hi1 : Integrable (fun x => (‖x‖^2/2)*inner ℝ (gradient ψ x) (gradient G x)) volume := by
    apply (((continuous_norm.pow 2).div_const 2).mul (hψc.inner hGc)).integrable_of_hasCompactSupport
    apply hψ.2.1.mono'
    intro x hx
    by_contra hn
    exact hx (by
      change (‖x‖^2/2)*inner ℝ (gradient ψ x) (gradient G x)=0
      simp only [hgzero x hn,inner_zero_left,mul_zero])
  have hi2 : Integrable (fun x => ψ x*fderiv ℝ G x x) volume := by
    apply (hψ.1.continuous.mul ((hG.continuous_fderiv (by simp)).clm_apply continuous_id)).integrable_of_hasCompactSupport
    exact hψ.2.1.mul_right
  have he1 (x : Euclidean n) :
      (‖x‖^2/2)*inner ℝ (gradient ψ x) (gradient G x)=
        (‖x‖^2/2)*inner ℝ (gradient ψ x) (gradient g x) := by
    by_cases hx : x∈tsupport ψ
    · simp only [gradient,hd (hs hx)]
    · simp only [hgzero x hx,inner_zero_left,mul_zero]
  have he2 (x : Euclidean n) : ψ x*fderiv ℝ G x x=ψ x*fderiv ℝ g x x := by
    by_cases hx : x∈tsupport ψ
    · rw [hd (hs hx)]
    · rw [image_eq_zero_of_notMem_tsupport hx,zero_mul,zero_mul]
  have hid := weak_harmonic_radial_pairing hS hg hweak hψ
    (hi1.congr (Eventually.of_forall he1)) (hi2.congr (Eventually.of_forall he2))
  have hleft (x : Euclidean n) : Q x*inner ℝ (gradient ψ x) (gradient G x)=
      (‖x‖^2/2)*inner ℝ (gradient ψ x) (gradient g x) := by
    by_cases hx : x∈tsupport ψ
    · rw [hQ (ball_subset_closedBall (hs hx)),he1 x]
    · simp only [hgzero x hx,inner_zero_left,mul_zero]
  have hzero (x : Euclidean n) (hx : x∉ball (0:Euclidean n) S) : x∉tsupport ψ :=
    fun hh => hx ((ball_subset_ball hRS.le) (hs hh))
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx => by
    rw [hgzero x (hzero x hx),inner_zero_left,mul_zero]),
    setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx => by
      rw [image_eq_zero_of_notMem_tsupport (hzero x hx),zero_mul]),
    integral_congr_ae (Eventually.of_forall hleft)]
  exact hid

end RegularPointCoordinates

end

end OAI
