import OAI.Geometry.SurfaceImmersion.Geometry.FiniteExceptionalTransverse

namespace OAI

/-! Extend a local transverse defining function smoothly before applying the
compact correction construction. -/
noncomputable section
open Set Metric Filter
open scoped ContDiff Topology

namespace ClosedSurfaceR4.TransverseSmallFunction

lemma localize_defining_function {K U : Set Base} {p : Base} {f : Base → ℝ}
    (hU : IsOpen U) (hp : p ∈ U) (hf : ContDiffOn ℝ ∞ f U)
    (hz : ∀ x ∈ K ∩ U, f x = 0) (hd : fderiv ℝ f p (0, 1) ≠ 0) :
    ∃ W : Set Base, IsOpen W ∧ p ∈ W ∧
      ∃ F : Base → ℝ, ContDiff ℝ ∞ F ∧ (∀ x ∈ K ∩ W, F x = 0) ∧
        ∀ x ∈ W, fderiv ℝ F x (0, 1) ≠ 0 := by
  obtain ⟨r, hr, hrU⟩ := Metric.isOpen_iff.mp hU p hp
  let φ : ContDiffBump p := ⟨r / 4, r / 2, by positivity, by linarith⟩
  have hs : tsupport φ ⊆ U := by
    rw [φ.tsupport_eq]
    exact fun x hx => hrU (lt_of_le_of_lt hx (by change r / 2 < r; linarith))
  let F : Base → ℝ := fun x => φ x * f x
  have hF : ContDiff ℝ ∞ F := by
    rw [contDiff_iff_contDiffAt]
    intro x
    by_cases hx : x ∈ tsupport φ
    · exact φ.contDiff.contDiffAt.mul (hf.contDiffAt (hU.mem_nhds (hs hx)))
    · apply contDiffAt_const.congr_of_eventuallyEq
      filter_upwards [notMem_tsupport_iff_eventuallyEq.mp hx] with y hy
      change φ y * f y = 0
      rw [show φ y = 0 from hy, zero_mul]
  have he : F =ᶠ[𝓝 p] f := by
    filter_upwards [φ.eventuallyEq_one_of_mem_ball (mem_ball_self φ.rIn_pos)] with x hx
    change φ x * f x = f x
    rw [show φ x = 1 from hx, one_mul]
  have hFp : fderiv ℝ F p (0, 1) ≠ 0 := by rw [he.fderiv_eq]; exact hd
  let N : Set Base := {x | fderiv ℝ F x (0, 1) ≠ 0}
  have hdF : ContDiff ℝ ∞ (fun x => fderiv ℝ F x (0, 1)) :=
    (hF.fderiv_right (by simp)).clm_apply contDiff_const
  have hN : IsOpen N := isOpen_ne.preimage hdF.continuous
  refine ⟨ball p φ.rIn ∩ N, isOpen_ball.inter hN, ⟨mem_ball_self φ.rIn_pos, hFp⟩,
    F, hF, ?_, fun x hx => hx.2⟩
  intro x hx
  have hxU : x ∈ U := hrU (lt_trans hx.2.1 (by change r / 4 < r; linarith))
  change φ x * f x = 0
  rw [hz x ⟨hx.1, hxU⟩, mul_zero]

/-- The small-value derivative construction with local smooth curve equations.
This is the local analytic content of manuscript Lemma `small-value-derivative`. -/
theorem small_value_prescribed_derivative {K O P : Set Base}
    (hK : IsCompact K) (hO : IsOpen O) (hKO : K ⊆ O)
    (hP : P.Finite) (hPK : P ⊆ K)
    (hlocal : ∀ p ∈ K \ P, ∃ U : Set Base, IsOpen U ∧ p ∈ U ∧
      ∃ f : Base → ℝ, ContDiffOn ℝ ∞ f U ∧ (∀ x ∈ K ∩ U, f x = 0) ∧
        fderiv ℝ f p (0, 1) ≠ 0)
    (B : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∃ H : Base → ℝ, ContDiff ℝ ∞ H ∧ HasCompactSupport H ∧ tsupport H ⊆ O ∧
      (∀ x, |H x| < ε) ∧ ∀ x ∈ K, fderiv ℝ H x (0, 1) = B := by
  apply finite_exceptional_transverse_correction hK hO hKO hP hPK _ B hε
  intro p hp
  obtain ⟨U, hU, hpU, f, hf, hz, hd⟩ := hlocal p hp
  exact localize_defining_function hU hpU hf hz hd

end ClosedSurfaceR4.TransverseSmallFunction

end

end OAI
