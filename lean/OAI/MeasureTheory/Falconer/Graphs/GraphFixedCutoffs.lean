import OAI.MeasureTheory.Falconer.Fourier.GraphFourSymbolDerivatives
import OAI.MeasureTheory.Falconer.Angular.GraphRotatedWeights

namespace OAI

namespace PlanarFalconer
open Set Metric
open scoped ContDiff ComplexConjugate

theorem graph_plane_axis_all (η : Plane) :
    ‖η‖ • sourceDirection (graphPlaneAngle η) = η := by
  rw [graphPlaneAngle_eq_arg]
  have he := congrArg Complex.orthonormalBasisOneI.repr
    (Complex.norm_mul_cos_add_sin_mul_I (graphComplexCoordinate η))
  simpa only [← Complex.ofReal_cos, ← Complex.ofReal_sin, ← Complex.real_smul, LinearIsometryEquiv.map_smul,
    graphComplexCoordinate_norm, graphComplexCoordinate,
    LinearIsometryEquiv.apply_symm_apply, LinearIsometryEquiv.norm_map, sourceDirection] using he

theorem graphNormalizedAxis_eq_all {η : Plane} (hη : η ≠ 0) :
    graphNormalizedAxis η = sourceDirection (graphPlaneAngle η) := by
  calc
    graphNormalizedAxis η = ‖η‖⁻¹ • (‖η‖ • sourceDirection (graphPlaneAngle η)) :=
      congrArg (fun v : Plane => ‖η‖⁻¹ • v) (graph_plane_axis_all η).symm
    _ = _ := by rw [smul_smul, inv_mul_cancel₀ (norm_ne_zero_iff.mpr hη), one_smul]

theorem graphAlgebraicDirection_eq_all (plus : Bool) {η : Plane} (hη : η ≠ 0) (z : ℝ) :
    graphAlgebraicDirection plus (η,z) =
      sourceDirection (graphPlaneAngle η+(if plus then Real.arctan z else -Real.arctan z)) := by
  cases plus
  · simp only [graphAlgebraicDirection, Bool.false_eq_true, ↓reduceIte,
      graphNormalizedAxis_eq_all hη, neg_smul, ← sub_eq_add_neg]
    exact (sourceDirection_sub_arctan _ _).symm
  · simp only [graphAlgebraicDirection, ↓reduceIte, graphNormalizedAxis_eq_all hη]
    exact (sourceDirection_add_arctan _ _).symm

noncomputable def graphFixedSign (plus : Bool) (p : Plane × ℝ) : ℂ :=
  if plus then (graphSignPlus (graphAlgebraicDirection true p, graphAlgebraicDirection false p) : ℝ)
  else (graphSignMinus (graphAlgebraicDirection true p, -graphAlgebraicDirection false p) : ℝ)

theorem graphFixedSign_eq (plus : Bool) {p : Plane × ℝ} (hp : p.1 ≠ 0) :
    graphFixedSign plus p =
      ((if plus then circleGraphSignPlus else circleGraphSignMinus)
        (sourceUnitDirection (graphPlaneAngle p.1+Real.arctan p.2),
          sourceUnitDirection (graphPlaneAngle p.1-Real.arctan p.2+(if plus then 0 else Real.pi))) : ℝ) := by
  cases plus <;> simp only [graphFixedSign, Bool.false_eq_true, ↓reduceIte,
    circleGraphSignPlus, circleGraphSignMinus, sourceUnitDirection, add_zero,
    graphAlgebraicDirection_eq_all true hp, graphAlgebraicDirection_eq_all false hp,
    Bool.false_eq_true, ↓reduceIte, ← sub_eq_add_neg, sourceDirection_add_pi]

theorem graphFixedSign_contDiffAt (plus : Bool) {p : Plane × ℝ} (hp : p.1 ≠ 0) :
    ContDiffAt ℝ ∞ (graphFixedSign plus) p := by
  have ha := graphAlgebraicDirection_contDiffAt true p hp
  have hb := graphAlgebraicDirection_contDiffAt false p hp
  cases plus
  · exact Complex.ofRealCLM.contDiff.contDiffAt.comp p
      (graphSignMinus_contDiff.contDiffAt.comp p (ha.prodMk hb.neg))
  · exact Complex.ofRealCLM.contDiff.contDiffAt.comp p
      (graphSignPlus_contDiff.contDiffAt.comp p (ha.prodMk hb))

noncomputable def graphShellJacobian (Ψ : ℝ → ℝ) (p : Plane × ℝ) : ℂ :=
  ((‖p.1‖*Real.sqrt (1+p.2^2))⁻¹ * Ψ (‖p.1‖*Real.sqrt (1+p.2^2)/2) : ℝ)

theorem graphShellJacobian_contDiffAt {Ψ : ℝ → ℝ} (hΨ : ContDiff ℝ ∞ Ψ)
    {p : Plane × ℝ} (hp : p.1 ≠ 0) : ContDiffAt ℝ ∞ (graphShellJacobian Ψ) p := by
  have hr : ContDiffAt ℝ ∞ (fun q : Plane × ℝ => ‖q.1‖*Real.sqrt (1+q.2^2)) p :=
    (contDiffAt_fst.norm ℝ hp).mul
      ((contDiffAt_const.add (contDiffAt_snd.pow 2)).sqrt (by positivity))
  have hn : ‖p.1‖*Real.sqrt (1+p.2^2) ≠ 0 :=
    mul_ne_zero (norm_ne_zero_iff.mpr hp) (by positivity)
  exact Complex.ofRealCLM.contDiff.contDiffAt.comp p
    ((hr.inv hn).mul (hΨ.contDiffAt.comp p (hr.div_const 2)))

theorem graph_compact_derivative_bound {f : (Plane × ℝ) → ℂ}
    (hf : ∀ p, p.1 ≠ 0 → ContDiffAt ℝ ∞ f p) (n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (η : Plane) (z : ℝ),
      ‖η‖ ≤ 8 → |z| ≤ 4 → 1/8 ≤ ‖η‖ → ‖iteratedFDeriv ℝ n f (η,z)‖ ≤ C := by
  let K : Set (Plane × ℝ) := closedBall 0 8 ∩ {p | 1/8 ≤ ‖p.1‖}
  have hK : IsCompact K := (isCompact_closedBall (0:Plane × ℝ) 8).inter_right
    (isClosed_le continuous_const continuous_fst.norm)
  obtain ⟨C,hC⟩ := hK.exists_bound_of_continuousOn
    (f := iteratedFDeriv ℝ n f) (fun p hp =>
      ((hf p (norm_pos_iff.mp (lt_of_lt_of_le (by norm_num : (0:ℝ)<1/8) hp.2))).continuousAt_iteratedFDeriv
        (by exact_mod_cast (le_top : (n:ℕ∞) ≤ ⊤))).continuousWithinAt)
  refine ⟨max 0 C,le_max_left _ _,?_⟩
  intro η z hhi hz hlo
  apply (hC (η,z) ?_).trans (le_max_right _ _)
  refine ⟨?_,hlo⟩
  simp only [mem_closedBall,dist_zero_right,Prod.norm_def,max_le_iff,Real.norm_eq_abs]
  exact ⟨hhi,hz.trans (by norm_num)⟩

theorem graph_fixed_sign_derivatives (n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (plus : Bool) (η : Plane) (z : ℝ),
      ‖η‖ ≤ 8 → |z| ≤ 4 → 1/8 ≤ ‖η‖ →
      ‖iteratedFDeriv ℝ n (graphFixedSign plus) (η,z)‖ ≤ C := by
  choose C hC hb using fun plus => graph_compact_derivative_bound
    (fun _ hp => graphFixedSign_contDiffAt plus hp) n
  refine ⟨max (C true) (C false),(hC true).trans (le_max_left _ _),?_⟩
  intro plus η z hhi hz hlo
  apply (hb plus η z hhi hz hlo).trans
  cases plus <;> simp

theorem graph_shell_jacobian_derivatives {Ψ : ℝ → ℝ} (hΨ : ContDiff ℝ ∞ Ψ) (n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (η : Plane) (z : ℝ),
      ‖η‖ ≤ 8 → |z| ≤ 4 → 1/8 ≤ ‖η‖ →
      ‖iteratedFDeriv ℝ n (graphShellJacobian Ψ) (η,z)‖ ≤ C :=
  graph_compact_derivative_bound (fun _ hp => graphShellJacobian_contDiffAt hΨ hp) n

end PlanarFalconer

end OAI
