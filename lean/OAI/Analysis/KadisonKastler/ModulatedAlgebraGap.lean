import OAI.Analysis.KadisonKastler.ProbabilityMatrixDistance
import OAI.Analysis.KadisonKastler.AmenableEmbedding
import OAI.Analysis.KadisonKastler.PoissonBoundaryLimit

namespace OAI

/-! # Boundary algebra errors from the ordinary conjugacy gap

Scaling the unit-ball estimate supplies the exact boundary hypothesis
used in analytic smoothing, in both directions of conjugation.
-/

namespace KadisonKastler

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem infDist_le_norm_mul_of_kkDistance_lt
    {M N : VonNeumannAlgebra H} {δ : ℝ} (hgap : kkDistance M N < δ)
    {x : H →L[ℂ] H} (hx : x ∈ M) :
    Metric.infDist x (N : Set (H →L[ℂ] H)) ≤ δ * ‖x‖ := by
  by_cases hx0 : x = 0
  · subst x
    rw [Metric.infDist_zero_of_mem (show (0 : H →L[ℂ] H) ∈ (N : Set (H →L[ℂ] H)) from N.zero_mem), norm_zero, mul_zero]
  have hn : 0 < ‖x‖ := norm_pos_iff.mpr hx0
  let y : H →L[ℂ] H := (‖x‖⁻¹ : ℂ) • x
  have hy : y ∈ unitBall M := by
    refine ⟨M.toStarSubalgebra.smul_mem hx _, ?_⟩
    simp [y, norm_smul, Complex.norm_real, inv_mul_cancel₀ hn.ne']
  obtain ⟨z, hz, hyz⟩ := exists_unitBall_approx hy hgap
  have hdy : Metric.infDist y (N : Set (H →L[ℂ] H)) ≤ δ :=
    (Metric.infDist_le_dist_of_mem hz.1).trans (by simpa only [dist_eq_norm] using hyz.le)
  have he : x = (‖x‖ : ℂ) • y := by
    change x = (‖x‖ : ℂ) • ((‖x‖⁻¹ : ℂ) • x)
    rw [smul_smul, mul_inv_cancel₀ (Complex.ofReal_ne_zero.mpr hn.ne'), one_smul]
  calc
    Metric.infDist x (N : Set (H →L[ℂ] H)) =
        ‖x‖ * Metric.infDist y (N : Set (H →L[ℂ] H)) := by
      conv_lhs => rw [he, infDist_smul_algebra]
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hn]
    _ ≤ δ * ‖x‖ := by nlinarith

theorem kkDistance_inverse_conjugate (M : VonNeumannAlgebra H)
    (v : unitary (H →L[ℂ] H)) :
    kkDistance (unitaryConjugateAlgebra (star v) M) M =
      kkDistance (unitaryConjugateAlgebra v M) M := by
  have h := kkDistance_eq_of_conjugates
    (conjugates_unitaryConjugateAlgebra v M).symm
    (conjugates_unitaryConjugateAlgebra (star v) M)
  exact (kkDistance_comm _ _).trans h

theorem modulated_sandwich_eq (W : ℝ → unitary (H →L[ℂ] H))
    (t : ℝ) (x : H →L[ℂ] H) :
    modulatedUnitaryField W t * x * modulatedUnitaryField (fun s => star (W s)) t =
      ((Circle.exp t : ℂ) * (Circle.exp t : ℂ)) • unitaryConj (W t) x := by
  simp only [modulatedUnitaryField, Unitary.coe_star, unitaryConj,
    smul_mul_assoc, mul_smul_comm, smul_smul]

theorem infDist_modulated_sandwich_le
    (M : VonNeumannAlgebra H) (W : ℝ → unitary (H →L[ℂ] H))
    {δ : ℝ} (hgap : ∀ t, kkDistance (unitaryConjugateAlgebra (W t) M) M < δ)
    (t : ℝ) (x : H →L[ℂ] H) (hx : x ∈ M) :
    Metric.infDist
      (modulatedUnitaryField W t * x * modulatedUnitaryField (fun s => star (W s)) t)
      (M : Set (H →L[ℂ] H)) ≤ δ * ‖x‖ := by
  rw [modulated_sandwich_eq, infDist_smul_algebra, norm_mul, Circle.norm_coe, one_mul,
    one_mul]
  have hm : unitaryConj (W t) x ∈ unitaryConjugateAlgebra (W t) M := by
    change unitaryConj (W t) x ∈ (unitaryConjugateAlgebra (W t) M : Set (H →L[ℂ] H))
    rw [← conjugates_unitaryConjugateAlgebra (W t) M]
    exact Set.mem_image_of_mem _ hx
  simpa only [norm_unitaryConj] using infDist_le_norm_mul_of_kkDistance_lt (hgap t) hm

end

end KadisonKastler

end OAI
