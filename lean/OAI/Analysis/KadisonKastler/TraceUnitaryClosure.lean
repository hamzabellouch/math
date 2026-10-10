import OAI.Analysis.KadisonKastler.CountableTraceGroup

namespace OAI

/-! # Closure of unitary vectors in a finite trace representation -/

namespace KadisonKastler

noncomputable section

variable {A : Type*} [CStarAlgebra A]

private theorem star_mul_eq_one_of_trace_norm_one
    (τ : FaithfulTracialState A) (a : A) (ha : ‖a‖ ≤ 1)
    (hτa : traceTwoNorm τ a = 1) : star a * a = 1 := by
  let : PartialOrder A := CStarAlgebra.spectralOrder A
  let : StarOrderedRing A := CStarAlgebra.spectralOrderedRing A
  have hb : star a * a ≤ 1 := by
    apply (CStarAlgebra.norm_le_one_iff_of_nonneg (star a * a)).mp
    rw [CStarRing.norm_star_mul_self]
    nlinarith [norm_nonneg a]
  obtain ⟨c, hc⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp (sub_nonneg.mpr hb)
  have ht : τ.toLinearMap (star a * a) = 1 := by
    apply Complex.ext
    · have h := traceTwoNorm_sq τ a
      rw [hτa] at h
      simpa only [one_pow, Complex.one_re] using h.symm
    · simpa only [Complex.one_im] using τ.positive_im a
  have hcτ : τ.toLinearMap (star c * c) = 0 := by
    rw [← hc, map_sub, τ.map_one, ht, sub_self]
  have hc0 := τ.faithful c hcτ
  have hz : (1 : A) - star a * a = 0 := by rw [hc, hc0, star_zero, zero_mul]
  exact (sub_eq_zero.mp hz).symm

/-- A contraction attaining trace two-norm one is unitary. -/
theorem mem_unitary_of_traceTwoNorm_eq_one
    (τ : FaithfulTracialState A) (a : A) (ha : ‖a‖ ≤ 1)
    (hτa : traceTwoNorm τ a = 1) : a ∈ unitary A := by
  refine ⟨star_mul_eq_one_of_trace_norm_one τ a ha hτa, ?_⟩
  simpa only [star_star] using star_mul_eq_one_of_trace_norm_one τ (star a)
    (by simpa only [norm_star] using ha) (by simpa only [traceTwoNorm_star] using hτa)

variable {H E : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] {M : VonNeumannAlgebra H}

/-- The unitary vectors form a closed subset of any faithful tracial
Hilbert realization of a concrete finite algebra. -/
theorem FiniteVectorTrace.isClosed_traceUnitary_image
    {τ : FaithfulTracialState (Algebra M)} (hτ : FiniteVectorTrace τ)
    (J : Algebra M →ₗ[ℂ] E) (hJ : ∀ a, ‖J a‖ = traceTwoNorm τ a) :
    IsClosed (J '' (unitary (Algebra M) : Set (Algebra M))) := by
  have hball : J '' (unitary (Algebra M) : Set (Algebra M)) ⊆
      J '' Metric.closedBall (0 : Algebra M) 1 := by
    rintro _ ⟨u, hu, rfl⟩
    refine ⟨u, ?_, rfl⟩
    simpa only [Metric.mem_closedBall, dist_zero_right] using
      norm_unitary_le_one (⟨u, hu⟩ : unitary (Algebra M))
  have hnorm : J '' (unitary (Algebra M) : Set (Algebra M)) ⊆ {v | ‖v‖ = 1} := by
    rintro _ ⟨u, hu, rfl⟩
    rw [Set.mem_ofPred_eq, hJ]
    simpa only [mul_one, traceTwoNorm_one] using
      traceTwoNorm_unitary_mul τ (⟨u, hu⟩ : unitary (Algebra M)) (1 : Algebra M)
  apply isClosed_of_closure_subset
  intro v hv
  obtain ⟨a, ha, hav⟩ :=
    (closure_minimal hball (hτ.isClosed_traceHilbert_ball J hJ 0 (by norm_num))) hv
  have hvnorm : ‖v‖ = 1 :=
    (closure_minimal hnorm (isClosed_eq continuous_norm continuous_const)) hv
  refine ⟨a, mem_unitary_of_traceTwoNorm_eq_one τ a ?_ ?_, hav⟩
  · simpa only [Metric.mem_closedBall, dist_zero_right] using ha
  · rw [← hJ, hav, hvnorm]

end

end KadisonKastler

end OAI
