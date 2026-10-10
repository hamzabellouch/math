import OAI.Geometry.RCD.Coordinates.GramNormalization

namespace OAI

/-! # Construction of exact normalizers for positive definite Gram operators -/

open scoped BigOperators InnerProductSpace

noncomputable section

namespace RegularPointCoordinates

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- A positive definite symmetric operator admits an exact congruence
normalization. The proof constructs it in an orthonormal eigenbasis. -/
theorem exists_exact_operator_normalization (Q : E →L[ℝ] E)
    (hQ : Q.IsSymmetric) (hpos : ∀ v : E, v ≠ 0 → 0 < ⟪v, Q v⟫_ℝ) :
    ∃ A : E ≃L[ℝ] E,
      (A : E →L[ℝ] E).adjoint.comp (Q.comp (A : E →L[ℝ] E)) =
        ContinuousLinearMap.id ℝ E := by
  let b := hQ.eigenvectorBasis rfl
  let lam := hQ.eigenvalues rfl
  have hlam (i : Fin (Module.finrank ℝ E)) : 0 < lam i := by
    have hn : b i ≠ 0 := b.orthonormal.ne_zero i
    have hp := hpos (b i) hn
    have he : Q (b i) = lam i • b i := hQ.apply_eigenvectorBasis rfl i
    rw [he, inner_smul_right] at hp
    simpa only [real_inner_self_eq_norm_sq, b.norm_eq_one, one_pow, mul_one] using hp
  let L : E →L[ℝ] E := ∑ i : Fin (Module.finrank ℝ E),
    ((EuclideanSpace.proj i).comp (b.repr.toContinuousLinearEquiv :
      E →L[ℝ] Euclidean (Module.finrank ℝ E))).smulRight
        ((Real.sqrt (lam i))⁻¹ • b i)
  have hL (v : E) (i : Fin (Module.finrank ℝ E)) :
      b.repr (L v) i = (Real.sqrt (lam i))⁻¹ * b.repr v i := by
    simp [L, map_sum, map_smul, b.repr_self, Pi.single_apply, mul_comm]
  have hQL (v : E) (i : Fin (Module.finrank ℝ E)) :
      b.repr (Q (L v)) i = lam i * ((Real.sqrt (lam i))⁻¹ * b.repr v i) := by
    have he := hQ.eigenvectorBasis_apply_self_apply rfl (L v) i
    change b.repr (Q (L v)) i = lam i * b.repr (L v) i at he
    rw [he, hL]
  have henergy (v : E) : ⟪L v, Q (L v)⟫_ℝ = ‖v‖ ^ 2 := by
    rw [← b.repr.inner_map_map]
    simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial]
    rw [← b.repr.norm_map v, EuclideanSpace.real_norm_sq_eq]
    apply Finset.sum_congr rfl
    intro i _
    rw [hL, hQL]
    have hs : Real.sqrt (lam i) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr (hlam i))
    have hs2 := Real.sq_sqrt (hlam i).le
    field_simp
    nlinarith
  have hinj : Function.Injective L := by
    apply (LinearMap.ker_eq_bot).mp
    apply LinearMap.ker_eq_bot'.mpr
    intro v hv
    change L v = 0 at hv
    have he := henergy v
    rw [hv, inner_zero_left] at he
    exact norm_eq_zero.mp (sq_eq_zero_iff.mp he.symm)
  let A : E ≃L[ℝ] E := (LinearEquiv.ofInjectiveEndo L.toLinearMap hinj).toContinuousLinearEquiv
  refine ⟨A, ?_⟩
  apply ContinuousLinearMap.ext
  intro v
  apply ext_inner_right ℝ
  intro w
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.adjoint_inner_left,
    ContinuousLinearMap.id_apply]
  have hpair : ∀ v w : E, ⟪L v, Q (L w)⟫_ℝ = ⟪v, w⟫_ℝ := by
    intro v w
    have hplus := henergy (v + w)
    have hv := henergy v
    have hw := henergy w
    have hsym : ⟪L w, Q (L v)⟫_ℝ = ⟪L v, Q (L w)⟫_ℝ := by
      calc
        _ = ⟪Q (L v), L w⟫_ℝ := real_inner_comm _ _
        _ = _ := hQ _ _
    simp only [map_add, inner_add_left, inner_add_right, hsym] at hplus
    rw [norm_add_sq_real] at hplus
    linarith
  change ⟪Q (L v), L w⟫_ℝ = ⟪v, w⟫_ℝ
  exact (hQ _ _).trans (hpair v w)

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]
  (μ : MeasureTheory.Measure X) (hQ : QuadraticCheegerEnergy μ)
  (U : E →L[ℝ] SobolevSpace μ hQ)

/-- Positive definiteness of the actual mean energy suffices to construct
the exact normalizer; the normalizer itself need not be assumed. -/
theorem exists_exact_mean_normalization (s : Set X) (hs : MeasurableSet s)
    (hpos : ∀ v : E, v ≠ 0 → 0 < ⟪v, sobolevMeanGram μ hQ U s hs v⟫_ℝ) :
    ∃ A : E ≃L[ℝ] E, IsExactMeanNormalization μ hQ U s hs A := by
  obtain ⟨A, hA⟩ := exists_exact_operator_normalization
    (sobolevMeanGram μ hQ U s hs) (sobolevMeanGram_isPositive μ hQ U s hs).isSymmetric hpos
  refine ⟨A, ?_⟩
  unfold IsExactMeanNormalization
  rw [sobolevMeanGram_comp, hA]

end RegularPointCoordinates

end

end OAI
