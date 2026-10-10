import OAI.NumberTheory.DukePrimeDegree.Geometry.RootHolonomy

namespace OAI

/-!
# Root-leaf constancy along every stable root pair off a null set
-/

noncomputable section
open Set Filter MeasureTheory
open scoped Topology

namespace DukePrimeDegree
open PrimeDegreePackets

lemma root_conjugate_tendsto_one
    {n : ℕ} {i j : Fin n} (hij : i ≠ j)
    (ell : Fin n → ℝ) (hell : ∑ r, ell r = 0) (hneg : ell i - ell j < 0) (r : ℝ) :
    Tendsto (fun t : ℝ => diagonalOneParameter ell hell t *
      Matrix.SpecialLinearGroup.transvection hij r * diagonalOneParameter ell hell (-t))
      atTop (𝓝 1) := by
  have he (t : ℝ) : (ell i - ell j) * t = -((ell j - ell i) * t) := by ring
  have ht := Real.tendsto_exp_neg_atTop_nhds_zero.comp
    (Filter.Tendsto.const_mul_atTop (by linarith : 0 < ell j - ell i) tendsto_id)
  have hp : Tendsto (fun t : ℝ => Real.exp ((ell i - ell j) * t) * r) atTop (𝓝 0) := by
    simpa only [Function.comp_def, id_eq, he, zero_mul] using ht.mul_const r
  have h := (continuous_rootTransvection hij).tendsto 0 |>.comp hp
  simpa only [Function.comp_def, diagonal_conjugation_transvection,
    Matrix.SpecialLinearGroup.transvection_coeff_zero] using h

lemma basedRealMeasure_zero_of_unit (ν : Measure ℝ) (hunit : ν (Metric.ball 0 1) = 1) :
    basedRealMeasure ν 0 = ν := by
  have he : (Homeomorph.subRight (0 : ℝ) : ℝ → ℝ) = id := by
    funext x
    simp
  rw [basedRealMeasure, centerRealMeasure, he, Measure.map_id]
  simp only [anchorNormalize, hunit, inv_one, one_smul]

theorem exists_nullset_nonparallel_root_constancy
    (d : ℕ) {a b i j : Fin (d + 1)} (hab : a ≠ b) (hij : i ≠ j)
    (hf : ¬ (i = a ∧ j = b)) (hb : ¬ (i = b ∧ j = a))
    (μ : Measure (X (d + 1))) [IsFiniteMeasure μ]
    (hA : ∀ u : LogCoordinates d, μ.map (fun x => rightAction x (diagonalFlow u)) = μ) :
    ∃ N : Set (X (d + 1)), MeasurableSet N ∧ μ N = 0 ∧
      ∀ x ∉ N, ∀ t : ℝ, rightAction x (Matrix.SpecialLinearGroup.transvection hij t) ∉ N →
        intrinsicRootLeaf hab μ (rightAction x (Matrix.SpecialLinearGroup.transvection hij t)) =
          intrinsicRootLeaf hab μ x := by
  obtain ⟨ell, hell, hn, hw⟩ := exists_neutral_expanding_weights d hab hij hf hb
  obtain ⟨N, hN, hNzero, hhol⟩ := exists_nullset_neutral_root_holonomy d hab μ hA ell hell hn
  have hfree : ∀ᵐ x ∂μ, ∀ t : ℝ,
      rightAction x (Matrix.SpecialLinearGroup.transvection hab t) = x → t = 0 :=
    (ae_root_stabilizer_trivial d μ hA).mono fun x hx => hx a b hab
  obtain ⟨E, hbad, hE, hEzero⟩ := exists_measurable_superset_of_null
    (ae_iff.mp ((ae_intrinsicRootLeaf_spec hab μ hfree).mono fun _ h => h.2))
  refine ⟨N ∪ E, hN.union hE, measure_union_null hNzero hEzero, ?_⟩
  intro x hx t hy
  have hunit : intrinsicRootLeaf hab μ x (Metric.ball 0 1) = 1 := by
    by_contra h
    exact hx (Or.inr (hbad h))
  have h := hhol x (fun h => hx (Or.inl h))
    (rightAction x (Matrix.SpecialLinearGroup.transvection hij t)) (fun h => hy (Or.inl h))
    (Matrix.SpecialLinearGroup.transvection hij t) rfl 0 (by
      simpa only [Matrix.SpecialLinearGroup.transvection_coeff_zero] using
        root_conjugate_tendsto_one hij ell hell (by linarith) t)
  rwa [basedRealMeasure_zero_of_unit _ hunit] at h

end DukePrimeDegree

end

end OAI
