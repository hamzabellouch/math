import OAI.Probability.InvariantIsing.Cavity.CavityCascadeCovariance

namespace OAI

/-! The grouped Gaussian covariance on rounded cascades is positive
semidefinite from monotone synchronized coordinates and diagonal excess. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Filter Set
open scoped BigOperators Topology Matrix

namespace InvariantIsing

theorem cavity_cascade_synchronized_covariance_posSemidef {m r q : ℕ}
    (n : ℕ) (b a : ℕ → ℝ) (ha : Monotone a) (ha0 : 0 ≤ a 0) (ha1 : a n ≤ 1)
    (d : SpectralEntry (m + 1)) (f : Fin (m + 1) → ℝ → Icc (-1 : ℝ) 1)
    (hf : ∀ j, Continuous (f j))
    (hmono : ∀ j : Fin m, Monotone (fun t => (f j.castSucc t : ℝ)))
    (h0 : ∀ j : Fin m, 0 ≤ (f j.castSucc (a 0) : ℝ))
    (hD : ∀ j : Fin m, (f j.castSucc (a n) : ℝ) ≤ (d j.castSucc : ℝ))
    (ρ : Fin m → ℝ) (hρ : ∀ j, 0 ≤ ρ j) :
    ∀ᵐ x ∂(cascadeCompactLaw n b a : Measure JointArray),
      (cavitySpectralBlockCovariance q ρ
        (cavitySynchronizedBlock d f (arrayBlock spinArray r x))).PosSemidef := by
  let C := fun x : JointArray => cavitySpectralBlockCovariance q ρ
    (cavitySynchronizedBlock d f (arrayBlock spinArray r x))
  have hC : Continuous C := (continuous_cavitySpectralBlockCovariance q ρ).comp
    ((continuous_cavitySynchronizedBlock d f hf).comp (by unfold arrayBlock spinArray; fun_prop))
  have hMap : Measurable (fun σ : ℕ → LabeledLeaf n =>
      compactScalarArray (diagonalPatch 1 (cascadeScalarArray n a σ))) :=
    continuous_compactScalarArray.measurable.comp
      ((measurable_diagonalPatch 1).comp (measurable_cascadeScalarArray n a))
  change ∀ᵐ x ∂(cascadeReplicaLaw n b).map (fun σ =>
    compactScalarArray (diagonalPatch 1 (cascadeScalarArray n a σ))), (C x).PosSemidef
  apply (ae_map_iff hMap.aemeasurable (Matrix.posSemidef_is_closed.preimage hC).measurableSet).mpr
  apply ae_of_all
  intro σ
  change (cavitySpectralBlockCovariance q ρ (cavitySynchronizedBlock d f
    (arrayBlock spinArray r (compactScalarArray (diagonalPatch 1 (cascadeScalarArray n a σ)))))).PosSemidef
  apply cavityGroupReplicaCovariance_posSemidef
  intro j
  have h := (cavity_cascade_transformed_gram n ha (fun t => (f j.castSucc t : ℝ))
    (hmono j) (h0 j) (hD j) σ r).smul (inv_nonneg.mpr (hρ j))
  have he : (fun i k : Fin r =>
      (cavitySynchronizedBlock d f
        (arrayBlock spinArray r (compactScalarArray (diagonalPatch 1 (cascadeScalarArray n a σ)))))
        i k j.castSucc / ρ j) =
      (ρ j)⁻¹ • (fun i k : Fin r =>
        if i = k then (d j.castSucc : ℝ) else (f j.castSucc (cascadeScalarArray n a σ i k) : ℝ)) := by
    funext i k
    simp only [cavitySynchronizedBlock, arrayBlock, cascadeCompact_spin n ha ha0 ha1 σ,
      Pi.smul_apply, smul_eq_mul]
    by_cases hik : i = k
    · subst k
      simp only [ite_true]
      ring
    · simp only [ite_eq_right hik, diagonalPatch, Fin.val_inj]
      ring
  rw [he]
  exact h

end InvariantIsing

end

end OAI
