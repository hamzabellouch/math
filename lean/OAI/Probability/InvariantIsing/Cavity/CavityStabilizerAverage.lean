import OAI.Probability.InvariantIsing.Cavity.CavitySpectralStabilizer

namespace OAI

/-! Averaging fresh frames inside the spectral groups preserves the
base interaction. This identity also allows bounded Gibbs tests. -/

noncomputable section
open MeasureTheory
open scoped Matrix

namespace InvariantIsing

lemma cavityBaseSpecialAction_stabilizer {N d : ℕ} (V R : Orthogonal N)
    (D : Matrix (Fin N) (Fin N) ℝ) (F : Matrix (Fin N) (Fin d) ℝ)
    (hR : cavityConjugate R D = D) :
    cavityBaseSpecialAction (V * R) (D, F) =
      (cavityConjugate V D, (V : Matrix (Fin N) (Fin N) ℝ) *
        ((R : Matrix (Fin N) (Fin N) ℝ) * F)) := by
  rw [cavityBaseSpecialAction_mul]
  apply Prod.ext
  · change cavityConjugate V (cavityConjugate R D) = cavityConjugate V D
    rw [hR]
  · rfl

theorem cavity_spectral_stabilizer_average {N m d : ℕ}
    (k : Fin m → ℕ) (e : ((a : Fin m) × Fin (k a)) ≃ Fin N)
    (lam : Fin m → ℝ) (F : Matrix (Fin N) (Fin d) ℝ)
    (μ : Measure (Orthogonal N)) [IsProbabilityMeasure μ] [μ.IsMulRightInvariant]
    (ν : Measure ((a : Fin m) → Orthogonal (k a))) [IsProbabilityMeasure ν]
    (f : (Matrix (Fin N) (Fin N) ℝ × Matrix (Fin N) (Fin d) ℝ) → ℝ)
    (hf : Measurable f) (C : ℝ) (hb : ∀ p, ‖f p‖ ≤ C) :
    (∫ V, f (cavityBaseSpecialAction V
      (Matrix.diagonal (fun j => lam (e.symm j).1), F)) ∂μ) =
    ∫ V, ∫ W, f (cavityConjugate V (Matrix.diagonal (fun j => lam (e.symm j).1)),
      (V : Matrix (Fin N) (Fin N) ℝ) *
        ((cavityGroupRotation k e W : Matrix (Fin N) (Fin N) ℝ) * F)) ∂ν ∂μ := by
  let : BorelSpace (Matrix (Fin N) (Fin N) ℝ × Matrix (Fin N) (Fin d) ℝ) :=
    inferInstanceAs (BorelSpace ((Fin N → Fin N → ℝ) × (Fin N → Fin d → ℝ)))
  let : SecondCountableTopology (Matrix (Fin N) (Fin N) ℝ) :=
    inferInstanceAs (SecondCountableTopology (Fin N → Fin N → ℝ))
  let : SecondCountableTopology (Orthogonal N) :=
    (show Topology.IsInducing (Subtype.val : Orthogonal N → Matrix (Fin N) (Fin N) ℝ) from
      Topology.IsInducing.subtypeVal).secondCountableTopology
  let (a : Fin m) : SecondCountableTopology (Orthogonal (k a)) := by
    let : SecondCountableTopology (Matrix (Fin (k a)) (Fin (k a)) ℝ) :=
      inferInstanceAs (SecondCountableTopology (Fin (k a) → Fin (k a) → ℝ))
    exact (show Topology.IsInducing
      (Subtype.val : Orthogonal (k a) → Matrix (Fin (k a)) (Fin (k a)) ℝ) from
        Topology.IsInducing.subtypeVal).secondCountableTopology
  let D : Matrix (Fin N) (Fin N) ℝ := Matrix.diagonal (fun j => lam (e.symm j).1)
  let T := fun p : Orthogonal N × ((a : Fin m) → Orthogonal (k a)) =>
    f (cavityBaseSpecialAction (p.1 * cavityGroupRotation k e p.2) (D, F))
  have hrot : Continuous (fun p : Orthogonal N × ((a : Fin m) → Orthogonal (k a)) =>
      p.1 * cavityGroupRotation k e p.2) :=
    continuous_fst.mul ((continuous_cavityGroupRotation k e).comp continuous_snd)
  have hT : Measurable T := hf.comp
    (((continuous_cavityBaseSpecialAction N d).comp (hrot.prodMk continuous_const)).measurable)
  have hi : Integrable T (μ.prod ν) := Integrable.of_bound hT.aestronglyMeasurable C
    (ae_of_all _ (fun p => hb _))
  have hrow (W : (a : Fin m) → Orthogonal (k a)) :
      (∫ V, T (V, W) ∂μ) = ∫ V, f (cavityBaseSpecialAction V (D, F)) ∂μ :=
    integral_mul_right_eq_self (fun V => f (cavityBaseSpecialAction V (D, F)))
      (cavityGroupRotation k e W)
  have hpoint (V : Orthogonal N) (W : (a : Fin m) → Orthogonal (k a)) :
      T (V, W) = f (cavityConjugate V D,
        (V : Matrix (Fin N) (Fin N) ℝ) *
          ((cavityGroupRotation k e W : Matrix (Fin N) (Fin N) ℝ) * F)) := by
    exact congrArg f (cavityBaseSpecialAction_stabilizer V (cavityGroupRotation k e W) D F
      (cavityGroupRotation_conjugate k e W lam))

  calc
    _ = ∫ W, ∫ V, T (V, W) ∂μ ∂ν := by simp only [hrow]; simp [D]
    _ = ∫ V, ∫ W, T (V, W) ∂ν ∂μ := (integral_integral_swap hi).symm
    _ = _ := by simp only [hpoint, D]

end InvariantIsing

end

end OAI
