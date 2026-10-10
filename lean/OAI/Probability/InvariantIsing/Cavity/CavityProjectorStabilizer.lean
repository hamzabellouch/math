import OAI.Probability.InvariantIsing.Cavity.CavityGroupOverlapInvariant
import OAI.Probability.InvariantIsing.Cavity.CavityProjectorHaarMean
import OAI.Probability.InvariantIsing.Cavity.CavityStabilizerAverage

namespace OAI

/-! Independent rotations in each labeled spectral subspace preserve
all base projectors, while rotating the selected cavity axes. -/

noncomputable section
open MeasureTheory
open scoped Matrix

namespace InvariantIsing

lemma cavityGroupRotation_spectralProjector {N m : ℕ}
    (k : Fin m → ℕ) (e : ((a : Fin m) × Fin (k a)) ≃ Fin N)
    (V : Orthogonal N) (W : (a : Fin m) → Orthogonal (k a)) (a : Fin m) :
    cavitySpectralProjector (V*cavityGroupRotation k e W)
      (cavitySpectralGroup (fun i => (e.symm i).1) a) =
    cavitySpectralProjector V (cavitySpectralGroup (fun i => (e.symm i).1) a) := by
  rw [cavitySpectralProjector, cavitySpectralProjector, cavityConjugate_mul]
  have hmask : (Matrix.diagonal (fun i : Fin N =>
      if i ∈ cavitySpectralGroup (fun i => (e.symm i).1) a then (1 : ℝ) else 0)) =
      Matrix.diagonal (fun i => (fun b => if b=a then (1 : ℝ) else 0) (e.symm i).1) := by
    congr 1
    funext i
    simp only [cavitySpectralGroup, Finset.mem_filter, Finset.mem_univ, true_and]
  rw [hmask, cavityGroupRotation_conjugate k e W (fun b => if b=a then (1 : ℝ) else 0)]

theorem cavity_labeled_stabilizer_average {N m d : ℕ}
    (k : Fin m → ℕ) (e : ((a : Fin m) × Fin (k a)) ≃ Fin N)
    (S : Matrix (Fin N) (Fin d) ℝ)
    (μ : Measure (Orthogonal N)) [IsProbabilityMeasure μ] [μ.IsMulRightInvariant]
    (η : Measure ((a : Fin m) → Orthogonal (k a))) [IsProbabilityMeasure η]
    (f : CavityProjectorFrame N m d → ℝ) (hf : Measurable f)
    (C : ℝ) (hb : ∀ p, ‖f p‖ ≤ C) :
    (∫ V, f (fun a => cavitySpectralProjector V
      (cavitySpectralGroup (fun i => (e.symm i).1) a),
      (V : Matrix (Fin N) (Fin N) ℝ)*S) ∂μ) =
    ∫ V, ∫ W, f (fun a => cavitySpectralProjector V
      (cavitySpectralGroup (fun i => (e.symm i).1) a),
      (V : Matrix (Fin N) (Fin N) ℝ)*
        ((cavityGroupRotation k e W : Matrix (Fin N) (Fin N) ℝ)*S)) ∂η ∂μ := by
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
  let h : Orthogonal N → ℝ := fun V => f
    (fun a => cavitySpectralProjector V (cavitySpectralGroup (fun i => (e.symm i).1) a),
      (V : Matrix (Fin N) (Fin N) ℝ)*S)
  have hm : Measurable h := by
    apply hf.comp
    apply Measurable.prodMk
    · apply Measurable.of_eval
      intro a
      exact ((continuous_cavityConjugate N).comp
        (continuous_id.prodMk continuous_const)).measurable
    · exact (continuous_subtype_val.matrix_mul continuous_const).measurable
  let H := fun p : Orthogonal N × ((a : Fin m) → Orthogonal (k a)) =>
    h (p.1*cavityGroupRotation k e p.2)
  have hrot : Continuous (fun p : Orthogonal N × ((a : Fin m) → Orthogonal (k a)) =>
      p.1*cavityGroupRotation k e p.2) :=
    continuous_fst.mul ((continuous_cavityGroupRotation k e).comp continuous_snd)
  have hi : Integrable H (μ.prod η) := Integrable.of_bound
    (hm.comp hrot.measurable).aestronglyMeasurable C (ae_of_all _ fun p => hb _)
  have hrow W : (∫ V, H (V,W) ∂μ) = ∫ V, h V ∂μ :=
    integral_mul_right_eq_self h (cavityGroupRotation k e W)
  have heq V W : H (V,W) = f
      (fun a => cavitySpectralProjector V (cavitySpectralGroup (fun i => (e.symm i).1) a),
      (V : Matrix (Fin N) (Fin N) ℝ)*
        ((cavityGroupRotation k e W : Matrix (Fin N) (Fin N) ℝ)*S)) := by
    dsimp only [H, h]
    simp only [cavityGroupRotation_spectralProjector]
    rw [show ((V*cavityGroupRotation k e W : Orthogonal N) : Matrix (Fin N) (Fin N) ℝ) =
      (V : Matrix (Fin N) (Fin N) ℝ)*(cavityGroupRotation k e W : Matrix (Fin N) (Fin N) ℝ) from rfl,
      Matrix.mul_assoc]
  calc
    _ = ∫ W, ∫ V, H (V,W) ∂μ ∂η := by simp only [hrow]; simp [h]
    _ = ∫ V, ∫ W, H (V,W) ∂η ∂μ := (integral_integral_swap hi).symm
    _ = _ := by simp only [heq]

end InvariantIsing

end

end OAI
