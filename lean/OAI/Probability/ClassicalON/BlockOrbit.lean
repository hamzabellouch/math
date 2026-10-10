import OAI.Probability.ClassicalON.BlockGeometry

namespace OAI

universe uV

noncomputable section
open MeasureTheory
open scoped InnerProductSpace Classical
namespace ClassicalON

theorem orthogonalSpin_eval_preserves (n : ℕ) [NeZero n] (s : Spin n) :
    MeasurePreserving (fun Q : SpinOrthogonal n => orthogonalSpin Q s)
      (orthogonalLaw n) (sphereProbability n) := by
  have hc : Continuous (fun Q : SpinOrthogonal n => orthogonalSpin Q s) :=
    (continuous_orthogonalSpin n).comp (continuous_id.prodMk continuous_const)
  refine ⟨hc.measurable,?_⟩
  apply Measure.ext_of_integral_eq_on_compactlySupported
  intro f
  rw [integral_map (f := fun x => f x) hc.measurable.aemeasurable f.continuous.aestronglyMeasurable]
  exact integral_orthogonalSpin_eq f f.continuous s

variable {V : Type uV} [Fintype V]

def blockFiberConfiguration (k : ℕ) (s : V → Spin (3+k)) (t : V → Spin 3) : V → Spin (3+k) :=
  fun v => blockFiber k (s v) (t v)

omit [Fintype V] in
theorem continuous_blockFiberConfiguration (k : ℕ) :
    Continuous (Function.uncurry (blockFiberConfiguration (V := V) k)) := by
  apply continuous_pi
  intro v
  exact (continuous_blockFiber k).comp
    (f := fun p : (V → Spin (3+k))×(V → Spin 3) => (p.1 v,p.2 v))
    (((continuous_apply v).comp continuous_fst).prodMk ((continuous_apply v).comp continuous_snd))

def blockRotateConfiguration (k : ℕ) (Q : V → SpinOrthogonal 3) :
    (V → Spin (3+k)) ≃ₜ (V → Spin (3+k)) :=
  SpinSystem.rotateConfiguration (fun v => blockRotation k (Q v))

omit [Fintype V] in
theorem blockRotateConfiguration_fiber (k : ℕ) (Q : V → SpinOrthogonal 3) (s : V → Spin (3+k)) :
    blockRotateConfiguration k Q s=
      blockFiberConfiguration k s (fun v => orthogonalSpin (Q v) (blockDirection k (s v))) := by
  funext v
  exact blockRotateSpin_fiber k (Q v) (s v)

omit [Fintype V] in
theorem continuous_blockRotateConfiguration (k : ℕ) : Continuous
    (fun p : (V → SpinOrthogonal 3)×(V → Spin (3+k)) => blockRotateConfiguration k p.1 p.2) := by
  apply continuous_pi
  intro v
  exact (continuous_blockRotateSpin k).comp
    (f := fun p : (V → SpinOrthogonal 3)×(V → Spin (3+k)) => (p.1 v,p.2 v))
    (((continuous_apply v).comp continuous_fst).prodMk ((continuous_apply v).comp continuous_snd))

theorem blockRotateConfiguration_preserves (k : ℕ) (Q : V → SpinOrthogonal 3) :
    MeasurePreserving (blockRotateConfiguration k Q) (freeSpinReference (3+k)) (freeSpinReference (3+k)) :=
  measurePreserving_pi (fun _ : V => sphereProbability (3+k)) (fun _ => sphereProbability (3+k))
    (fun v => spinRotation_preserves_probability (blockRotation k (Q v)))

def orthogonalConfigurationLaw : Measure (V → SpinOrthogonal 3) := Measure.pi (fun _ => orthogonalLaw 3)
instance orthogonalConfigurationLaw_isProbability : IsProbabilityMeasure (orthogonalConfigurationLaw (V := V)) := by
  unfold orthogonalConfigurationLaw
  infer_instance

theorem integral_block_orbit (k : ℕ) (f : (V → Spin (3+k)) → ℝ) (hf : Continuous f)
    (s : V → Spin (3+k)) :
    (∫ Q,f (blockRotateConfiguration k Q s) ∂orthogonalConfigurationLaw)=
      ∫ t,f (blockFiberConfiguration k s t) ∂freeSpinReference 3 := by
  have hp := measurePreserving_pi (fun _ : V => orthogonalLaw 3) (fun _ => sphereProbability 3)
    (fun v => orthogonalSpin_eval_preserves 3 (blockDirection k (s v)))
  have hc : Continuous (fun t : V → Spin 3 => f (blockFiberConfiguration k s t)) :=
    hf.comp ((continuous_blockFiberConfiguration k).comp
      (f := fun t : V → Spin 3 => (s,t)) (continuous_const.prodMk continuous_id))
  rw [show freeSpinReference (V := V) 3=
      (orthogonalConfigurationLaw (V := V)).map
        (fun Q v => orthogonalSpin (Q v) (blockDirection k (s v))) from hp.map_eq.symm,
    integral_map hp.measurable.aemeasurable hc.aestronglyMeasurable]
  apply integral_congr_ae
  filter_upwards with Q
  rw [blockRotateConfiguration_fiber]

theorem integral_freeSpinReference_block (k : ℕ) (f : (V → Spin (3+k)) → ℝ) (hf : Continuous f) :
    (∫ s,f s ∂freeSpinReference (3+k))=
      ∫ s,∫ t,f (blockFiberConfiguration k s t) ∂freeSpinReference 3 ∂freeSpinReference (3+k) := by
  let : NeZero (3+k) := ⟨by omega⟩
  have hc : Continuous (fun p : (V → Spin (3+k))×(V → SpinOrthogonal 3) =>
      f (blockRotateConfiguration k p.2 p.1)) :=
    hf.comp ((continuous_blockRotateConfiguration k).comp
      (f := (Prod.swap : (V → Spin (3+k))×(V → SpinOrthogonal 3) →
        (V → SpinOrthogonal 3)×(V → Spin (3+k)))) continuous_swap)
  have he := integral_integral_swap (μ := freeSpinReference (3+k)) (ν := orthogonalConfigurationLaw)
    (f := fun s Q => f (blockRotateConfiguration k Q s)) (compact_integrable hc)
  have hi (Q : V → SpinOrthogonal 3) :
      (∫ s,f (blockRotateConfiguration k Q s) ∂freeSpinReference (3+k))=∫ s,f s ∂freeSpinReference (3+k) :=
    (blockRotateConfiguration_preserves k Q).integral_comp
      (blockRotateConfiguration k Q).measurableEmbedding f
  simp_rw [hi] at he
  simp only [integral_const,probReal_univ,one_smul] at he
  rw [← he]
  exact integral_congr_ae (Filter.Eventually.of_forall (integral_block_orbit k f hf))

end ClassicalON

end

end OAI
