import OAI.Probability.InvariantIsing.Magnetic.RestrictedCanonicalLogIntegrability
import OAI.Probability.InvariantIsing.Cavity.CavityProjectorJointLaw
import OAI.Probability.InvariantIsing.Cavity.CavityCompressionFactorBound

namespace OAI

/-! Haar averaging of the two logarithmic terms in the physical
cavity inequality.  Integrability follows from the actual frame and
coefficient bounds. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron

namespace InvariantIsing

theorem restricted_physical_log_average {N n m d depth : ℕ}
    (S : Finset (Spin N)) (hS : S.Nonempty) (C : Finset (Spin n)) (hC : C.Nonempty)
    (g : Fin (N+n) → Fin m) (k : Fin m → ℕ)
    (ek : ∀ a, {i : Fin (N+n) // g i=a} ≃ Fin (k a+n))
    (e : (((a : Fin m) × Fin (k a)) ⊕ Fin d) ≃ Fin N)
    (es : Fin (m*n) ≃ Fin (d+n)) (B₀ : Matrix (Fin (d+n)) (Fin d) ℝ)
    (a₀ : Fin d → Fin m) (l r : Fin m → ℕ)
    (hg : ∀ a i, g i=a ↔ l a ≤ i.val ∧ i.val<r a)
    (hln : ∀ a, l a+n ≤ r a) (hr : ∀ a, r a ≤ N+n)
    (μ : Measure (Orthogonal (N+n))) [IsProbabilityMeasure μ] [μ.IsMulRightInvariant]
    (ν : Measure (Orthogonal N)) [IsProbabilityMeasure ν] [ν.IsMulRightInvariant]
    (T : LabeledTree depth) (lam v : Fin m → ℝ) (u : ℕ → ℝ)
    (hu : ∀ j, |u j| ≤ 2) (t cap δ : ℝ) (hcap : 0 ≤ cap) :
    let A := fun U => cavityCompressionFactorBlocks es lam (fun j => lam (a₀ j)) B₀
      (cavityCompressionGrams g U)
    let p := fun U => cavityPhysicalLabeledProjectors g (cavityConcreteComplement es B₀) a₀ U
    let q := fun V => cavityLabeledProjectorAction V (cavityCanonicalProjectorFrame k e a₀)
    let c := fun a => t*lam a+2*perturbationScale N*v a
    Integrable (fun U => restrictedProjectorCappedLog S hS C hC T c u t cap δ (A U) (p U) +
      restrictedProjectorLogPartition S hS T c u (p U).1) μ ∧
    (∫ U, restrictedProjectorCappedLog S hS C hC T c u t cap δ (A U) (p U) +
      restrictedProjectorLogPartition S hS T c u (p U).1 ∂μ) =
      (∫ z, restrictedProjectorCappedLog S hS C hC T c u t cap δ (A z.1) (q z.2) ∂μ.prod ν) +
      ∫ V, restrictedProjectorLogPartition S hS T c u (q V).1 ∂ν := by
  intro A p q c
  let f := fun z : (Fin m → Matrix (Fin n) (Fin n) ℝ) × CavityProjectorFrame N m d =>
    restrictedProjectorCappedLog S hS C hC T c u t cap δ
      (cavityCompressionFactorBlocks es lam (fun j => lam (a₀ j)) B₀ z.1) z.2 +
      restrictedProjectorLogPartition S hS T c u z.2.1
  have hf : Measurable f :=
    (measurable_restrictedProjectorCappedLog S hS C hC T c u t cap δ _
      ((measurable_cavityCompressionFactorBlocks es lam (fun j => lam (a₀ j)) B₀).comp
        measurable_fst) _ measurable_snd).add
      (measurable_restrictedProjectorLogPartition S hS T c u _ measurable_snd.fst)
  have hA : Measurable A :=
    (measurable_cavityCompressionFactorBlocks es lam (fun j => lam (a₀ j)) B₀).comp
      (measurable_cavityCompressionGrams g)
  have hi₁ := integrable_restricted_canonical_capped_log S hS C hC μ ν k e a₀ T lam v u hu t cap δ hcap
    A hA (fun U => cavity_compression_factor_size_bound g es lam (fun j => lam (a₀ j)) B₀ U)
  have hi₂ := (integrable_restricted_canonical_log_partition S hS k e a₀ ν T lam v u hu t).comp_snd μ
  have hi : Integrable (fun z => f (cavityCompressionGrams g z.1,q z.2)) (μ.prod ν) :=
    hi₁.add hi₂
  let F := fun U => (cavityCompressionGrams g U,p U)
  let G := fun z : Orthogonal (N+n) × Orthogonal N => (cavityCompressionGrams g z.1,q z.2)
  have hF : Measurable F := (measurable_cavityCompressionGrams g).prodMk
    (measurable_cavityPhysicalLabeledProjectors g _ (measurable_cavityConcreteComplement es B₀) a₀)
  have hG : Measurable G := ((measurable_cavityCompressionGrams g).comp measurable_fst).prodMk
    ((measurable_cavityCanonicalProjectorAction k e a₀).comp measurable_snd)
  have hmap : μ.map F = (μ.prod ν).map G :=
    cavity_labeled_projector_joint_law g k ek e es B₀ a₀ l r hg hln hr μ ν
  have him : Integrable f (μ.map F) := by
    rw [hmap]
    exact (integrable_map_measure hf.aestronglyMeasurable hG.aemeasurable).mpr hi
  have hip := (integrable_map_measure hf.aestronglyMeasurable hF.aemeasurable).mp him
  refine ⟨hip, ?_⟩
  have he := cavity_labeled_projector_joint_integral g k ek e es B₀ a₀ l r hg hln hr μ ν f hf
  change (∫ U, f (F U) ∂μ) = _
  rw [he, integral_add hi₁ hi₂]
  congr 1
  simpa only [probReal_univ, one_smul] using
    integral_fun_snd (μ := μ) (ν := ν) (fun V => restrictedProjectorLogPartition S hS T c u (q V).1)

end InvariantIsing

end

end OAI
