import OAI.Analysis.CircleDomains.Sobolev.TensorEnergy

namespace OAI

/-!
# Selecting the finite-transfer regularization

For a finite list of planar differentials, a small integral of absolute
pairwise wedges produces a regularized metric with small total energy.
This proves the energy optimization step of finite transfer, after the
geometric filling and staircase construction have supplied the differentials.
-/

open Filter MeasureTheory Finset
open scoped Topology

noncomputable section

namespace CircleDomainRigidity.FiniteTransfer

/-- Each unordered pair is counted exactly once. -/
def covectorWedges (x y : ℕ → ℝ) (n : ℕ) : ℝ :=
  ∑ j ∈ range n, ∑ i ∈ range j, |x i * y j - x j * y i|

/-- The exact finite-transfer energy choice, using the actually constructed
finite family of coordinate differentials. -/
theorem exists_regularization_energy_lt
    {X : Type*} [MeasurableSpace X] {μ : Measure X}
    (x y : ℕ → X → ℝ) (n : ℕ)
    (hx : ∀ i, Measurable (x i)) (hy : ∀ i, Measurable (y i))
    (htrace : Integrable (fun z => covectorTrace (fun i => x i z) (fun i => y i z) n) μ)
    (hwedge : Integrable (fun z => covectorWedges (fun i => x i z) (fun i => y i z) n) μ)
    {ε : ℝ} (hε : (∫ z, 2 * covectorWedges (fun i => x i z) (fun i => y i z) n ∂μ) < ε) :
    ∃ τ : ℝ, 0 < τ ∧
      (∫ z, tensorEnergy
        (covectorTrace (fun i => x i z) (fun i => y i z) n)
        (covectorDet (fun i => x i z) (fun i => y i z) n) τ ∂μ) < ε := by
  let T : X → ℝ := fun z => covectorTrace (fun i => x i z) (fun i => y i z) n
  let D : X → ℝ := fun z => covectorDet (fun i => x i z) (fun i => y i z) n
  let W : X → ℝ := fun z => covectorWedges (fun i => x i z) (fun i => y i z) n
  have hT : Measurable T := by
    dsimp [T, covectorTrace]
    fun_prop
  have hD : Measurable D := by
    dsimp [D, covectorDet]
    fun_prop
  have hpoint (z : X) : 2 * Real.sqrt (D z) ≤ 2 * W z := by
    apply mul_le_mul_of_nonneg_left _ (by norm_num)
    exact sqrt_gramDet_le_wedges (fun i => x i z) (fun i => y i z) n
  have hi : Integrable (fun z => 2 * Real.sqrt (D z)) μ := by
    apply (hwedge.const_mul 2).mono'
      ((hD.sqrt.const_mul 2).aestronglyMeasurable)
    apply Filter.Eventually.of_forall
    intro z
    have hnonneg : 0 ≤ 2 * Real.sqrt (D z) := by positivity
    simpa only [Real.norm_eq_abs, abs_of_nonneg hnonneg] using hpoint z
  have hlimlt : (∫ z, 2 * Real.sqrt (D z) ∂μ) < ε :=
    (integral_mono hi (hwedge.const_mul 2) hpoint).trans_lt hε
  have hlim := tendsto_integral_tensorEnergy hT hD
    (fun z => covectorTrace_nonneg (fun i => x i z) (fun i => y i z) n)
    (fun z => covectorDet_nonneg (fun i => x i z) (fun i => y i z) n)
    (fun z => covector_discriminant_nonneg (fun i => x i z) (fun i => y i z) n) htrace
  have hpos : ∀ᶠ τ : ℝ in 𝓝[>] 0, 0 < τ := self_mem_nhdsWithin
  exact (hpos.and (hlim.eventually (gt_mem_nhds hlimlt))).exists

end CircleDomainRigidity.FiniteTransfer

end

end OAI
