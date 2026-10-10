import OAI.Geometry.RCD.Sobolev.DirichletPoisson

namespace OAI

/-! # Normal contractions in the genuine zero-boundary Sobolev space -/

open Set Filter MeasureTheory
open scoped Topology InnerProductSpace NNReal

noncomputable section

namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X]
  (μ : Measure X) (hQ : QuadraticCheegerEnergy μ)

/-- A scalar normal contraction decreases the full Sobolev norm. -/
theorem SobolevSpace.norm_compContraction_le {φ : ℝ → ℝ}
    (hφ : LipschitzWith 1 φ) (hφ0 : φ 0 = 0) (f : SobolevSpace μ hQ) :
    ‖SobolevSpace.compContraction μ hQ hφ hφ0 f‖ ≤ ‖f‖ := by
  have hL := hφ.norm_compLp_le hφ0 (SobolevSpace.toLp μ hQ f)
  simp only [NNReal.coe_one, one_mul] at hL
  have he := SobolevSpace.energy_compContraction_le μ hQ hφ hφ0 f
  have hn := SobolevSpace.norm_sq μ hQ (SobolevSpace.compContraction μ hQ hφ hφ0 f)
  have hf := SobolevSpace.norm_sq μ hQ f
  unfold SobolevSpace.normSq at hn hf
  rw [SobolevSpace.compContraction_toLp] at hn
  have hsq := (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr hL
  nlinarith [norm_nonneg f, norm_nonneg (SobolevSpace.compContraction μ hQ hφ hφ0 f)]

/-- Composition preserves the compactly supported Lipschitz core. -/
theorem SobolevSpace.compContraction_mem_dirichletCore {φ : ℝ → ℝ}
    (hφ : LipschitzWith 1 φ) (hφ0 : φ 0 = 0) (Ω : Set X)
    (f : SobolevSpace μ hQ) (hf : f ∈ SobolevSpace.dirichletCore μ hQ Ω) :
    SobolevSpace.compContraction μ hQ hφ hφ0 f ∈
      SobolevSpace.dirichletCore μ hQ Ω := by
  rcases hf with ⟨g, C, hg, hgc, hgs, hgf⟩
  refine ⟨φ ∘ g, C, ?_, hgc.comp_left hφ0,
    (tsupport_comp_subset hφ0 g).trans hgs, ?_⟩
  · simpa only [one_mul] using hφ.comp hg
  · exact (hφ.coeFn_compLp hφ0 (SobolevSpace.toLp μ hQ f)).trans
      (hgf.fun_comp φ)

/-- Bounded energy and strong `L²` convergence suffice to retain membership
in the closed Dirichlet subspace. -/
theorem SobolevSpace.mem_dirichlet_of_bounded_L2_limit (Ω : Set X)
    {fs : ℕ → SobolevSpace μ hQ} {f : SobolevSpace μ hQ} {C : ℝ}
    (hmem : ∀ i, fs i ∈ SobolevSpace.dirichlet μ hQ Ω)
    (hbound : ∀ i, ‖fs i‖ ≤ C)
    (hlim : Tendsto (fun i => SobolevSpace.toLp μ hQ (fs i)) atTop
      (𝓝 (SobolevSpace.toLp μ hQ f))) :
    f ∈ SobolevSpace.dirichlet μ hQ Ω := by
  let K := SobolevSpace.dirichlet μ hQ Ω
  change f ∈ K
  rw [← K.orthogonal_orthogonal]
  apply ((Kᗮ).mem_orthogonal' f).mpr
  intro v hv
  have ht := SobolevSpace.inner_tendsto_of_toLp_tendsto_bounded μ hQ hbound hlim v
  have hz : (fun i => inner ℝ (fs i) v) = fun _ => 0 := by
    funext i
    exact K.inner_right_of_mem_orthogonal (hmem i) hv
  rw [hz] at ht
  exact tendsto_nhds_unique ht tendsto_const_nhds

/-- The closed zero-boundary space is stable under every scalar normal
contraction. Strong continuity of composition in `H¹` is not assumed. -/
theorem SobolevSpace.compContraction_mem_dirichlet {φ : ℝ → ℝ}
    (hφ : LipschitzWith 1 φ) (hφ0 : φ 0 = 0) (Ω : Set X)
    (f : SobolevSpace μ hQ) (hf : f ∈ SobolevSpace.dirichlet μ hQ Ω) :
    SobolevSpace.compContraction μ hQ hφ hφ0 f ∈
      SobolevSpace.dirichlet μ hQ Ω := by
  obtain ⟨fs, hfs, hlim⟩ := mem_closure_iff_seq_limit.mp hf
  obtain ⟨C, hC⟩ := (Metric.isBounded_range_of_tendsto fs hlim).exists_norm_le
  apply SobolevSpace.mem_dirichlet_of_bounded_L2_limit μ hQ Ω
    (fs := fun i => SobolevSpace.compContraction μ hQ hφ hφ0 (fs i)) (C := C)
  · intro i
    exact (SobolevSpace.dirichletCore μ hQ Ω).le_topologicalClosure
      (SobolevSpace.compContraction_mem_dirichletCore μ hQ hφ hφ0 Ω (fs i) (hfs i))
  · intro i
    exact (SobolevSpace.norm_compContraction_le μ hQ hφ hφ0 (fs i)).trans
      (hC (fs i) (mem_range_self i))
  · exact (hφ.continuous_compLp hφ0).continuousAt.tendsto.comp
      ((SobolevSpace.toLpCLM μ hQ).continuous.continuousAt.tendsto.comp hlim)

end RegularPointCoordinates

end

end OAI
