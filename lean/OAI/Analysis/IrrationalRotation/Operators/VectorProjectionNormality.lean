import OAI.Analysis.IrrationalRotation.Model.OperatorProperties
import Mathlib.Analysis.InnerProductSpace.Projection.Submodule
import Mathlib.Topology.Order.OrderClosed

namespace OAI

noncomputable section
open Filter
open scoped Topology

namespace Invariant233

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

omit [CompleteSpace H] in
theorem vectorTrace_starProjection_re (ξ : H) (K : Submodule ℂ H)
    [K.HasOrthogonalProjection] :
    (vectorTrace ξ K.starProjection).re = ‖K.starProjection ξ‖ ^ 2 := by
  change (inner ℂ ξ (K.starProjection ξ)).re = _
  exact (inner_re_symm (𝕜 := ℂ) ξ (K.starProjection ξ)).trans
    (Submodule.re_inner_starProjection_eq_normSq K ξ)

omit [CompleteSpace H] in
theorem vectorTrace_starProjection_mono (ξ : H) {K L : Submodule ℂ H}
    [K.HasOrthogonalProjection] [L.HasOrthogonalProjection] (hKL : K ≤ L) :
    (vectorTrace ξ K.starProjection).re ≤ (vectorTrace ξ L.starProjection).re := by
  rw [vectorTrace_starProjection_re, vectorTrace_starProjection_re]
  have hproj : K.starProjection (L.starProjection ξ) = K.starProjection ξ :=
    congrArg (fun A : H →L[ℂ] H => A ξ)
      (Submodule.starProjection_comp_starProjection_of_le hKL)
  have hn : ‖K.starProjection ξ‖ ≤ ‖L.starProjection ξ‖ := by
    rw [← hproj]
    exact K.norm_starProjection_apply_le _
  exact pow_le_pow_left₀ (norm_nonneg _) hn 2

theorem tendsto_vectorTrace_starProjection_iSup
    {ι : Type*} [Preorder ι] (ξ : H) (K : ι → Submodule ℂ H)
    [∀ i, (K i).HasOrthogonalProjection] (hK : Monotone K) :
    Tendsto (fun i => vectorTrace ξ (K i).starProjection) atTop
      (𝓝 (vectorTrace ξ (⨆ i, K i).topologicalClosure.starProjection)) := by
  exact tendsto_const_nhds.inner (Submodule.starProjection_tendsto_closure_iSup K hK ξ)

theorem iSup_vectorTrace_starProjection
    {ι : Type*} [Preorder ι] [NeBot (atTop : Filter ι)]
    (ξ : H) (K : ι → Submodule ℂ H)
    [∀ i, (K i).HasOrthogonalProjection] (hK : Monotone K) :
    (⨆ i, (vectorTrace ξ (K i).starProjection).re) =
      (vectorTrace ξ (⨆ i, K i).topologicalClosure.starProjection).re := by
  apply iSup_eq_of_forall_le_of_tendsto (F := (atTop : Filter ι))
  · intro i
    exact vectorTrace_starProjection_mono ξ
      ((le_iSup K i).trans (Submodule.le_topologicalClosure _))
  · exact Complex.continuous_re.continuousAt.tendsto.comp
      (tendsto_vectorTrace_starProjection_iSup ξ K hK)

omit [CompleteSpace H] in
theorem tendsto_vectorTrace_starProjection_exhaustion
    {ι : Type*} [Preorder ι] (ξ : H) (K : ι → Submodule ℂ H)
    [∀ i, (K i).HasOrthogonalProjection] (hK : Monotone K)
    (hdense : (⨆ i, K i).topologicalClosure = ⊤) :
    Tendsto (fun i => vectorTrace ξ (K i).starProjection) atTop
      (𝓝 ((‖ξ‖ ^ 2 : ℝ) : ℂ)) := by
  have h : Tendsto (fun i => inner ℂ ξ ((K i).starProjection ξ)) atTop
      (𝓝 (inner ℂ ξ ξ)) := tendsto_const_nhds.inner
    (Submodule.starProjection_tendsto_self K hK ξ (by rw [hdense]))
  simpa [vectorTrace, inner_self_eq_norm_sq_to_K] using h

omit [CompleteSpace H] in
theorem tendsto_vectorTrace_starProjection_exhaustion_one
    {ι : Type*} [Preorder ι] (ξ : H) (hξ : ‖ξ‖ = 1)
    (K : ι → Submodule ℂ H) [∀ i, (K i).HasOrthogonalProjection]
    (hK : Monotone K) (hdense : (⨆ i, K i).topologicalClosure = ⊤) :
    Tendsto (fun i => (vectorTrace ξ (K i).starProjection).re) atTop (𝓝 1) := by
  have h := Complex.continuous_re.continuousAt.tendsto.comp
    (tendsto_vectorTrace_starProjection_exhaustion ξ K hK hdense)
  simpa only [Function.comp_def, hξ, one_pow, Complex.ofReal_one, Complex.one_re] using h

theorem starProjection_closure_iSup_mem (M : VonNeumannAlgebra H)
    {ι : Type*} (K : ι → Submodule ℂ H)
    [∀ i, (K i).HasOrthogonalProjection]
    (hmem : ∀ i, (K i).starProjection ∈ M) :
    (⨆ i, K i).topologicalClosure.starProjection ∈ M := by
  apply (VonNeumannAlgebra.IsStarProjection.mem_iff
    isStarProjection_starProjection M).2
  intro y hy
  rw [Submodule.range_starProjection]
  apply Submodule.topologicalClosure_mem_invtSubmodule
  rw [Module.End.mem_invtSubmodule_iff_map_le, Submodule.map_iSup]
  apply iSup_le
  intro i
  have hi := (VonNeumannAlgebra.IsStarProjection.mem_iff
    isStarProjection_starProjection M).1 (hmem i) y hy
  rw [Submodule.range_starProjection, Module.End.mem_invtSubmodule_iff_map_le] at hi
  exact hi.trans (le_iSup K i)

theorem vectorTrace_projection_normality (M : VonNeumannAlgebra H)
    {ι : Type*} [Preorder ι] [NeBot (atTop : Filter ι)]
    (ξ : H) (K : ι → Submodule ℂ H)
    [∀ i, (K i).HasOrthogonalProjection] (hK : Monotone K)
    (hmem : ∀ i, (K i).starProjection ∈ M) :
    (⨆ i, K i).topologicalClosure.starProjection ∈ M ∧
      (⨆ i, (vectorTrace ξ (K i).starProjection).re) =
        (vectorTrace ξ (⨆ i, K i).topologicalClosure.starProjection).re :=
  ⟨starProjection_closure_iSup_mem M K hmem,
    iSup_vectorTrace_starProjection ξ K hK⟩

end Invariant233

end

end OAI
