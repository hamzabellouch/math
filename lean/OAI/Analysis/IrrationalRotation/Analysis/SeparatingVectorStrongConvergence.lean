import OAI.Analysis.IrrationalRotation.Operators.StrongOperatorConvergence
import OAI.Analysis.IrrationalRotation.Operators.TracialVectorSeparating

namespace OAI

noncomputable section
open Filter
open scoped Topology

namespace Invariant233

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

theorem commutant_cyclic_span_of_separating (M : VonNeumannAlgebra H) (ξ : H)
    (hsep : ∀ A : H →L[ℂ] H, A ∈ M → A ξ = 0 → A = 0) :
    (Submodule.span ℂ (Set.range (fun B : M.commutant =>
      (B : H →L[ℂ] H) ξ))).topologicalClosure = ⊤ := by
  let S := Submodule.span ℂ (Set.range (fun B : M.commutant =>
    (B : H →L[ℂ] H) ξ))
  let K := S.topologicalClosure
  have hinv (B : H →L[ℂ] H) (hB : B ∈ M.commutant) :
      S ∈ Module.End.invtSubmodule B := by
    intro x hx
    change B x ∈ S
    induction hx using Submodule.span_induction with
    | mem x hx =>
        obtain ⟨C, rfl⟩ := hx
        exact Submodule.subset_span ⟨⟨B * C, mul_mem hB C.property⟩, rfl⟩
    | zero => simpa only [map_zero] using S.zero_mem
    | add x y hx hy ihx ihy => simpa only [map_add] using S.add_mem ihx ihy
    | smul c x hx ih => simpa only [map_smul] using S.smul_mem c ih
  have hp : K.starProjection ∈ M := by
    apply (VonNeumannAlgebra.IsStarProjection.mem_iff
      (isStarProjection_starProjection (U := K)) M).mpr
    intro B hB
    rw [Submodule.range_starProjection]
    exact Submodule.topologicalClosure_mem_invtSubmodule (hinv B hB)
  have hξ : ξ ∈ K := by
    apply S.le_topologicalClosure
    exact Submodule.subset_span ⟨1, by simp⟩
  have hpξ : K.starProjection ξ = ξ := K.starProjection_eq_self_iff.mpr hξ
  have hzero : (1 - K.starProjection : H →L[ℂ] H) = 0 := by
    apply hsep _ (sub_mem (one_mem M) hp)
    change ξ - K.starProjection ξ = 0
    rw [hpξ, sub_self]
  have hpone : K.starProjection = 1 := (sub_eq_zero.mp hzero).symm
  apply top_unique
  intro x hx
  have hmem := K.starProjection_apply_mem x
  simpa only [hpone, one_apply_eq_self] using hmem

theorem strong_tendsto_of_commutant_cyclic_of_bounded
    {ι : Type*} {l : Filter ι} (M : VonNeumannAlgebra H) (ξ : H)
    (hcyclic : (Submodule.span ℂ (Set.range (fun B : M.commutant =>
      (B : H →L[ℂ] H) ξ))).topologicalClosure = ⊤)
    {A : ι → H →L[ℂ] H} {A₀ : H →L[ℂ] H} {C : ℝ}
    (hA : ∀ i, A i ∈ M) (hA₀ : A₀ ∈ M)
    (hξ : Tendsto (fun i => A i ξ) l (𝓝 (A₀ ξ)))
    (hC : ∀ᶠ i in l, ‖A i‖ ≤ C) (v : H) :
    Tendsto (fun i => A i v) l (𝓝 (A₀ v)) := by
  apply strong_tendsto_of_dense_span_of_bounded
    (Submodule.dense_iff_topologicalClosure_eq_top.mpr hcyclic) ?_ hC v
  intro B
  have hcomm (i : ι) : A i ((B : H →L[ℂ] H) ξ) = (B : H →L[ℂ] H) (A i ξ) :=
    congrArg (fun T : H →L[ℂ] H => T ξ)
      ((VonNeumannAlgebra.mem_commutant_iff.mp B.property) (A i) (hA i))
  have hcomm₀ : A₀ ((B : H →L[ℂ] H) ξ) = (B : H →L[ℂ] H) (A₀ ξ) :=
    congrArg (fun T : H →L[ℂ] H => T ξ)
      ((VonNeumannAlgebra.mem_commutant_iff.mp B.property) A₀ hA₀)
  simp only [hcomm, hcomm₀]
  exact B.val.continuous.continuousAt.tendsto.comp hξ

theorem strong_tendsto_of_separating_of_bounded
    {ι : Type*} {l : Filter ι} (M : VonNeumannAlgebra H) (ξ : H)
    (hsep : ∀ A : H →L[ℂ] H, A ∈ M → A ξ = 0 → A = 0)
    {A : ι → H →L[ℂ] H} {A₀ : H →L[ℂ] H} {C : ℝ}
    (hA : ∀ i, A i ∈ M) (hA₀ : A₀ ∈ M)
    (hξ : Tendsto (fun i => A i ξ) l (𝓝 (A₀ ξ)))
    (hC : ∀ᶠ i in l, ‖A i‖ ≤ C) (v : H) :
    Tendsto (fun i => A i v) l (𝓝 (A₀ v)) :=
  strong_tendsto_of_commutant_cyclic_of_bounded M ξ
    (commutant_cyclic_span_of_separating M ξ hsep) hA hA₀ hξ hC v

theorem IsFaithfulTracialVector.strong_tendsto_of_bounded
    {ι : Type*} {l : Filter ι} {M : VonNeumannAlgebra H} {ξ : H}
    (htrace : IsFaithfulTracialVector M ξ)
    {A : ι → H →L[ℂ] H} {A₀ : H →L[ℂ] H} {C : ℝ}
    (hA : ∀ i, A i ∈ M) (hA₀ : A₀ ∈ M)
    (hξ : Tendsto (fun i => A i ξ) l (𝓝 (A₀ ξ)))
    (hC : ∀ᶠ i in l, ‖A i‖ ≤ C) (v : H) :
    Tendsto (fun i => A i v) l (𝓝 (A₀ v)) :=
  strong_tendsto_of_separating_of_bounded M ξ
    (fun _ hA hz => htrace.eq_zero_of_apply_eq_zero hA hz) hA hA₀ hξ hC v

end Invariant233

end

end OAI
