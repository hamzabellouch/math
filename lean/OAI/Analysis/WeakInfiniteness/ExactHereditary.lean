import Mathlib
import OAI.Analysis.WeakInfiniteness.TensorIdealCut
import OAI.Analysis.WeakInfiniteness.TensorInjectivity

namespace OAI

noncomputable section
open scoped TensorProduct ENNReal ComplexOrder
open UniformSpace
open CStarAlgebra
open scoped NNReal
open scoped TensorProduct ComplexConjugate
open scoped ENNReal InnerProductSpace
open scoped InnerProductSpace
open scoped TensorProduct InnerProductSpace
open Filter Topology

namespace WeakPureInfiniteness

universe u v

section IdealCharacterization

variable {A : Type u} {C D : Type v} [CStarAlgebra A]
  [NonUnitalCStarAlgebra C] [NonUnitalCStarAlgebra D]

lemma tensor_mul_kernel_element_mem (q : C →⋆ₙₐ[ℂ] D) (e : C) (he : q e = 0)
    (x : MinimalTensor A C) :
    (x * rightElementaryHom e).val ∈ tensorKernelIdeal (A := A) q := by
  have hs : ∀ z ∈ Submodule.span ℂ
      (Set.range fun p : A × C => spatialElementary p.1 p.2),
      z * spatialElementary (1 : A) e ∈ tensorKernelIdeal (A := A) q := by
    intro z hz
    induction hz using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨⟨a,c⟩,rfl⟩ := hz
      rw [← spatialElementary_mul, mul_one]
      apply NonUnitalStarSubalgebra.le_topologicalClosure
      apply NonUnitalStarAlgebra.subset_adjoin ℂ
      exact ⟨a,c*e,by rw [map_mul,he,mul_zero],rfl⟩
    | zero =>
      rw [zero_mul]
      exact (tensorKernelIdeal (A := A) q).zero_mem
    | add z w _ _ hz hw =>
      rw [add_mul]
      exact (tensorKernelIdeal (A := A) q).add_mem hz hw
    | smul c z _ hz =>
      rw [smul_mul_assoc]
      exact (tensorKernelIdeal (A := A) q).smul_mem c hz
  have hc : IsClosed {z : SpatialAmbient A C |
      z * spatialElementary (1 : A) e ∈ tensorKernelIdeal (A := A) q} :=
    isClosed_closure.preimage (continuous_id.mul continuous_const)
  have hx := x.property
  change x.val ∈ (minimalTensorSubalgebra A C : Set (SpatialAmbient A C)) at hx
  rw [minimalTensor_eq_closure_span] at hx
  exact (closure_minimal hs hc) hx

lemma tensor_mem_ideal_of_cuts {ι : Type*} (l : Filter ι) [l.NeBot]
    (e : ι → C) (q : C →⋆ₙₐ[ℂ] D) (he : ∀ i, q (e i) = 0)
    (x : MinimalTensor A C)
    (hx : Tendsto (fun i => tensorCut (e i) x) l (𝓝 0)) :
    x.val ∈ tensorKernelIdeal (A := A) q := by
  have hmul : Tendsto (fun i => x * rightElementaryHom (e i)) l (𝓝 x) := by
    have h := (tendsto_const_nhds : Tendsto (fun _ : ι => x) l (𝓝 x)).sub hx
    simpa only [tensorCut, sub_sub_cancel, sub_zero] using h
  apply isClosed_closure.mem_of_tendsto (continuous_subtype_val.tendsto x |>.comp hmul)
  exact Filter.Eventually.of_forall (fun i => tensor_mul_kernel_element_mem q (e i) (he i) x)

end IdealCharacterization

section Heredity

variable {A B : Type u} [CStarAlgebra A] [CStarAlgebra B]

lemma minimalMapLeft_tensorCut {C : Type v} [NonUnitalCStarAlgebra C]
    (φ : A →⋆ₐ[ℂ] B) (e : C) (x : MinimalTensor A C) :
    minimalMapLeft φ.toNonUnitalStarAlgHom (tensorCut e x) =
      tensorCut e (minimalMapLeft φ.toNonUnitalStarAlgHom x) := by
  simp only [tensorCut, map_sub, map_mul]
  congr 2
  change minimalMapLeft φ.toNonUnitalStarAlgHom (minimalElementary (1 : A) e) =
    minimalElementary (1 : B) e
  rw [minimalMapLeft_elementary]
  change minimalElementary (φ 1) e = _
  rw [map_one]

theorem exact_of_injective_unital
    (φ : A →⋆ₐ[ℂ] B) (hφ : Function.Injective φ)
    (K : ComplexHilbert.{u}) (ψ : B →⋆ₙₐ[ℂ] (K →L[ℂ] K))
    (hψ : Function.Injective ψ) (hB : Exact B) : Exact A := by
  intro C D _ _ q hq z hz
  let := CStarAlgebra.spectralOrder C
  let := CStarAlgebra.spectralOrderedRing C
  let I := kernelAlgebra q
  let := CStarAlgebra.spectralOrder I
  let := CStarAlgebra.spectralOrderedRing I
  let l := CStarAlgebra.approximateUnit I
  have hl := CStarAlgebra.increasingApproximateUnit I
  let : l.NeBot := hl.toIsApproximateUnit.neBot
  let e : I → C := Subtype.val
  have he : ∀ᶠ i in l, 0 ≤ e i ∧ ‖e i‖ ≤ 1 := by
    filter_upwards [hl.eventually_nonneg, hl.eventually_norm] with i hi hn
    refine ⟨?_, hn⟩
    obtain ⟨x, hx⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hi
    have hi' : e i = star (e x) * e x := congrArg Subtype.val hx
    rw [hi']
    exact star_mul_self_nonneg _
  have happ : ∀ c : C, q c = 0 → Tendsto (fun i => c * e i) l (𝓝 c) := by
    intro c hc
    let x : I := ⟨c,hc⟩
    exact continuous_subtype_val.tendsto x |>.comp (hl.tendsto_mul_left x)
  have hmem : (minimalMapLeft φ.toNonUnitalStarAlgHom z).val ∈
      tensorKernelIdeal (A := B) q := by
    apply hB C D q hq
    intro π
    exact hz (π.precompLeft φ.toNonUnitalStarAlgHom)
  have hcuts := tensorCut_tendsto_zero_on_ideal l e he q happ
    (minimalMapLeft φ.toNonUnitalStarAlgHom z) hmem
  have hcutz : Tendsto (fun i => tensorCut (e i) z) l (𝓝 0) := by
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    have hn := tendsto_zero_iff_norm_tendsto_zero.mp hcuts
    convert hn using 1
    funext i
    rw [← minimalMapLeft_tensorCut]
    exact (norm_minimalMapLeft φ.toNonUnitalStarAlgHom K ψ hφ hψ _).symm
  exact tensor_mem_ideal_of_cuts l e q (fun i => i.property) z hcutz

end Heredity

end WeakPureInfiniteness
end

end OAI
