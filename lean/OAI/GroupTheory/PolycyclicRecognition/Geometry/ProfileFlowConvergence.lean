import OAI.GroupTheory.PolycyclicRecognition.Analysis.ProfileCompactness
import Mathlib.Topology.UniformSpace.CompactConvergence

namespace OAI

/-! # Uniform evaluation of compact profile families along converging flows -/

noncomputable section

namespace PolycyclicRecognition

open Set Filter
open scoped Topology

variable {U V W : Type*} [TopologicalSpace U] [LocallyCompactSpace U]
  [TopologicalSpace V] [LocallyCompactSpace V] [PseudoMetricSpace W]

/-- Evaluate a profile and a coordinate map jointly on fixed profile and
parameter sets. -/
def profileAlongMap (S : Set C(V, W)) (K : Set U) (T : C(U, V)) : C(S × K, W) :=
  ⟨fun p => p.1.val (T p.2.val), continuous_eval.comp
    ((continuous_subtype_val.comp continuous_fst).prodMk
      (T.continuous.comp (continuous_subtype_val.comp continuous_snd)))⟩

/-- Compact-open continuity of joint profile evaluation. -/
theorem continuous_profileAlongMap (S : Set C(V, W)) (K : Set U) :
    Continuous (profileAlongMap (W := W) S K) := by
  apply ContinuousMap.continuous_of_continuous_uncurry
  change Continuous (fun p : C(U, V) × (S × K) => p.2.1.val (p.1 p.2.2.val))
  exact continuous_eval.comp
    ((continuous_subtype_val.comp continuous_snd.fst).prodMk
      (continuous_eval.comp (continuous_fst.prodMk
        (continuous_subtype_val.comp continuous_snd.snd))))

/-- Convergence of the coordinate maps is uniform after evaluating every
profile in one compact family at every parameter in one compact set. -/
theorem profileAlongMap_tendstoUniformly
    (S : Set C(V, W)) (hS : IsCompact S) (K : Set U) (hK : IsCompact K)
    {ι : Type*} {l : Filter ι} {T : ι → C(U, V)} {T₀ : C(U, V)}
    (hT : Tendsto T l (𝓝 T₀)) :
    TendstoUniformly (fun i (p : S × K) => p.1.val (T i p.2.val))
      (fun p : S × K => p.1.val (T₀ p.2.val)) l := by
  let : CompactSpace S := isCompact_iff_compactSpace.mp hS
  let : CompactSpace K := isCompact_iff_compactSpace.mp hK
  have hf : Tendsto (fun i => profileAlongMap (W := W) S K (T i)) l
      (𝓝 (profileAlongMap (W := W) S K T₀)) := by
    simpa only [Function.comp_def] using
      ((continuous_profileAlongMap (W := W) S K).tendsto T₀).comp hT
  have hu := (ContinuousMap.tendsto_iff_forall_isCompact_tendstoUniformlyOn.mp hf)
    Set.univ isCompact_univ
  exact tendstoUniformlyOn_univ.mp hu

end PolycyclicRecognition

end

end OAI
