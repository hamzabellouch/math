import Mathlib.Topology.UniformSpace.Ascoli
import Mathlib.Topology.UniformSpace.CompleteSeparated
import Mathlib.Topology.Sequences
import Mathlib.Analysis.Complex.Basic

namespace OAI

/-! The compact-open Ascoli extraction used for real height coordinates. -/
open Set Function Filter Topology
open scoped Topology UniformConvergence
noncomputable section
namespace CircleDomainRigidity

 theorem locally_uniform_height_subsequence (f : ℕ → C(ℂ, ℝ))
    (he : Equicontinuous (fun n z => f n z))
    (hb : ∀ z : ℂ, ∃ B : ℝ, ∀ n, |f n z| ≤ B) :
    ∃ (v : C(ℂ, ℝ)) (s : ℕ → ℕ), StrictMono s ∧
      TendstoLocallyUniformly (fun n z => f (s n) z) v atTop := by
  let S : Set C(ℂ, ℝ) := range f
  let chooseIndex : S → ℕ := fun g => Classical.choose g.property
  have hchoose (g : S) : f (chooseIndex g) = g := Classical.choose_spec g.property
  have hse : Equicontinuous (fun g : S => ((g : C(ℂ, ℝ)) : ℂ → ℝ)) := by
    have hh := he.comp chooseIndex
    convert hh using 1
    funext g z
    exact congrArg (fun a : C(ℂ, ℝ) => a z) (hchoose g).symm
  have hcover : ⋃₀ {K : Set ℂ | IsCompact K} = univ := by
    apply eq_univ_of_forall
    intro z
    exact mem_sUnion.mpr ⟨{z}, isCompact_singleton, mem_singleton z⟩
  let : T2Space (ℂ →ᵤ[{K : Set ℂ | IsCompact K}] ℝ) :=
    UniformOnFun.t2Space_of_covering hcover
  have hclosed : IsClosedEmbedding
      (UniformOnFun.ofFun {K : Set ℂ | IsCompact K} ∘
        (fun g : C(ℂ, ℝ) => (g : ℂ → ℝ))) :=
    ContinuousMap.isUniformEmbedding_toUniformOnFunIsCompact.isClosedEmbedding
  have hc : IsCompact (closure S) :=
    ArzelaAscoli.isCompact_closure_of_isClosedEmbedding (fun K hK => hK) hclosed
      (fun K _ => hse.equicontinuousOn K) (fun _ _ z _ => by
        obtain ⟨B, hB⟩ := hb z
        refine ⟨Icc (-B) B, isCompact_Icc, ?_⟩
        rintro g ⟨n, rfl⟩
        exact abs_le.mp (hB n))
  obtain ⟨v, _, s, hs, hv⟩ := hc.tendsto_subseq (fun n => subset_closure (mem_range_self n))
  refine ⟨v, s, hs, ?_⟩
  exact ContinuousMap.tendsto_iff_tendstoLocallyUniformly.mp hv

end CircleDomainRigidity

end

end OAI
