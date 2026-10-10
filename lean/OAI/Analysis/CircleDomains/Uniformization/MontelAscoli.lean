import OAI.Analysis.CircleDomains.Topology.MontelCutoffFamily
import Mathlib.Topology.UniformSpace.Ascoli
import Mathlib.Topology.UniformSpace.CompleteSeparated
import Mathlib.Topology.Sequences

namespace OAI

/-! Compact-open Ascoli extraction for the continuous cutoff family. -/
open Set Function Filter Topology
open scoped Topology UniformConvergence
noncomputable section
namespace CircleDomainRigidity

 theorem locally_uniform_complex_subsequence {U : Set ℂ} (hU : IsOpen U)
    (f : ℕ → C(U, ℂ)) (he : Equicontinuous (fun n z => f n z))
    (hb : ∀ z : U, ∃ B : ℝ, ∀ n, ‖f n z‖ ≤ B) :
    ∃ (v : C(U, ℂ)) (s : ℕ → ℕ), StrictMono s ∧
      TendstoLocallyUniformly (fun n z => f (s n) z) v atTop := by
  let : LocallyCompactSpace U := hU.locallyCompactSpace
  let S : Set C(U, ℂ) := range f
  let chooseIndex : S → ℕ := fun g => Classical.choose g.property
  have hchoose (g : S) : f (chooseIndex g) = g := Classical.choose_spec g.property
  have hse : Equicontinuous (fun g : S => ((g : C(U, ℂ)) : U → ℂ)) := by
    have hh := he.comp chooseIndex
    convert hh using 1
    funext g z
    exact congrArg (fun a : C(U, ℂ) => a z) (hchoose g).symm
  have hcover : ⋃₀ {K : Set U | IsCompact K} = univ := by
    apply eq_univ_of_forall
    intro z
    exact mem_sUnion.mpr ⟨{z},isCompact_singleton,mem_singleton z⟩
  let : T2Space (U →ᵤ[{K : Set U | IsCompact K}] ℂ) :=
    UniformOnFun.t2Space_of_covering hcover
  have hclosed : IsClosedEmbedding
      (UniformOnFun.ofFun {K : Set U | IsCompact K} ∘
        (fun g : C(U, ℂ) => (g : U → ℂ))) :=
    ContinuousMap.isUniformEmbedding_toUniformOnFunIsCompact.isClosedEmbedding
  have hc : IsCompact (closure S) :=
    ArzelaAscoli.isCompact_closure_of_isClosedEmbedding (fun K hK => hK) hclosed
      (fun K _ => hse.equicontinuousOn K) (fun _ _ z _ => by
        obtain ⟨B,hB⟩ := hb z
        refine ⟨Metric.closedBall 0 B,isCompact_closedBall _ _,?_⟩
        rintro g ⟨n,rfl⟩
        simpa only [Metric.mem_closedBall,dist_zero_right] using hB n)
  obtain ⟨v,_,s,hs,hv⟩ := hc.tendsto_subseq (fun n => subset_closure (mem_range_self n))
  exact ⟨v,s,hs,ContinuousMap.tendsto_iff_tendstoLocallyUniformly.mp hv⟩

end CircleDomainRigidity

end

end OAI
