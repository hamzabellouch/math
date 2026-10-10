import Mathlib
import OAI.Analysis.Commutator.BicommutantOrbit
import OAI.Analysis.Commutator.FreeBlockTensor3
import OAI.Analysis.Commutator.FreeMoments

namespace OAI

noncomputable section
open scoped ComplexOrder InnerProductSpace
open Complex ContinuousLinearMap UniformSpace Completion
open scoped InnerProductSpace
open scoped TensorProduct
open scoped TensorProduct InnerProductSpace Topology
open UniformSpace Completion Filter
open scoped TensorProduct
open UniformSpace Completion
open scoped Matrix.Norms.L2Operator MatrixOrder ComplexOrder
open scoped InnerProductSpace TensorProduct ComplexOrder
open UniformSpace
open scoped InnerProductSpace _root_.Topology

namespace Kadison.FreeBlocks

open FreeMoments FreeWordTensor FreeCreation UniformSpace

open scoped InnerProductSpace TensorProduct

variable {A : Type} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

variable (t : FaithfulState A) {ι : Type*} (S : ι → StarSubalgebra ℂ A)

variable (hfree : Free S t.functional.toLinearMap) {i j : ι} (hij : i≠j)

variable (hcolors : ∀ c : ι, c=i ∨ c=j)

include hcolors

lemma wordVector_mem_levels (w : List (Letter t S)) (hw : Reduced w) :
    wordVector t S w ∈ ⨆ n, LinearMap.range (levelEmbedding t S hfree hij n).toLinearMap := by
  obtain ⟨n,x,hx⟩ := word_as_endpoint t S hcolors w hw
  apply Submodule.mem_iSup_of_mem n
  refine ⟨(x : Completion (endpointTensor t S i j n)), ?_⟩
  rw [LinearIsometry.coe_toLinearMap, levelEmbedding_coe]
  exact congrArg (fun x : preSpace t => (x : t.functional.GNS)) hx.symm

lemma generated_mem_levels {a : A} (ha : a ∈ iSup S) :
    (t.functional.toPreGNS a : t.functional.GNS) ∈
      ⨆ n, LinearMap.range (levelEmbedding t S hfree hij n).toLinearMap := by
  have ha' : a ∈ FreeMoments.wordSpan S t.functional.toLinearMap := by
    change a ∈ (FreeMoments.reducedAlgebra S (fun a => map_star t.functional a) t.normalized)
    rw [FreeMoments.reducedAlgebra_eq_iSup]
    exact ha
  clear ha
  induction ha' using Submodule.span_induction with
  | mem a ha => obtain ⟨w,hw,rfl⟩ := ha; exact wordVector_mem_levels t S hfree hij hcolors w hw
  | zero => simp only [map_zero, Completion.coe_zero, Submodule.zero_mem]
  | add a b _ _ ha hb => simpa only [map_add, Completion.coe_add] using
      (⨆ n, LinearMap.range (levelEmbedding t S hfree hij n).toLinearMap).add_mem ha hb
  | smul c a _ ha => simpa only [map_smul, Completion.coe_smul] using
      (⨆ n, LinearMap.range (levelEmbedding t S hfree hij n).toLinearMap).smul_mem c ha

lemma total_levels
    (hgen : ∀ a : A, t.functional.gnsStarAlgHom a ∈
      Set.centralizer (Set.centralizer (generatedOperators t S : Set _))) :
    (⨆ n, LinearMap.range (levelEmbedding t S hfree hij n).toLinearMap).topologicalClosure=⊤ := by
  apply Submodule.eq_top_iff'.mpr
  intro x
  induction x using Completion.induction_on with
  | hp => exact (⨆ n, LinearMap.range
      (levelEmbedding t S hfree hij n).toLinearMap).isClosed_topologicalClosure
  | ih x =>
    let ξ : t.functional.GNS := (t.functional.toPreGNS 1 : t.functional.GNS)
    have h := Kadison.bicommutant_mem_cyclicSubspace (generatedOperators t S)
      (hgen (t.functional.ofPreGNS x)) ξ
    have heq : t.functional.gnsStarAlgHom (t.functional.ofPreGNS x) ξ =
        (x : t.functional.GNS) := by
      simp [ξ, PositiveLinearMap.gnsStarAlgHom]
    rw [heq] at h
    apply Submodule.topologicalClosure_mono ?_ h
    rintro y ⟨a,ha,rfl⟩
    obtain ⟨b,hb,rfl⟩ := ha
    simpa [ξ, PositiveLinearMap.gnsStarAlgHom] using generated_mem_levels t S hfree hij hcolors hb

end Kadison.FreeBlocks
end

end OAI
