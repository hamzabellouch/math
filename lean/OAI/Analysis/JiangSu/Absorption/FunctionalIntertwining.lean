import Mathlib
import OAI.Analysis.TracialSplitting.PreparedBlocks
import OAI.Analysis.JiangSu.Model

namespace OAI


noncomputable section
open scoped NonUnitalContinuousFunctionalCalculus Topology
open ContinuousMapZero Filter

namespace TraceCone
variable {A : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

theorem cfc_intertwine (a b : Positive A) (x : A) (hx : x * a.1 = b.1 * x)
    (f : ℝ → ℝ) (hf : Continuous f) (hf0 : f 0 = 0) :
    x * cfcₙ f a.1 = cfcₙ f b.1 * x := by
  let s := quasispectrum ℝ a.1 ∪ quasispectrum ℝ b.1
  have : CompactSpace s := isCompact_iff_compactSpace.mp
    ((NonUnitalContinuousFunctionalCalculus.isCompact_quasispectrum a.1).union (NonUnitalContinuousFunctionalCalculus.isCompact_quasispectrum b.1))
  have : Fact (0 ∈ s) := ⟨Or.inl (quasispectrum.zero_mem ℝ a.1)⟩
  have has : quasispectrum ℝ a.1 ⊆ s := Set.subset_union_left
  have hbs : quasispectrum ℝ b.1 ⊆ s := Set.subset_union_right
  have ha := IsSelfAdjoint.of_nonneg a.2
  have hb := IsSelfAdjoint.of_nonneg b.2
  let F := cfcₙHomSuperset ha has
  let G := cfcₙHomSuperset hb hbs
  have hF : Continuous F := cfcₙHomSuperset_continuous ha has
  have hG : Continuous G := cfcₙHomSuperset_continuous hb hbs
  have key (g : C(s, ℝ)₀) : x * F g = G g * x := by
    induction g using ContinuousMapZero.induction_on_of_compact with
    | zero => simp
    | smul r g hg =>
      rw [map_smul, map_smul, mul_smul_comm, smul_mul_assoc, hg]
    | id => simpa only [F, G, cfcₙHomSuperset_id] using hx
    | star_id => simpa only [star_trivial, F, G, cfcₙHomSuperset_id] using hx
    | add g h hg hh => simp only [map_add, mul_add, add_mul, hg, hh]
    | mul g h hg hh =>
      rw [map_mul, map_mul, ← mul_assoc, hg, mul_assoc, hh, ← mul_assoc]
    | frequently g hg =>
      have hc : IsClosed {g : C(s, ℝ)₀ | x * F g = G g * x} :=
        isClosed_eq (continuous_const.mul hF) (hG.mul continuous_const)
      exact hc.mem_of_frequently_of_tendsto hg tendsto_id
  let g : C(s, ℝ)₀ := ⟨⟨fun t => f t.1, hf.comp continuous_subtype_val⟩, by change f 0 = 0; exact hf0⟩
  have h := key g
  have heq (c : Positive A) (hc : quasispectrum ℝ c.1 ⊆ s) :
      cfcₙHomSuperset (IsSelfAdjoint.of_nonneg c.2) hc g = cfcₙ f c.1 := by
    rw [cfcₙHomSuperset_apply, cfcₙHom_eq_cfcₙ_extend f]
    apply cfcₙ_congr
    intro t ht
    lift t to quasispectrum ℝ c.1 using ht
    simp only [Subtype.val_injective.extend_apply, comp_apply, coe_mk,
      ContinuousMap.coe_mk, g]
    rfl
  change x * cfcₙHomSuperset ha has g = cfcₙHomSuperset hb hbs g * x at h
  simpa only [heq a has, heq b hbs] using h

end TraceCone
end

end OAI
