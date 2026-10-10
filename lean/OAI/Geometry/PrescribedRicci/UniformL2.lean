import Mathlib
import OAI.Geometry.PrescribedRicci.UniformSchwartz

namespace OAI

/-! Uniform L2. -/

section

 
noncomputable section
open Set MeasureTheory
open scoped ContDiff SchwartzMap ENNReal Classical
namespace SobolevChart
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] {Z : Type*}
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

def UniformL2 (F : Z → E → V) : Prop :=
  (∀ z, MemLp (F z) 2 volume) ∧ ∃ C : ℝ, 0 ≤ C ∧ ∀ z, lpNorm (F z) 2 volume ≤ C

lemma UniformSobolev.uniformL2 {F : Z → 𝓢(E,ℂ)} (hF : UniformSobolev 0 F) :
    UniformL2 (fun z => (F z : E → ℂ)) :=
  ⟨fun z => (F z).memLp _ _,(uniformSobolev_zero_iff F).mp hF⟩

omit [NormedSpace ℝ V] in
lemma UniformL2.norm {F : Z → E → V} (h : UniformL2 F) : UniformL2 (fun z x => ‖F z x‖) := by
  refine ⟨fun z => (h.1 z).norm,?_⟩
  obtain ⟨C,hC,hc⟩ := h.2
  exact ⟨C,hC,fun z => by rw [lpNorm_norm (h.1 z).aestronglyMeasurable]; exact hc z⟩

omit [NormedSpace ℝ V] in
lemma UniformL2.add {F G : Z → E → V} (hF : UniformL2 F) (hG : UniformL2 G) :
    UniformL2 (fun z x => F z x+G z x) := by
  obtain ⟨C,hC,hc⟩ := hF.2
  obtain ⟨B,hB,hb⟩ := hG.2
  refine ⟨fun z => (hF.1 z).add (hG.1 z),C+B,add_nonneg hC hB,fun z => ?_⟩
  exact (lpNorm_add_le (hF.1 z) (by norm_num)).trans (add_le_add (hc z) (hb z))

lemma UniformL2.smul {F : Z → E → V} (hF : UniformL2 F) (c : ℝ) :
    UniformL2 (fun z x => c • F z x) := by
  obtain ⟨C,hC,hc⟩ := hF.2
  refine ⟨fun z => (hF.1 z).const_smul c,‖c‖*C,mul_nonneg (norm_nonneg _) hC,fun z => ?_⟩
  change lpNorm (c • F z) 2 volume ≤ _
  rw [lpNorm_const_smul]
  exact mul_le_mul_of_nonneg_left (hc z) (norm_nonneg _)

omit [NormedSpace ℝ V] in
lemma UniformL2.zero : UniformL2 (fun _ : Z => (0 : E → V)) :=
  ⟨fun _ => MemLp.zero,0,le_rfl,fun _ => by simp⟩

omit [NormedSpace ℝ V] in
lemma UniformL2.sum {ι : Type*} (S : Finset ι) (F : ι → Z → E → V)
    (h : ∀ i ∈ S, UniformL2 (F i)) : UniformL2 (fun z x => ∑ i ∈ S, F i z x) := by
  induction S using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    exact UniformL2.zero
  | @insert a S ha ih =>
    simpa only [Finset.sum_insert ha] using
      (h a (Finset.mem_insert_self a S)).add (ih (fun i hi => h i (Finset.mem_insert_of_mem hi)))

lemma UniformSobolev.zero_of_majorant {F : Z → 𝓢(E,ℂ)} {G : Z → E → ℝ}
    (hG : UniformL2 G) (h : ∀ z x, ‖F z x‖ ≤ G z x) : UniformSobolev 0 F := by
  obtain ⟨C,hC,hc⟩ := hG.2
  apply (uniformSobolev_zero_iff F).mpr
  exact ⟨C,hC,fun z => (lpNorm_mono_real (hG.1 z) (h z)).trans (hc z)⟩
end SobolevChart

end
end

end OAI
