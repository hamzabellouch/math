import Mathlib

namespace OAI

noncomputable section

section

noncomputable section

open Filter

open scoped Topology

namespace Kadison.RationalDense

variable (H : Type*) [NormedAddCommGroup H] [NormedSpace ℂ H]
  [TopologicalSpace.SeparableSpace H]

local instance : NormedSpace ℚ H := NormedSpace.restrictScalars ℚ ℂ H

def subspace : Submodule ℚ H := Submodule.span ℚ (Set.range (TopologicalSpace.denseSeq H))

instance : Countable (subspace H) := by unfold subspace; infer_instance

lemma dense : DenseRange ((subspace H).subtypeL : subspace H →L[ℚ] H) := by
  apply denseRange_subtype_val.mpr
  exact Dense.mono (Submodule.subset_span) (TopologicalSpace.denseRange_denseSeq H)

lemma exists_seq (x : H) : ∃ f : ℕ → subspace H,Tendsto (fun n => (f n:H)) atTop (𝓝 x) := by
  obtain ⟨f,hf,hl⟩ := mem_closure_iff_seq_limit.mp ((dense H) x)
  choose g hg using hf
  have he : (fun n => (g n:H))=f := funext hg
  exact ⟨g,by rw [he]; exact hl⟩

end Kadison.RationalDense

namespace Kadison.ComplexLinearization

variable {H : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H]

def part (U : H →L[ℝ] H) : H →L[ℝ] H :=
  (1/2:ℝ) • (U-(Complex.I • U).comp ((Complex.I • ContinuousLinearMap.id ℂ H).restrictScalars ℝ))

lemma part_apply (U : H →L[ℝ] H) (x : H) :
    part U x=(1/2:ℝ) • (U x-Complex.I • U (Complex.I • x)) := rfl

lemma part_map_I (U : H →L[ℝ] H) (x : H) : part U (Complex.I • x)=Complex.I • part U x := by
  simp only [part_apply,smul_sub,smul_comm (1/2:ℝ) Complex.I,smul_smul,Complex.I_mul_I,
    neg_one_smul,map_neg,smul_neg,sub_neg_eq_add]
  rw [smul_add,smul_comm (1/2:ℝ) Complex.I]
  abel

lemma complex_smul (V : H →L[ℝ] H) (hI : ∀ x,V (Complex.I • x)=Complex.I • V x)
    (z : ℂ) (x : H) : V (z • x)=z • V x := by
  rw [←Complex.re_add_im z,add_smul,map_add,add_smul,mul_smul,mul_smul]
  have hr (r : ℝ) (y : H) : V ((r:ℂ) • y)=(r:ℂ) • V y := by
    change V (r • y)=r • V y
    exact map_smul V r y
  rw [hr,hr,hI]

def operator (U : H →L[ℝ] H) : H →L[ℂ] H where
  toFun := part U
  map_add' := map_add _
  map_smul' := complex_smul (part U) (part_map_I U)
  cont := (part U).continuous

lemma operator_apply (U : H →L[ℝ] H) (x : H) :
    operator U x=(1/2:ℝ) • (U x-Complex.I • U (Complex.I • x)) := rfl

lemma norm_le (U : H →L[ℝ] H) : ‖operator U‖≤‖U‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg U)
  intro x
  rw [operator_apply,norm_smul,Real.norm_eq_abs,abs_of_nonneg (by norm_num : (0:ℝ)≤1/2)]
  have hi : ‖Complex.I • x‖=‖x‖ := by simp only [norm_smul,Complex.norm_I,one_mul]
  have h := norm_sub_le (U x) (Complex.I • U (Complex.I • x))
  simp only [norm_smul,Complex.norm_I,one_mul] at h
  have h1 := U.le_opNorm x
  have h2 := U.le_opNorm (Complex.I • x)
  rw [hi] at h2
  linarith

end Kadison.ComplexLinearization

end

end
end

end OAI
