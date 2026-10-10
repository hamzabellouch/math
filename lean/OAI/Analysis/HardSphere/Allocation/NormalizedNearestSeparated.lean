import Mathlib

namespace OAI

noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology BigOperators
open scoped BigOperators ComplexConjugate
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
open MeasureTheory ProbabilityTheory Real Complex
open scoped ENNReal ComplexConjugate
open ProbabilityTheory
open MeasureTheory Filter Set
open scoped ENNReal Topology
open MeasureTheory Set
open scoped ENNReal
namespace HardSphere
open MeasureTheory Set Filter

lemma normalized_nearest_separated {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {x y : E} (hx : x≠0) (hy : y≠0) (hxy : ‖x‖≤‖x-y‖) (hyx : ‖y‖≤‖x-y‖) :
    1≤‖‖x‖⁻¹ • x-‖y‖⁻¹ • y‖ := by
  have aux {x y : E} (hx : x≠0) (hy : y≠0) (h : ‖y‖≤‖x‖) (hd : ‖x‖≤‖x-y‖) :
      1≤‖‖x‖⁻¹ • x-‖y‖⁻¹ • y‖ := by
    have hx0 : 0<‖x‖ := norm_pos_iff.mpr hx
    have hy0 : 0<‖y‖ := norm_pos_iff.mpr hy
    have he : x-y=‖y‖ • (‖x‖⁻¹ • x-‖y‖⁻¹ • y)+(‖x‖-‖y‖) • (‖x‖⁻¹ • x) := by
      rw [smul_sub,sub_smul,smul_smul,smul_smul,smul_smul,
        mul_inv_cancel₀ hy0.ne',mul_inv_cancel₀ hx0.ne',one_smul,one_smul]
      abel
    have ht := norm_add_le (‖y‖ • (‖x‖⁻¹ • x-‖y‖⁻¹ • y)) ((‖x‖-‖y‖) • (‖x‖⁻¹ • x))
    rw [←he,norm_smul,norm_smul,Real.norm_of_nonneg hy0.le,
      Real.norm_of_nonneg (sub_nonneg.mpr h)] at ht
    have hn : ‖‖x‖⁻¹ • x‖=1 := by
      rw [norm_smul,Real.norm_of_nonneg (inv_nonneg.mpr hx0.le),inv_mul_cancel₀ hx0.ne']
    rw [hn,mul_one] at ht
    nlinarith only [ht,hd,hy0]
  rcases le_total ‖y‖ ‖x‖ with h | h
  · exact aux hx hy h hxy
  · have hd : ‖y‖≤‖y-x‖ := by simpa only [norm_sub_rev] using hyx
    simpa only [norm_sub_rev] using aux hy hx h hd

lemma nearest_incoming_card {ι E : Type*} [DecidableEq ι] [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] (I : Finset ι) (v : ι→E)
    (h0 : ∀ i∈I, v i≠0)
    (hne : ∀ i∈I, ∀ j∈I, i≠j → ‖v i‖≤‖v i-v j‖) :
    I.card≤5^Module.finrank ℝ E := by
  classical
  let d : ι→E := fun i ↦ ‖v i‖⁻¹ • v i
  have hsep : ∀ i∈I, ∀ j∈I, i≠j → 1≤‖d i-d j‖ := by
    intro i hi j hj hij
    exact normalized_nearest_separated (h0 i hi) (h0 j hj) (hne i hi j hj hij)
      (by simpa only [norm_sub_rev] using hne j hj i hi hij.symm)
  have hinj : Set.InjOn d I := by
    intro i hi j hj hd
    by_contra hn
    have hh := hsep i hi j hj hn
    rw [hd,sub_self,norm_zero] at hh
    norm_num at hh
  rw [←Finset.card_image_of_injOn hinj]
  apply Besicovitch.card_le_of_separated
  · intro x hx
    obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hx
    dsimp [d]
    rw [norm_smul,Real.norm_of_nonneg (inv_nonneg.mpr (norm_nonneg _)),inv_mul_cancel₀ (norm_ne_zero_iff.mpr (h0 i hi))]
    norm_num
  · intro x hx y hy hxy
    obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp hy
    exact hsep i hi j hj (fun hij ↦ hxy (congrArg d hij))

end HardSphere

end

end OAI
