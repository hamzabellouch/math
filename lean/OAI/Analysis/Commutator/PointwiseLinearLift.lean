import Mathlib
import OAI.Analysis.Commutator.RationalDense

namespace OAI

noncomputable section

section

noncomputable section

open MeasureTheory Filter

open scoped Topology InnerProductSpace

namespace Kadison.PointwiseLift

variable {Ω H : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [TopologicalSpace.SeparableSpace H]

local instance : NormedSpace ℚ H := NormedSpace.restrictScalars ℚ ℂ H

variable (A : H →L[ℂ] Lp H 2 μ) (b : ℝ)

def Good (a : Ω) : Prop :=
  (∀ x y : RationalDense.subspace H,A ((x+y:H)) a=A (x:H) a+A (y:H) a) ∧
  (∀ (r : ℚ) (x : RationalDense.subspace H),A (r • (x:H)) a=r • A (x:H) a) ∧
  (∀ x : RationalDense.subspace H,‖A (x:H) a‖≤b*‖(x:H)‖)

omit [CompleteSpace H] in
lemma good_ae (hbound : ∀ x : H,∀ᵐ a ∂μ,‖A x a‖≤b*‖x‖) : ∀ᵐ a ∂μ,Good μ A b a := by
  have ha (x y : RationalDense.subspace H) :
      ∀ᵐ a ∂μ,A ((x+y:H)) a=A (x:H) a+A (y:H) a := by
    rw [map_add]
    exact Lp.coeFn_add _ _
  have hs (r : ℚ) (x : RationalDense.subspace H) :
      ∀ᵐ a ∂μ,A (r • (x:H)) a=r • A (x:H) a := by
    rw [map_rat_smul]
    exact Lp.coeFn_smul _ _
  filter_upwards [ae_all_iff.mpr (fun x => ae_all_iff.mpr (ha x)),
    ae_all_iff.mpr (fun r => ae_all_iff.mpr (hs r)),
    ae_all_iff.mpr (fun x : RationalDense.subspace H => hbound (x:H))] with a ha hs hn
  exact ⟨ha,hs,hn⟩

def raw (a : Ω) (ha : Good μ A b a) : RationalDense.subspace H →L[ℚ] H :=
  ({toFun := fun x => A (x:H) a
    map_add' := ha.1
    map_smul' := ha.2.1} : RationalDense.subspace H →ₗ[ℚ] H).mkContinuous b ha.2.2

def rationalField (a : Ω) : H →L[ℚ] H := by
  classical
  exact if ha : Good μ A b a then (raw μ A b a ha).extend (RationalDense.subspace H).subtypeL else 0

lemma rationalField_subtype (a : Ω) (ha : Good μ A b a) (x : RationalDense.subspace H) :
    rationalField μ A b a (x:H)=A (x:H) a := by
  rw [rationalField,dite_eq_left ha]
  exact ContinuousLinearMap.extend_eq _ (RationalDense.dense H)
    isUniformEmbedding_subtype_val.isUniformInducing x

lemma rationalField_norm_le (hb : 0≤b) (a : Ω) : ‖rationalField μ A b a‖≤b := by
  by_cases ha : Good μ A b a
  · apply ContinuousLinearMap.opNorm_le_bound _ hb
    intro x
    exact (RationalDense.dense H).induction_on x
      (isClosed_le (rationalField μ A b a).continuous.norm (continuous_const.mul continuous_norm))
      (fun y => by
        change ‖rationalField μ A b a (y:H)‖≤b*‖(y:H)‖
        rw [rationalField_subtype μ A b a ha y]
        exact ha.2.2 y)
  · simp [rationalField,ha,hb]

lemma rationalField_ae (hb : 0≤b)
    (hbound : ∀ x : H,∀ᵐ a ∂μ,‖A x a‖≤b*‖x‖) (x : H) :
    (fun a => rationalField μ A b a x)=ᵐ[μ] A x := by
  obtain ⟨f,hf⟩ := RationalDense.exists_seq H x
  have hA : Tendsto (fun n => A (f n:H)) atTop (𝓝 (A x)) := A.continuous.tendsto x |>.comp hf
  obtain ⟨k,hk,hka⟩ := (tendstoInMeasure_of_tendsto_Lp hA).exists_seq_tendsto_ae
  filter_upwards [good_ae μ A b hbound,hka] with a ha hka
  have hcont := (ContinuousLinearMap.lipschitzWith_of_opNorm_le (K := ⟨b,hb⟩)
    (rationalField_norm_le μ A b hb a)).continuous
  have hf' := hcont.tendsto x |>.comp (hf.comp hk.tendsto_atTop)
  have he : (fun n => rationalField μ A b a (f (k n):H))=(fun n => A (f (k n):H) a) :=
    funext (fun n => rationalField_subtype μ A b a ha (f (k n)))
  change Tendsto (fun n => rationalField μ A b a (f (k n):H)) atTop
    (𝓝 (rationalField μ A b a x)) at hf'
  rw [he] at hf'
  exact tendsto_nhds_unique hf' hka

lemma rationalField_measurable (hb : 0≤b)
    (hbound : ∀ x : H,∀ᵐ a ∂μ,‖A x a‖≤b*‖x‖) (x : H) :
    AEStronglyMeasurable (fun a => rationalField μ A b a x) μ :=
  (Lp.aestronglyMeasurable (A x)).congr (rationalField_ae μ A b hb hbound x).symm

def realField (a : Ω) : H →L[ℝ] H :=
  (rationalField μ A b a).toLinearMap.toAddMonoidHom.toRealLinearMap (rationalField μ A b a).continuous

lemma realField_norm_le (hb : 0≤b) (a : Ω) : ‖realField μ A b a‖≤b := by
  apply ContinuousLinearMap.opNorm_le_bound _ hb
  intro x
  exact ((rationalField μ A b a).le_opNorm x).trans
    (mul_le_mul_of_nonneg_right (rationalField_norm_le μ A b hb a) (norm_nonneg x))

def field (a : Ω) : H →L[ℂ] H := ComplexLinearization.operator (realField μ A b a)

lemma field_norm_le (hb : 0≤b) (a : Ω) : ‖field μ A b a‖≤b :=
  (ComplexLinearization.norm_le _).trans (realField_norm_le μ A b hb a)

lemma field_ae (hb : 0≤b) (hbound : ∀ x : H,∀ᵐ a ∂μ,‖A x a‖≤b*‖x‖) (x : H) :
    (fun a => field μ A b a x)=ᵐ[μ] A x := by
  have hs : A (Complex.I • x)=Complex.I • A x := map_smul A _ _
  filter_upwards [rationalField_ae μ A b hb hbound x,
    rationalField_ae μ A b hb hbound (Complex.I • x),Lp.coeFn_smul Complex.I (A x)] with a hx hi hs'
  change (1/2:ℝ) • (rationalField μ A b a x-Complex.I • rationalField μ A b a (Complex.I • x))=_
  rw [hx,hi,hs,hs']
  dsimp only [Pi.smul_apply]
  simp only [smul_smul,Complex.I_mul_I,neg_one_smul,sub_neg_eq_add,smul_add]
  module

lemma field_measurable (hb : 0≤b)
    (hbound : ∀ x : H,∀ᵐ a ∂μ,‖A x a‖≤b*‖x‖) (x : H) :
    AEStronglyMeasurable (fun a => field μ A b a x) μ :=
  (Lp.aestronglyMeasurable (A x)).congr (field_ae μ A b hb hbound x).symm

end Kadison.PointwiseLift

end

end
end

end OAI
