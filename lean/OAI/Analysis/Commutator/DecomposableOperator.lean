import Mathlib

namespace OAI

noncomputable section

section

noncomputable section

open MeasureTheory Filter

open scoped Topology ComplexOrder InnerProductSpace

namespace Kadison.Decomposable

variable {Ω H : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
  [NormedAddCommGroup H] [InnerProductSpace ℂ H]

lemma measurable_apply_simple (T : Ω → H →L[ℂ] H)
    (hm : ∀ ξ : H,AEStronglyMeasurable (fun a => T a ξ) μ) (f : SimpleFunc Ω H) :
    AEStronglyMeasurable (fun a => T a (f a)) μ := by
  classical
  induction f with
  | const c => exact hm c
  | @pcw f g s hs hf hg =>
    convert AEStronglyMeasurable.piecewise hs hf.restrict hg.restrict using 1
    funext a
    change T a (if a∈s then f a else g a)=(if a∈s then T a (f a) else T a (g a))
    split_ifs <;> rfl

lemma measurable_apply (T : Ω → H →L[ℂ] H)
    (hm : ∀ ξ : H,AEStronglyMeasurable (fun a => T a ξ) μ)
    {f : Ω → H} (hf : AEStronglyMeasurable f μ) :
    AEStronglyMeasurable (fun a => T a (f a)) μ := by
  obtain ⟨s,hs⟩ := hf.stronglyMeasurable_mk
  apply aestronglyMeasurable_of_tendsto_ae atTop (fun n => measurable_apply_simple μ T hm (s n))
  filter_upwards [hf.ae_eq_mk] with a ha
  rw [ha]
  exact (T a).continuous.continuousAt.tendsto.comp (hs a)

lemma memLp_apply (T : Ω → H →L[ℂ] H)
    (hm : ∀ ξ : H,AEStronglyMeasurable (fun a => T a ξ) μ)
    {b : ℝ} (hb : ∀ᵐ a ∂μ,‖T a‖≤b) (f : Lp H 2 μ) :
    MemLp (fun a => T a (f a)) 2 μ := by
  apply (Lp.memLp f).of_le_mul (measurable_apply μ T hm (Lp.aestronglyMeasurable f))
  filter_upwards [hb] with a ha
  exact ((T a).le_opNorm (f a)).trans (mul_le_mul_of_nonneg_right ha (norm_nonneg _))

def act (T : Ω → H →L[ℂ] H)
    (hm : ∀ ξ : H,AEStronglyMeasurable (fun a => T a ξ) μ)
    {b : ℝ} (hb : ∀ᵐ a ∂μ,‖T a‖≤b) (f : Lp H 2 μ) : Lp H 2 μ :=
  (memLp_apply μ T hm hb f).toLp _

lemma act_ae (T : Ω → H →L[ℂ] H)
    (hm : ∀ ξ : H,AEStronglyMeasurable (fun a => T a ξ) μ)
    {b : ℝ} (hb : ∀ᵐ a ∂μ,‖T a‖≤b) (f : Lp H 2 μ) :
    act μ T hm hb f =ᵐ[μ] fun a => T a (f a) := MemLp.coeFn_toLp _

lemma act_add (T : Ω → H →L[ℂ] H)
    (hm : ∀ ξ : H,AEStronglyMeasurable (fun a => T a ξ) μ)
    {b : ℝ} (hb : ∀ᵐ a ∂μ,‖T a‖≤b) (f g : Lp H 2 μ) :
    act μ T hm hb (f+g)=act μ T hm hb f+act μ T hm hb g := by
  apply Lp.ext
  filter_upwards [act_ae μ T hm hb (f+g),act_ae μ T hm hb f,act_ae μ T hm hb g,
    Lp.coeFn_add f g,Lp.coeFn_add (act μ T hm hb f) (act μ T hm hb g)] with a h1 h2 h3 h4 h5
  rw [h1,h4,h5]
  change T a (f a+g a)=act μ T hm hb f a+act μ T hm hb g a
  rw [map_add,h2,h3]

lemma act_smul (T : Ω → H →L[ℂ] H)
    (hm : ∀ ξ : H,AEStronglyMeasurable (fun a => T a ξ) μ)
    {b : ℝ} (hb : ∀ᵐ a ∂μ,‖T a‖≤b) (c : ℂ) (f : Lp H 2 μ) :
    act μ T hm hb (c • f)=c • act μ T hm hb f := by
  apply Lp.ext
  filter_upwards [act_ae μ T hm hb (c • f),act_ae μ T hm hb f,
    Lp.coeFn_smul c f,Lp.coeFn_smul c (act μ T hm hb f)] with a h1 h2 h3 h4
  simp [h1,h2,h3,h4]

lemma act_norm_le (T : Ω → H →L[ℂ] H)
    (hm : ∀ ξ : H,AEStronglyMeasurable (fun a => T a ξ) μ)
    {b d : ℝ} (hb : ∀ᵐ a ∂μ,‖T a‖≤b) (hd : ∀ᵐ a ∂μ,‖T a‖≤d) (f : Lp H 2 μ) :
    ‖act μ T hm hb f‖≤d*‖f‖ := by
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [act_ae μ T hm hb f,hd] with a ha hda
  rw [ha]
  exact ((T a).le_opNorm (f a)).trans (mul_le_mul_of_nonneg_right hda (norm_nonneg _))

def operator (T : Ω → H →L[ℂ] H)
    (hm : ∀ ξ : H,AEStronglyMeasurable (fun a => T a ξ) μ)
    {b : ℝ} (hb : ∀ᵐ a ∂μ,‖T a‖≤b) : Lp H 2 μ →L[ℂ] Lp H 2 μ :=
  ({toFun := act μ T hm hb
    map_add' := act_add μ T hm hb
    map_smul' := act_smul μ T hm hb} : Lp H 2 μ →ₗ[ℂ] Lp H 2 μ).mkContinuous b
      (act_norm_le μ T hm hb hb)

lemma operator_ae (T : Ω → H →L[ℂ] H)
    (hm : ∀ ξ : H,AEStronglyMeasurable (fun a => T a ξ) μ)
    {b : ℝ} (hb : ∀ᵐ a ∂μ,‖T a‖≤b) (f : Lp H 2 μ) :
    operator μ T hm hb f =ᵐ[μ] fun a => T a (f a) := act_ae μ T hm hb f

lemma operator_norm_le (T : Ω → H →L[ℂ] H)
    (hm : ∀ ξ : H,AEStronglyMeasurable (fun a => T a ξ) μ)
    {b d : ℝ} (hb : ∀ᵐ a ∂μ,‖T a‖≤b) (hd0 : 0≤d) (hd : ∀ᵐ a ∂μ,‖T a‖≤d) :
    ‖operator μ T hm hb‖≤d :=
  ContinuousLinearMap.opNorm_le_bound _ hd0 (act_norm_le μ T hm hb hd)

end Kadison.Decomposable

end

end
end

end OAI
