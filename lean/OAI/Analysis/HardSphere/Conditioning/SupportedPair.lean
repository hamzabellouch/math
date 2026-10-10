import Mathlib

namespace OAI

section

section
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
namespace HardSphere.Comparison
variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]

def supportedPair (ρ : Measure (X×Y)) (S : Set X) (T : Set Y) : Measure (S×T) :=
  ρ.comap (Prod.map Subtype.val Subtype.val)

lemma supportedPair_map (ρ : Measure (X×Y)) {S : Set X} {T : Set Y}
    (hS : MeasurableSet S) (hT : MeasurableSet T) (hρ : ∀ᵐp ∂ρ,p.1∈S ∧ p.2∈T) :
    (supportedPair ρ S T).map (Prod.map Subtype.val Subtype.val)=ρ := by
  rw [supportedPair,((MeasurableEmbedding.subtype_coe hS).prodMap
    (MeasurableEmbedding.subtype_coe hT)).map_comap]
  apply Measure.restrict_eq_self_of_ae_mem
  filter_upwards [hρ] with p hp
  exact ⟨(⟨p.1,hp.1⟩,⟨p.2,hp.2⟩),rfl⟩

lemma supportedPair_probability (ρ : Measure (X×Y)) [IsProbabilityMeasure ρ]
    {S : Set X} {T : Set Y} (hS : MeasurableSet S) (hT : MeasurableSet T)
    (hρ : ∀ᵐp ∂ρ,p.1∈S ∧ p.2∈T) : IsProbabilityMeasure (supportedPair ρ S T) := by
  constructor
  have h := congrArg (fun μ : Measure (X×Y) ↦ μ univ) (supportedPair_map ρ hS hT hρ)
  simpa only [Measure.map_apply (by fun_prop : Measurable (Prod.map (Subtype.val:S→X) (Subtype.val:T→Y)))
    MeasurableSet.univ,preimage_univ,measure_univ] using h

lemma map_le_reflect {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
    {f : A→B} (hf : MeasurableEmbedding f) {μ ν : Measure A}
    (h : μ.map f≤ν.map f) : μ≤ν := by
  apply Measure.le_iff.mpr
  intro C hC
  have hh := h (f '' C)
  simpa only [hf.map_apply,hf.injective.preimage_image] using hh

lemma supportedPair_fst (ρ : Measure (X×Y)) {S : Set X} {T : Set Y}
    (hS : MeasurableSet S) (hT : MeasurableSet T) (hρ : ∀ᵐp ∂ρ,p.1∈S ∧ p.2∈T) :
    (supportedPair ρ S T).fst.map Subtype.val=ρ.fst := by
  have h := congrArg (fun μ : Measure (X×Y) ↦ μ.fst) (supportedPair_map ρ hS hT hρ)
  rw [Measure.fst,Measure.map_map measurable_fst (by fun_prop)] at h
  rw [Measure.fst,Measure.map_map measurable_subtype_coe measurable_fst]
  exact h

lemma supportedPair_snd (ρ : Measure (X×Y)) {S : Set X} {T : Set Y}
    (hS : MeasurableSet S) (hT : MeasurableSet T) (hρ : ∀ᵐp ∂ρ,p.1∈S ∧ p.2∈T) :
    (supportedPair ρ S T).snd.map Subtype.val=ρ.snd := by
  have h := congrArg (fun μ : Measure (X×Y) ↦ μ.snd) (supportedPair_map ρ hS hT hρ)
  rw [Measure.snd,Measure.map_map measurable_snd (by fun_prop)] at h
  rw [Measure.snd,Measure.map_map measurable_subtype_coe measurable_snd]
  exact h

lemma supportedPair_fst_le (ρ : Measure (X×Y)) {S : Set X} {T : Set Y}
    (hS : MeasurableSet S) (hT : MeasurableSet T) (hρ : ∀ᵐp ∂ρ,p.1∈S ∧ p.2∈T)
    (P : Measure S) {G : ℝ≥0∞} (hP : ρ.fst≤G • P.map Subtype.val) :
    (supportedPair ρ S T).fst≤G • P := by
  apply map_le_reflect (MeasurableEmbedding.subtype_coe hS)
  rw [supportedPair_fst ρ hS hT hρ,Measure.map_smul _ measurable_subtype_coe.aemeasurable]
  exact hP

lemma supportedPair_snd_le (ρ : Measure (X×Y)) {S : Set X} {T : Set Y}
    (hS : MeasurableSet S) (hT : MeasurableSet T) (hρ : ∀ᵐp ∂ρ,p.1∈S ∧ p.2∈T)
    (P : Measure T) {G : ℝ≥0∞} (hP : ρ.snd≤G • P.map Subtype.val) :
    (supportedPair ρ S T).snd≤G • P := by
  apply map_le_reflect (MeasurableEmbedding.subtype_coe hT)
  rw [supportedPair_snd ρ hS hT hρ,Measure.map_smul _ measurable_subtype_coe.aemeasurable]
  exact hP

lemma supported_of_marginals (ρ : Measure (X×Y)) {S : Set X} {T : Set Y}
    (hS : MeasurableSet S) (hT : MeasurableSet T) (P : Measure S) (Q : Measure T)
    {G H : ℝ≥0∞} (hP : ρ.fst≤G • P.map Subtype.val) (hQ : ρ.snd≤H • Q.map Subtype.val) :
    ∀ᵐp ∂ρ,p.1∈S ∧ p.2∈T := by
  have hp0 : (P.map Subtype.val) Sᶜ=0 := by
    rw [Measure.map_apply measurable_subtype_coe hS.compl]
    have he : (Subtype.val:S→X) ⁻¹' Sᶜ=∅ := by ext x; simp only [mem_preimage,mem_compl_iff,x.property,not_true,mem_empty_iff_false]
    rw [he,measure_empty]
  have hq0 : (Q.map Subtype.val) Tᶜ=0 := by
    rw [Measure.map_apply measurable_subtype_coe hT.compl]
    have he : (Subtype.val:T→Y) ⁻¹' Tᶜ=∅ := by ext x; simp only [mem_preimage,mem_compl_iff,x.property,not_true,mem_empty_iff_false]
    rw [he,measure_empty]
  have hpa : ∀ᵐx ∂ρ.fst,x∈S := by
    rw [ae_iff]
    change ρ.fst Sᶜ=0
    exact le_antisymm (by simpa only [Measure.smul_apply,smul_eq_mul,hp0,mul_zero] using hP Sᶜ) bot_le
  have hqa : ∀ᵐy ∂ρ.snd,y∈T := by
    rw [ae_iff]
    change ρ.snd Tᶜ=0
    exact le_antisymm (by simpa only [Measure.smul_apply,smul_eq_mul,hq0,mul_zero] using hQ Tᶜ) bot_le
  have hp' : ∀ᵐp ∂ρ,p.1∈S := (ae_map_iff measurable_fst.aemeasurable hS).mp hpa
  have hq' : ∀ᵐp ∂ρ,p.2∈T := (ae_map_iff measurable_snd.aemeasurable hT).mp hqa
  exact hp'.and hq'

end HardSphere.Comparison

end
end

end

end OAI
