import Mathlib
import OAI.Probability.LogConcave.Dynamics.Squared

namespace OAI

section
noncomputable section
namespace LogConcaveSampling.Coupling
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology Classical

variable {E : Type*} [MetricSpace E] [CompleteSpace E] [SecondCountableTopology E]
  [MeasurableSpace E] [BorelSpace E]

def DistanceCoupled (μ ν : Measure E) (R : ℝ) : Prop :=
  ∃κ : Measure (E×E),IsProbabilityMeasure κ ∧ κ.fst=μ ∧ κ.snd=ν ∧
    ∀ᵐ z ∂κ,dist z.1 z.2≤R

lemma tight_range_of_tendsto {μ : ProbabilityMeasure E} {μs : ℕ → ProbabilityMeasure E}
    (h : Tendsto μs atTop (𝓝 μ)) : IsTightMeasureSet (range (fun n => (μs n : Measure E))) := by
  have hc : IsCompact (closure (range μs)) := h.isCompact_insert_range.of_isClosed_subset
    isClosed_closure (closure_minimal (subset_insert _ _) h.isCompact_insert_range.isClosed)
  have hh := isTightMeasureSet_of_isCompact_closure hc
  convert hh using 1
  ext ν
  simp only [mem_range,mem_ofPred_eq]
  aesop

theorem distanceCoupled_of_tendsto {μ ν : ProbabilityMeasure E}
    {μs νs : ℕ → ProbabilityMeasure E} (hμ : Tendsto μs atTop (𝓝 μ))
    (hν : Tendsto νs atTop (𝓝 ν)) (R : ℝ)
    (hc : ∀n,DistanceCoupled (μs n : Measure E) (νs n : Measure E) R) : DistanceCoupled (μ : Measure E) (ν : Measure E) R := by
  choose κ hκ hfst hsnd hdist using hc
  let Ks : ℕ → ProbabilityMeasure (E×E) := fun n => ⟨κ n,hκ n⟩
  have hj : IsTightMeasureSet (range κ) := by
    apply IsTightMeasureSet.prodMk
    · have he : Measure.fst '' range κ=range (fun n => (μs n : Measure E)) := by
        ext ρ
        simp only [mem_image,mem_range,exists_exists_eq_and]
        simp only [hfst]
      rw [he]
      exact tight_range_of_tendsto hμ
    · have he : Measure.snd '' range κ=range (fun n => (νs n : Measure E)) := by
        ext ρ
        simp only [mem_image,mem_range,exists_exists_eq_and]
        simp only [hsnd]
      rw [he]
      exact tight_range_of_tendsto hν
  have hj' : IsTightMeasureSet {((ρ : ProbabilityMeasure (E×E)) : Measure (E×E)) | ρ∈range Ks} := by
    convert hj using 1
    ext ρ
    simp only [mem_ofPred_eq,mem_range,exists_exists_eq_and]
    rfl
  obtain ⟨K,_,φ,hφ,hK⟩ := (isCompact_closure_of_isTightMeasureSet hj').tendsto_subseq
    (fun n => subset_closure (mem_range_self n))
  have hf := ProbabilityMeasure.tendsto_map_of_tendsto_of_continuous (Ks ∘ φ) K hK continuous_fst
  have hg := ProbabilityMeasure.tendsto_map_of_tendsto_of_continuous (Ks ∘ φ) K hK continuous_snd
  have hfm : (fun n => (Ks (φ n)).map Prod.fst)=μs ∘ φ := by
    funext n; apply Subtype.ext; exact hfst (φ n)
  have hgm : (fun n => (Ks (φ n)).map Prod.snd)=νs ∘ φ := by
    funext n; apply Subtype.ext; exact hsnd (φ n)
  simp only [Function.comp_apply] at hf hg
  rw [hfm] at hf
  rw [hgm] at hg
  have hef := tendsto_nhds_unique hf (hμ.comp hφ.tendsto_atTop)
  have heg := tendsto_nhds_unique hg (hν.comp hφ.tendsto_atTop)
  refine ⟨K,inferInstance,congrArg (fun p : ProbabilityMeasure E => (p : Measure E)) hef,
    congrArg (fun p : ProbabilityMeasure E => (p : Measure E)) heg,?_⟩
  let S : Set (E×E) := {z | dist z.1 z.2≤R}
  have hS : IsClosed S := isClosed_le (continuous_fst.dist continuous_snd) continuous_const
  have hprob (n : ℕ) : (Ks n : Measure (E×E)) S=1 := by
    calc (Ks n : Measure (E×E)) S = (Ks n : Measure (E×E)) univ := by
          apply measure_congr
          filter_upwards [hdist n] with z hz
          apply propext
          change (dist z.1 z.2≤R) ↔ True
          exact iff_true_intro hz
      _ = 1 := measure_univ
  have hl := ProbabilityMeasure.limsup_measure_closed_le_of_tendsto hK hS
  simp only [Function.comp_apply,hprob,limsup_const] at hl
  have he : (K : Measure (E×E)) S=1 := le_antisymm (by simpa only [measure_univ] using (measure_mono (subset_univ S) : (K : Measure (E×E)) S≤(K : Measure (E×E)) univ)) hl
  rw [←show (∀ᵐ z : E×E ∂(K : Measure (E×E)),z∈S) ↔ (∀ᵐ z ∂(K : Measure (E×E)),dist z.1 z.2≤R) from Iff.rfl]
  exact (ae_iff).mpr (by
    change (K : Measure (E×E)) Sᶜ=0
    rw [measure_compl hS.measurableSet (measure_ne_top _ _),measure_univ,he,tsub_self])

lemma DistanceCoupled.squared {d : ℕ} {μ ν : Measure (Point d)} {R : ℝ}
    (hr : 0≤R) (h : DistanceCoupled μ ν R) : SquaredAt μ ν id id (R^2) := by
  obtain ⟨κ,hκ,hf,hg,hd⟩ := h
  let := hκ
  have hb : ∀ᵐ z ∂κ, ‖z.1-z.2‖^2≤R^2 := hd.mono (fun z hz =>
    (sq_le_sq₀ (norm_nonneg _) hr).2 (by simpa only [dist_eq_norm] using hz))
  have hi : Integrable (fun z : Point d × Point d => ‖z.1-z.2‖^2) κ :=
    (integrable_const (R^2)).mono' (by fun_prop)
      (hb.mono (fun z hz => by simpa only [Real.norm_eq_abs,abs_sq] using hz))
  refine ⟨κ,hκ,hf,hg,hi,?_⟩
  simpa only [id_eq,integral_const,probReal_univ,one_smul] using integral_mono_ae hi (integrable_const (R^2)) hb
end LogConcaveSampling.Coupling

end

end

end OAI
