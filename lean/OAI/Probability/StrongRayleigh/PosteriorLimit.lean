import Mathlib

namespace OAI

universe u_1 u_2 u_3 u_4

noncomputable section

open MeasureTheory Filter
open scoped Topology ProbabilityTheory

namespace Problem336AdditiveD139.PosteriorLimit

variable {Ω : Type u_1} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}

theorem tendsto_of_ae_eq_condExp [IsFiniteMeasure μ]
    (ℱ : Filtration ℕ mΩ) (X : Ω → ℝ) (b : ℕ → Ω → ℝ)
    (hb : ∀ n, b n =ᵐ[μ] μ[X | ℱ n]) :
    ∀ᵐ ω ∂μ, Tendsto (fun n => b n ω) atTop
      (𝓝 ((μ[X | ⨆ n, ℱ n]) ω)) := by
  have hall : ∀ᵐ ω ∂μ, ∀ n, b n ω = (μ[X | ℱ n]) ω :=
    ae_all_iff.mpr hb
  filter_upwards [hall, MeasureTheory.tendsto_ae_condExp (ℱ := ℱ) X] with ω hω hlim
  exact hlim.congr (fun n => (hω n).symm)

theorem limsup_ae_eq_condExp [IsFiniteMeasure μ]
    (ℱ : Filtration ℕ mΩ) (X : Ω → ℝ) (b : ℕ → Ω → ℝ)
    (hb : ∀ n, b n =ᵐ[μ] μ[X | ℱ n]) :
    (fun ω => limsup (fun n => b n ω) atTop) =ᵐ[μ]
      μ[X | ⨆ n, ℱ n] := by
  filter_upwards [tendsto_of_ae_eq_condExp ℱ X b hb] with ω hω
  exact hω.limsup_eq

theorem tendsto_eLpNorm_of_ae_eq_condExp [IsFiniteMeasure μ]
    (ℱ : Filtration ℕ mΩ) (X : Ω → ℝ) (b : ℕ → Ω → ℝ)
    (hb : ∀ n, b n =ᵐ[μ] μ[X | ℱ n]) :
    Tendsto (fun n => eLpNorm (b n - μ[X | ⨆ k, ℱ k]) 1 μ)
      atTop (𝓝 0) := by
  refine (MeasureTheory.tendsto_eLpNorm_condExp (μ := μ) (ℱ := ℱ) X).congr ?_
  intro n
  apply eLpNorm_congr_ae
  filter_upwards [hb n] with ω hω
  simp only [Pi.sub_apply, hω]

section ObservationSpaces

variable {I : Type u_2} {T : Type u_3} {E : Type u_4} [MeasurableSpace E]

@[reducible] def observationSpace (Y : I → T → Ω → E) (S : Set I) : MeasurableSpace Ω :=
  ⨆ i ∈ S, ⨆ t, MeasurableSpace.comap (Y i t) inferInstance

theorem observationSpace_mono (Y : I → T → Ω → E) :
    Monotone (observationSpace Y) := by
  intro S S' hS
  exact iSup_le fun i => iSup_le fun hi =>
    le_iSup_of_le i (le_iSup_of_le (hS hi) le_rfl)

theorem observationSpace_le (Y : I → T → Ω → E)
    (hY : ∀ i t, Measurable (Y i t)) (S : Set I) :
    observationSpace Y S ≤ mΩ := by
  exact iSup_le fun i => iSup_le fun _ => iSup_le fun t => (hY i t).comap_le

theorem iSup_observationSpace_eq (Y : I → T → Ω → E) (S : ℕ → Set I)
    (hS : ∀ i, ∃ n, i ∈ S n) :
    (⨆ n, observationSpace Y (S n)) = observationSpace Y Set.univ := by
  apply le_antisymm
  · exact iSup_le fun n => observationSpace_mono Y (Set.subset_univ _)
  · refine iSup_le fun i => iSup_le fun _ => ?_
    obtain ⟨n, hn⟩ := hS i
    exact le_iSup_of_le n (le_iSup_of_le i (le_iSup_of_le hn le_rfl))

def observationFiltration (Y : I → T → Ω → E)
    (hY : ∀ i t, Measurable (Y i t)) (S : ℕ → Set I)
    (hmono : Monotone S) : Filtration ℕ mΩ where
  seq n := observationSpace Y (S n)
  mono' := fun _ _ hnm => observationSpace_mono Y (hmono hnm)
  le' n := observationSpace_le Y hY (S n)

theorem limsup_ae_eq_full_observation_condExp [IsFiniteMeasure μ]
    (Y : I → T → Ω → E) (hY : ∀ i t, Measurable (Y i t))
    (S : ℕ → Set I) (hmono : Monotone S) (hexhaust : ∀ i, ∃ n, i ∈ S n)
    (X : Ω → ℝ) (b : ℕ → Ω → ℝ)
    (hb : ∀ n, b n =ᵐ[μ] μ[X | observationSpace Y (S n)]) :
    (fun ω => limsup (fun n => b n ω) atTop) =ᵐ[μ]
      μ[X | observationSpace Y Set.univ] := by
  have h := limsup_ae_eq_condExp (observationFiltration Y hY S hmono) X b hb
  change (fun ω => limsup (fun n => b n ω) atTop) =ᵐ[μ]
    μ[X | ⨆ n, observationSpace Y (S n)] at h
  rwa [iSup_observationSpace_eq Y S hexhaust] at h

end ObservationSpaces

end Problem336AdditiveD139.PosteriorLimit

end

end OAI
