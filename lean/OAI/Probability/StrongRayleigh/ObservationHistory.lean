import OAI.Probability.StrongRayleigh.PosteriorLimit

namespace OAI

universe u_1 u_2 u_3

noncomputable section

open MeasureTheory
open scoped ProbabilityTheory NNReal

namespace Problem336AdditiveD139.PosteriorLimit

variable {Ω : Type u_1} {I : Type u_2} {T : Type u_3}

@[reducible] def endpointSpace (Y : I → T → Ω → ℝ) (S : Set I) (t : T) :
    MeasurableSpace Ω :=
  ⨆ i ∈ S, MeasurableSpace.comap (Y i t) inferInstance

def centeredHistory (Y : I → T → Ω → ℝ) (t : T) (a : T → ℝ) : I → T → Ω → ℝ :=
  fun i s ω => Y i s ω - a s * Y i t ω

theorem endpointSpace_eq_comap (Y : I → T → Ω → ℝ) (S : Set I) (t : T) :
    endpointSpace Y S t =
      MeasurableSpace.comap (fun ω (i : S) => Y i t ω) inferInstance := by
  simp only [MeasurableSpace.comap_process_pi, endpointSpace, iSup_subtype]

theorem observationSpace_eq_comap (Y : I → T → Ω → ℝ) (S : Set I) :
    observationSpace Y S =
      MeasurableSpace.comap (fun ω (i : S) (s : T) => Y i s ω) inferInstance := by
  simp only [MeasurableSpace.comap_process_pi, observationSpace, iSup_subtype]

theorem measurable_observation (Y : I → T → Ω → ℝ) (S : Set I)
    {i : I} (hi : i ∈ S) (s : T) :
    @Measurable Ω ℝ (observationSpace Y S) inferInstance (Y i s) := by
  apply Measurable.of_comap_le
  exact le_iSup_of_le i (le_iSup_of_le hi (le_iSup_of_le s le_rfl))

theorem endpointSpace_le_observationSpace (Y : I → T → Ω → ℝ)
    (S : Set I) (t : T) : endpointSpace Y S t ≤ observationSpace Y S := by
  exact iSup_le fun i => iSup_le fun hi =>
    (measurable_observation Y S hi t).comap_le

theorem observationSpace_eq_endpoint_sup_bridge (Y : I → T → Ω → ℝ)
    (S : Set I) (t : T) (a : T → ℝ) :
    observationSpace Y S = endpointSpace Y S t ⊔
      observationSpace (fun i s ω => Y i s ω - a s * Y i t ω) S := by
  apply le_antisymm
  · refine iSup_le fun i => iSup_le fun hi => iSup_le fun s => ?_
    apply Measurable.comap_le
    have he0 : MeasurableSpace.comap (Y i t) inferInstance ≤ endpointSpace Y S t := by
      exact le_iSup_of_le i (le_iSup_of_le hi le_rfl)
    have he : @Measurable Ω ℝ
        (endpointSpace Y S t ⊔
          observationSpace (fun i s ω => Y i s ω - a s * Y i t ω) S)
        inferInstance (Y i t) :=
      Measurable.of_comap_le (he0.trans le_sup_left)
    have hb : @Measurable Ω ℝ
        (endpointSpace Y S t ⊔
          observationSpace (fun i s ω => Y i s ω - a s * Y i t ω) S)
        inferInstance (fun ω => Y i s ω - a s * Y i t ω) :=
      (measurable_observation
        (fun i s ω => Y i s ω - a s * Y i t ω) S hi s).mono le_sup_right le_rfl
    convert hb.add (he.const_mul (a s)) using 1
    funext ω
    change Y i s ω = (Y i s ω - a s * Y i t ω) + a s * Y i t ω
    ring
  · refine sup_le (endpointSpace_le_observationSpace Y S t) ?_
    exact iSup_le fun i => iSup_le fun hi => iSup_le fun s =>
      ((measurable_observation Y S hi s).sub
        (measurable_const.mul (measurable_observation Y S hi t))).comap_le

theorem signal_observationSpace_eq_endpoint_sup_noise_bridge
    (X : I → Ω → ℝ) (B : I → ℝ≥0 → Ω → ℝ) (S : Set I)
    (t : ℝ≥0) (ht : t ≠ 0) :
    observationSpace
      (fun i (s : Set.Iic t) ω => (s.1 : ℝ) * X i ω + B i s.1 ω) S =
      endpointSpace
        (fun i (s : Set.Iic t) ω => (s.1 : ℝ) * X i ω + B i s.1 ω)
        S ⟨t, by simp⟩ ⊔
      observationSpace
        (fun i (s : Set.Iic t) ω => B i s.1 ω - (s.1 : ℝ) / (t : ℝ) * B i t ω) S := by
  have ht' : (t : ℝ) ≠ 0 := by exact_mod_cast ht
  rw [observationSpace_eq_endpoint_sup_bridge
    (fun i (s : Set.Iic t) ω => (s.1 : ℝ) * X i ω + B i s.1 ω)
    S ⟨t, by simp⟩ (fun s : Set.Iic t => (s.1 : ℝ) / (t : ℝ))]
  congr 2
  funext i s ω
  field_simp [ht']
  ring

end Problem336AdditiveD139.PosteriorLimit

end

end OAI
