import OAI.Probability.FreeIsing.Model

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology

namespace Problem367.SpinRecovery

def spinSign : IsingSpin → ℝ
  | .neg => -1
  | .pos => 1

def decode (x : ℕ → ℝ) : IsingSpin := by
  classical
  exact if Tendsto (fun n : ℕ => x n / (n : ℝ)) atTop (𝓝 (-1 : ℝ))
    then .neg else .pos

theorem measurable_decode : Measurable decode := by
  unfold decode
  apply Measurable.ite
  · exact measurableSet_tendsto (𝓝 (-1 : ℝ))
      (f := fun (n : ℕ) (x : ℕ → ℝ) => x n / (n : ℝ))
      (by intro n; fun_prop)
  · exact measurable_const
  · exact measurable_const

theorem decode_of_tendsto {x : ℕ → ℝ} {s : IsingSpin}
    (h : Tendsto (fun n : ℕ => x n / (n : ℝ)) atTop (𝓝 (spinSign s))) :
    decode x = s := by
  cases s with
  | neg =>
      simp only [spinSign] at h
      simp [decode, h]
  | pos =>
      have hn : ¬ Tendsto (fun n : ℕ => x n / (n : ℝ)) atTop (𝓝 (-1 : ℝ)) := by
        intro hm
        have he : (-1 : ℝ) = 1 := tendsto_nhds_unique hm h
        norm_num at he
      simp [decode, hn]

theorem decode_signal_add_noise (s : IsingSpin) {z : ℕ → ℝ}
    (hz : Tendsto (fun n : ℕ => z n / (n : ℝ)) atTop (𝓝 (0 : ℝ))) :
    decode (fun n : ℕ => (n : ℝ) * spinSign s + z n) = s := by
  apply decode_of_tendsto
  have he : (fun n : ℕ => ((n : ℝ) * spinSign s + z n) / (n : ℝ)) =ᶠ[atTop]
      (fun n : ℕ => spinSign s + z n / (n : ℝ)) := by
    filter_upwards [eventually_ge_atTop 1] with n hn
    have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
    field_simp
  apply (tendsto_congr' he).2
  simpa using tendsto_const_nhds.add hz

def decodeArray {V : Type*} (x : V → ℕ → ℝ) : V → IsingSpin :=
  fun v => decode (x v)

theorem measurable_decodeArray {V : Type*} :
    Measurable (decodeArray (V := V)) := by
  exact Measurable.of_eval fun vertex =>
    measurable_decode.comp (measurable_pi_apply vertex)

theorem decodeArray_comp {V W : Type*} (x : V → ℕ → ℝ) (f : W → V) :
    decodeArray (x ∘ f) = decodeArray x ∘ f := rfl

theorem decodeArray_relabel {d : ℕ} (g : TreeAut d)
    (x : TreeVertex d → ℕ → ℝ) :
    decodeArray (relabel g x) = relabel g (decodeArray x) := rfl

theorem decodeArray_of_tendsto {V : Type*} {x : V → ℕ → ℝ}
    {s : V → IsingSpin}
    (h : ∀ v, Tendsto (fun n : ℕ => x v n / (n : ℝ)) atTop (𝓝 (spinSign (s v)))) :
    decodeArray x = s := by
  funext v
  exact decode_of_tendsto (h v)

theorem decodeArray_ae_eq {Ω V : Type*} [MeasurableSpace Ω] [Countable V]
    {μ : Measure Ω} {x : Ω → V → ℕ → ℝ} {s : Ω → V → IsingSpin}
    (h : ∀ v, ∀ᵐ ω ∂μ,
      Tendsto (fun n : ℕ => x ω v n / (n : ℝ)) atTop (𝓝 (spinSign (s ω v)))) :
    (fun ω => decodeArray (x ω)) =ᵐ[μ] s := by
  filter_upwards [ae_all_iff.2 h] with ω hω
  exact decodeArray_of_tendsto hω

theorem map_decodeArray_eq {Ω V : Type*} [MeasurableSpace Ω] [Countable V]
    {μ : Measure Ω} {x : Ω → V → ℕ → ℝ} {s : Ω → V → IsingSpin}
    (h : ∀ v, ∀ᵐ ω ∂μ,
      Tendsto (fun n : ℕ => x ω v n / (n : ℝ)) atTop (𝓝 (spinSign (s ω v)))) :
    Measure.map (fun ω => decodeArray (x ω)) μ = Measure.map s μ :=
  Measure.map_congr (decodeArray_ae_eq h)

end Problem367.SpinRecovery

end

end OAI
