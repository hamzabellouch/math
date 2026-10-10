import OAI.Probability.SLE.Geometry.HarmonicStopSamples

namespace OAI

/-! Passing the finite mesh maximal estimate to all times between two
compact localization stops. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal

namespace SLEExactGauge
open Target

lemma mul_measure_le_of_eventually_mem {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (E : Set Ω) (A : ℕ → Set Ω) (c C : ℝ≥0∞)
    (hEA : ∀ b∈E, ∀ᶠ n in atTop, b∈A n) (hA : ∀ n, c*μ (A n) ≤ C) :
    c*μ E ≤ C := by
  let B (n : ℕ) := {b | ∀ k, n ≤ k → b∈A k}
  have hmono : Monotone B := fun i j hij b hb k hjk => hb k (hij.trans hjk)
  have hsub : E ⊆ ⋃ n, B n := by
    intro b hb
    obtain ⟨n,hn⟩ := eventually_atTop.mp (hEA b hb)
    exact mem_iUnion.mpr ⟨n,hn⟩
  calc
    c*μ E ≤ c*μ (⋃ n, B n) := by gcongr
    _ = ⨆ n, c*μ (B n) := by rw [hmono.measure_iUnion,ENNReal.mul_iSup]
    _ ≤ C := iSup_le fun n => le_trans (by
      gcongr
      exact fun b (hb : b∈B n) => hb n le_rfl) (hA n)

theorem harmonic_path_maximal
    (W : WienerLaw) (hW : IsWiener W) (U K : Set (ℝ×ℝ))
    (hU : IsOpen U) (hK : IsCompact K) (hKU : K ⊆ U)
    (u : ℝ×ℝ → ℝ) (hu : ContDiffOn ℝ (⊤ : ℕ∞) u U)
    (hhar : ∀ z∈U, planarGenerator u z=0)
    (σ τ : Driver×Driver → ℝ≥0)
    (hσ : IsStoppingTime planarWienerFiltration (fun b => (σ b : WithTop ℝ≥0)))
    (hτ : IsStoppingTime planarWienerFiltration (fun b => (τ b : WithTop ℝ≥0)))
    (hστ : ∀ b, σ b ≤ τ b) (T : ℝ≥0) (hb : ∀ b, τ b ≤ T)
    (hpath : ∀ b t, t ≤ τ b → planarWiener t b∈K) (ε : ℝ≥0) :
    ε * (W.prod W) {b | ∃ t∈Icc (σ b) (τ b),
      (ε:ℝ) < |u (planarWiener t b)-u (planarWiener (σ b) b)|} ≤
      ENNReal.ofReal (∫ b, |u (planarWiener (τ b) b)-u (planarWiener (σ b) b)| ∂W.prod W) := by
  obtain ⟨f,hf,_,_,he,_,_⟩ := exists_compact_smooth_extension U K hU hK hKU u hu
  let A (n : ℕ) := {b | ∃ k ≤ stopGridIndex n T,
    (ε:ℝ) ≤ |u (planarWiener (max (σ b) (min (stopGridTime n k) (τ b))) b)-
      u (planarWiener (σ b) b)|}
  apply mul_measure_le_of_eventually_mem (W.prod W) _ A ε _
  · rintro b ⟨t,ht,hε⟩
    let H (v : ℝ≥0) := f (planarWiener (max (σ b) (min v (τ b))) b)
    have hH : Continuous H := hf.continuous.comp ((planarWiener_continuous b).comp
      (continuous_const.max (continuous_id.min continuous_const)))
    have heval (v : ℝ≥0) : H v=
        u (planarWiener (max (σ b) (min v (τ b))) b) :=
      (he _ (hpath b _ (max_le (hστ b) (min_le_right _ _)))).self_of_nhds
    have hbase : H (σ b)=u (planarWiener (σ b) b) := by
      rw [heval,min_eq_left (hστ b),max_self]
    have htval : H t=u (planarWiener t b) := by
      rw [heval,min_eq_left ht.2,max_eq_right ht.1]
    have hlim := ((hH.continuousAt.tendsto.comp (stopGrid_tendsto t)).sub_const
      (H (σ b))).abs
    have hev : ∀ᶠ n in atTop, (ε:ℝ) < |H (stopGrid n t)-H (σ b)| :=
      hlim.eventually (eventually_gt_nhds (by simpa only [htval,hbase] using hε))
    filter_upwards [hev] with n hn
    refine ⟨stopGridIndex n t,?_,?_⟩
    · exact (stopGridIndex_le n _ _).mpr
        ((ht.2.trans (hb b)).trans (stopGrid_bounds n T).1)
    · rw [hbase,heval] at hn
      simpa only [stopGrid] using hn.le
  · intro n
    exact harmonic_clipped_grid_maximal W hW U K hU hK hKU u hu hhar σ τ hσ hτ hστ
      T hb hpath (stopGridTime n) (monotone_stopGridTime n)
      (by simp [stopGridTime]) (stopGridIndex n T) (stopGrid_bounds n T).1 ε

end SLEExactGauge

end

end OAI
