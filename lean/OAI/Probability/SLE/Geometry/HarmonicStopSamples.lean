import OAI.Probability.SLE.Geometry.HarmonicMaximal

namespace OAI

/-! Ordered samples between compact domain stops retain their full stopped
past. The resulting finite maximal bound controls all mesh observations. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal

namespace SLEExactGauge
open Target

def orderedStopFiltration (ρ : ℕ → Driver×Driver → ℝ≥0)
    (hρ : ∀ n, IsStoppingTime planarWienerFiltration (fun b => (ρ n b : WithTop ℝ≥0)))
    (hmono : ∀ b, Monotone (fun n => ρ n b)) :
    Filtration ℕ (inferInstance : MeasurableSpace (Driver×Driver)) where
  seq n := (hρ n).measurableSpace
  mono' := fun n m hnm => (hρ n).measurableSpace_mono (hρ m)
    (fun b => WithTop.coe_le_coe.mpr (hmono b hnm))
  le' n := (hρ n).measurableSpace_le

theorem planar_local_harmonic_sampled_martingale
    (W : WienerLaw) (hW : IsWiener W) (U K : Set (ℝ×ℝ))
    (hU : IsOpen U) (hK : IsCompact K) (hKU : K ⊆ U)
    (u : ℝ×ℝ → ℝ) (hu : ContDiffOn ℝ (⊤ : ℕ∞) u U)
    (hhar : ∀ z∈U, planarGenerator u z=0)
    (ρ : ℕ → Driver×Driver → ℝ≥0)
    (hρ : ∀ n, IsStoppingTime planarWienerFiltration (fun b => (ρ n b : WithTop ℝ≥0)))
    (hmono : ∀ b, Monotone (fun n => ρ n b))
    (T : ℝ≥0) (hb : ∀ n b, ρ n b ≤ T)
    (hpath : ∀ n b t, t ≤ ρ n b → planarWiener t b∈K) :
    Martingale (fun n b => u (planarWiener (ρ n b) b))
      (orderedStopFiltration ρ hρ hmono) (W.prod W) := by
  let : IsProbabilityMeasure W := hW.isGaussianProcess.isProbabilityMeasure
  obtain ⟨f,hf,hfc,_,he,_,_⟩ := exists_compact_smooth_extension U K hU hK hKU u hu
  have hp := (Filtration.stronglyAdapted_natural (fun t =>
    (measurable_planarWiener t).stronglyMeasurable)).isStronglyProgressive_of_continuous
      planarWiener_continuous
  have heq (n b) : f (planarWiener (ρ n b) b)=u (planarWiener (ρ n b) b) :=
    (he _ (hpath n b _ le_rfl)).self_of_nhds
  have ha : StronglyAdapted (orderedStopFiltration ρ hρ hmono)
      (fun n b => u (planarWiener (ρ n b) b)) := by
    intro n
    have hm := hf.continuous.measurable.comp (measurable_stoppedValue hp (hρ n))
    change Measurable[(orderedStopFiltration ρ hρ hmono) n]
      (fun b => f (planarWiener (ρ n b) b)) at hm
    simpa only [heq] using hm.stronglyMeasurable
  obtain ⟨C,hC,_⟩ := compact_smooth_bounded_lipschitz f hf hfc
  apply martingale_of_setIntegral_eq_succ ha
  · intro n
    apply Integrable.of_bound ((ha n).mono ((orderedStopFiltration ρ hρ hmono).le n)).aestronglyMeasurable C
    exact Eventually.of_forall fun b => by
      change ‖u (planarWiener (ρ n b) b)‖ ≤ C
      rw [← heq n b]
      exact hC _
  · intro n A hA
    exact planar_local_harmonic_optional_between W hW U K hU hK hKU u hu hhar
      (ρ n) (ρ (n+1)) (hρ n) (hρ (n+1)) (fun b => hmono b (Nat.le_succ n))
      T (hb (n+1)) A hA (hpath (n+1))

theorem harmonic_clipped_grid_maximal
    (W : WienerLaw) (hW : IsWiener W) (U K : Set (ℝ×ℝ))
    (hU : IsOpen U) (hK : IsCompact K) (hKU : K ⊆ U)
    (u : ℝ×ℝ → ℝ) (hu : ContDiffOn ℝ (⊤ : ℕ∞) u U)
    (hhar : ∀ z∈U, planarGenerator u z=0)
    (σ τ : Driver×Driver → ℝ≥0)
    (hσ : IsStoppingTime planarWienerFiltration (fun b => (σ b : WithTop ℝ≥0)))
    (hτ : IsStoppingTime planarWienerFiltration (fun b => (τ b : WithTop ℝ≥0)))
    (hστ : ∀ b, σ b ≤ τ b) (T : ℝ≥0) (hb : ∀ b, τ b ≤ T)
    (hpath : ∀ b t, t ≤ τ b → planarWiener t b∈K)
    (q : ℕ → ℝ≥0) (hq : Monotone q) (hq0 : q 0=0)
    (N : ℕ) (hqN : T ≤ q N) (ε : ℝ≥0) :
    ε * (W.prod W) {b | ∃ k ≤ N,
      (ε:ℝ) ≤ |u (planarWiener (max (σ b) (min (q k) (τ b))) b)-
        u (planarWiener (σ b) b)|} ≤
      ENNReal.ofReal (∫ b, |u (planarWiener (τ b) b)-u (planarWiener (σ b) b)| ∂W.prod W) := by
  let : IsProbabilityMeasure W := hW.isGaussianProcess.isProbabilityMeasure
  let ρ (n : ℕ) (b : Driver×Driver) := max (σ b) (min (τ b) (q n))
  have hρ (n) : IsStoppingTime planarWienerFiltration (fun b => (ρ n b : WithTop ℝ≥0)) := by
    simpa only [ρ,WithTop.coe_max,WithTop.coe_min] using hσ.max (hτ.min_const (q n))
  have hm (b) : Monotone (fun n => ρ n b) :=
    fun i j hij => max_le_max_left _ (min_le_min_left _ (hq hij))
  have hle (n b) : ρ n b ≤ τ b := max_le (hστ b) (min_le_left _ _)
  have hM := planar_local_harmonic_sampled_martingale W hW U K hU hK hKU u hu hhar
    ρ hρ hm T (fun n b => (hle n b).trans (hb b))
    (fun n b t ht => hpath b t (ht.trans (hle n b)))
  have h0 (b) : ρ 0 b=σ b := by simp [ρ,hq0]
  have hN (b) : ρ N b=τ b := by
    simp only [ρ,min_eq_left ((hb b).trans hqN),max_eq_right (hστ b)]
  simpa only [h0,hN,ρ,min_comm] using martingale_finite_maximal hM ε N

end SLEExactGauge

end

end OAI
