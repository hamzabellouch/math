import OAI.MathematicalPhysics.Boltzmann.Approximation.CapDilationScales
import OAI.MathematicalPhysics.Boltzmann.Approximation.CappedDensitySequence
import OAI.MathematicalPhysics.Boltzmann.Branching.OuterTightness
import OAI.MathematicalPhysics.Boltzmann.Branching.RawPairCompactness
import OAI.MathematicalPhysics.Boltzmann.Branching.RebuiltHotCapBound
import OAI.MathematicalPhysics.Boltzmann.Branching.WeightedNetLoss
import OAI.MathematicalPhysics.Boltzmann.Jets.GeometricColdSource
import OAI.MathematicalPhysics.Boltzmann.Jets.GeometricMesh
import OAI.MathematicalPhysics.Boltzmann.Jets.JetFamilyBounds
import OAI.MathematicalPhysics.Boltzmann.Jets.SpatialDilationAE

namespace OAI

section

/-! # Actual cap shots on horizons tending to zero -/

noncomputable section

open MeasureTheory Set Filter
open scoped Topology

namespace BoltzmannNonuniqueness.JetCopyDatum

def shrinkingHorizon (τ : ℝ) (n : ℕ) : ℝ := τ/((n:ℝ)+1)

theorem shrinkingHorizon_pos {τ : ℝ} (hτ : 0 < τ) (n : ℕ) : 0 < shrinkingHorizon τ n :=
  div_pos hτ (by positivity)

theorem shrinkingHorizon_le {τ : ℝ} (hτ : 0 < τ) (n : ℕ) : shrinkingHorizon τ n ≤ τ := by
  apply (div_le_iff₀ (by positivity : 0 < (n:ℝ)+1)).mpr
  nlinarith [Nat.cast_nonneg (α := ℝ) n]

theorem shrinkingHorizon_tendsto_zero (τ : ℝ) :
    Tendsto (shrinkingHorizon τ) atTop (𝓝 0) := by
  change Tendsto (fun n : ℕ => τ/((n:ℝ)+1)) atTop (𝓝 0)
  have h := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul τ
  simpa only [div_eq_mul_inv,one_mul,mul_zero] using h

theorem exists_diagonal_cap_indices {s₀ η τ : ℝ} (hs₀ : 0 < s₀) (hη : 0 < η)
    (hτ : 0 < τ) :
    ∃ N : ℕ → ℕ, (∀ n, n ≤ N n) ∧ Tendsto N atTop atTop ∧
      Tendsto (fun n => DatumBounds.scale s₀ η (N n+1)/shrinkingHorizon τ n) atTop (𝓝 0) := by
  have hex (n : ℕ) : ∃ N : ℕ, n ≤ N ∧
      DatumBounds.scale s₀ η (N+1) ≤ (shrinkingHorizon τ n)^2 := by
    have hlim := (DatumBounds.scale_tendsto_zero s₀ hη).eventually
      (gt_mem_nhds (sq_pos_of_pos (shrinkingHorizon_pos hτ n)))
    obtain ⟨M,hM⟩ := eventually_atTop.mp hlim
    refine ⟨max n M,le_max_left _ _,?_⟩
    exact (hM (max n M+1) ((le_max_right n M).trans (Nat.le_succ _))).le
  choose N hN hb using hex
  refine ⟨N,hN,tendsto_atTop_mono hN tendsto_id,?_⟩
  apply squeeze_zero (fun n => div_nonneg (DatumBounds.scale_pos hs₀ _).le
    (shrinkingHorizon_pos hτ n).le) (fun n => ?_) (shrinkingHorizon_tendsto_zero τ)
  apply (div_le_iff₀ (shrinkingHorizon_pos hτ n)).mpr
  simpa only [pow_two] using hb n

structure ShrinkingCapFamily (s₀ η K α γ d₀ q : ℝ) where
  horizonScale : ℝ
  horizonScale_pos : 0 < horizonScale
  horizonScale_le : horizonScale ≤ 1/32
  indices : ℕ → ℕ
  indices_ge : ∀ n, n ≤ indices n
  indices_tendsto : Tendsto indices atTop atTop
  cold_ratio_tendsto : Tendsto (fun n => DatumBounds.scale s₀ η (indices n+1)/
    shrinkingHorizon horizonScale n) atTop (𝓝 0)
  approximation : ∀ n, CapApproximation s₀ η K α γ d₀ q (shrinkingHorizon horizonScale n) (indices n)

theorem exists_shrinking_cap_family (hcarleman : Published.GPV2009CarlemanInput)
    {s₀ η K α γ d₀ q : ℝ}
    (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8) (hη : 0 < η) (hηmax : η ≤ Real.log 2)
    (hK : 0 ≤ K) (hα : 0 < α) (hαmax : α ≤ 1/4) (hγ : 0 < γ)
    (hd₀ : 0 < d₀) (hd₀max : d₀ ≤ 1) (hwidth : d₀*(1/8:ℝ)^10 ≤ 1/64)
    (hsmall : JetComparisonCoefficient.coefficient K*d₀*s₀^9 ≤ 1)
    (hq₁ : 1 < q) (hq₂ : q < 2) : Nonempty (ShrinkingCapFamily s₀ η K α γ d₀ q) := by
  obtain ⟨τ,hτ,hτmax,hcap⟩ := exists_uniform_cap_solution hcarleman hs₀ hsmax hη hηmax
    hK hα hαmax hγ hd₀ hd₀max hwidth hsmall hq₁ hq₂
  obtain ⟨N,hN,hNlim,hratio⟩ := exists_diagonal_cap_indices hs₀ hη hτ
  have hex (n) : Nonempty (CapApproximation s₀ η K α γ d₀ q (shrinkingHorizon τ n) (N n)) := by
    obtain ⟨A,ell,hA,hell,hinit,F,hF⟩ := hcap (N n) (N n+1) (shrinkingHorizon τ n)
      (by positivity) (shrinkingHorizon_pos hτ n).le (shrinkingHorizon_le hτ n)
    exact ⟨⟨A,ell,hA,hell,hinit,F,hF⟩⟩
  exact ⟨⟨τ,hτ,hτmax,N,hN,hNlim,hratio,fun n => Classical.choice (hex n)⟩⟩

end BoltzmannNonuniqueness.JetCopyDatum

end

end

section

/-! # An actual cap approximation has a time attaining its normalized hot size -/

noncomputable section

open MeasureTheory Set
open BoltzmannNonuniqueness.WeightedLocal
open BoltzmannNonuniqueness.WeightedLocalControl

namespace BoltzmannNonuniqueness.JetCopyDatum

theorem CapApproximation.cap_time {s₀ η K α γ d₀ q T : ℝ} {N : ℕ}
    (F : CapApproximation s₀ η K α γ d₀ q T N)
    (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8) (hη : 0 < η) (hηmax : η ≤ Real.log 2)
    (hK : 0 ≤ K) (hd₀ : 0 ≤ d₀) (hq : q < 2) (hT : 0 ≤ T) :
    ∃ t ∈ Icc 0 T,
      PhaseEssSup.size (fun p => F.solution.value (t,p)-
        ∑' i, rebuiltColdFamily q (N+1) (damping q (N+1) F.amplitude) T
          F.solution.value (color s₀ η K α γ d₀ q N) i (t,p)) =
        t+DatumBounds.scale s₀ η (N+1) := by
  have hδ := DatumBounds.scale_pos (η := η) hs₀ (N+1)
  have hδone : DatumBounds.scale s₀ η (N+1) ≤ 1 := by
    have h := JetGeometry.scale_antitone hs₀.le hη.le (Nat.zero_le (N+1))
    rw [show DatumBounds.scale s₀ η 0 = s₀ by simp [DatumBounds.scale]] at h
    linarith
  have hh₀ (p) : 0 ≤ F.coefficient*HotSeedProfile.normalized q (DatumBounds.scale s₀ η (N+1)) p :=
    mul_nonneg F.coefficient_mem.1 ((HotSeedProfile.normalized_bounds hδ hδone q).choose_spec.2 p).1
  have hi := initial_color_bounds hs₀ hsmax hη hηmax hK hd₀ α γ q N hh₀
  have hc₀ (i) (p) : 0 ≤ color s₀ η K α γ d₀ q N i p ∧
      color s₀ η K α γ d₀ q N i p ≤ 2*F.amplitude :=
    ⟨(hi.1 i p).1,(hi.1 i p).2.trans (F.initial_bound p)⟩
  have hreg := rebuilt_hot_continuous hq (by positivity : 0 ≤ (N+1:ℝ))
    (bounds (by positivity) F.amplitude_pos).1 hT
    (mul_nonneg (by norm_num) F.amplitude_pos.le)
    le_rfl F.solution.measurable_value
    ((measurable_seed s₀ η K α γ d₀ q N).add
      ((HotSeedProfile.normalized_measurable q _).const_mul F.coefficient))
    (measurable_color s₀ η K α γ d₀ q N) F.solution.value_bounds F.initial_bound hc₀ hi.2
    (F.solution.all_mild hT)
  obtain ⟨t,ht,he,_⟩ := Cap.peak_attained hT hδ hreg
  refine ⟨t,ht,?_⟩
  have hratio : PhaseEssSup.size (fun p => F.solution.value (t,p)-
        ∑' i, rebuiltColdFamily q (N+1) (damping q (N+1) F.amplitude) T
          F.solution.value (color s₀ η K α γ d₀ q N) i (t,p)) /
      (t+DatumBounds.scale s₀ η (N+1)) = 1 := he.symm.trans F.cap
  simpa only [one_mul] using
    (div_eq_iff (Cap.dilation_radius_pos ht.1 hδ).ne').mp hratio

end BoltzmannNonuniqueness.JetCopyDatum

end

end

section

/-! # Attained times and dilation radii for the actual shrinking cap shots -/

noncomputable section

open MeasureTheory Filter Set
open scoped Topology
open BoltzmannNonuniqueness.WeightedLocal
open BoltzmannNonuniqueness.WeightedLocalControl

namespace BoltzmannNonuniqueness.JetCopyDatum

def CapApproximation.hotSize {s₀ η K α γ d₀ q T : ℝ} {N : ℕ}
    (F : CapApproximation s₀ η K α γ d₀ q T N) (t : ℝ) : ℝ :=
  PhaseEssSup.size (fun p => F.solution.value (t,p)-
    ∑' i, rebuiltColdFamily q (N+1) (damping q (N+1) F.amplitude) T
      F.solution.value (color s₀ η K α γ d₀ q N) i (t,p))

structure AttainedCapSequence {s₀ η K α γ d₀ q : ℝ}
    (F : ShrinkingCapFamily s₀ η K α γ d₀ q) where
  time : ℕ → ℝ
  time_mem : ∀ n, time n ∈ Icc 0 (shrinkingHorizon F.horizonScale n)
  attained : ∀ n, (F.approximation n).hotSize (time n) =
    time n+DatumBounds.scale s₀ η (F.indices n+1)

theorem exists_attained_cap_sequence {s₀ η K α γ d₀ q : ℝ}
    (F : ShrinkingCapFamily s₀ η K α γ d₀ q)
    (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8) (hη : 0 < η) (hηmax : η ≤ Real.log 2)
    (hK : 0 ≤ K) (hd₀ : 0 ≤ d₀) (hq : q < 2) : Nonempty (AttainedCapSequence F) := by
  have hex (n : ℕ) : ∃ t ∈ Icc 0 (shrinkingHorizon F.horizonScale n),
      (F.approximation n).hotSize t = t+DatumBounds.scale s₀ η (F.indices n+1) :=
    (F.approximation n).cap_time hs₀ hsmax hη hηmax hK hd₀ hq
      (shrinkingHorizon_pos F.horizonScale_pos n).le
  choose t ht he using hex
  exact ⟨⟨t,ht,he⟩⟩

namespace AttainedCapSequence

variable {s₀ η K α γ d₀ q : ℝ} {F : ShrinkingCapFamily s₀ η K α γ d₀ q}

def radius (S : AttainedCapSequence F) (n : ℕ) : ℝ :=
  S.time n+DatumBounds.scale s₀ η (F.indices n+1)

def coldFraction (S : AttainedCapSequence F) (n : ℕ) : ℝ :=
  DatumBounds.scale s₀ η (F.indices n+1)/S.radius n

theorem radius_pos (S : AttainedCapSequence F) (hs₀ : 0 < s₀) (n : ℕ) : 0 < S.radius n :=
  Cap.dilation_radius_pos (S.time_mem n).1 (DatumBounds.scale_pos hs₀ _)

theorem radius_tendsto_zero (S : AttainedCapSequence F) (hs₀ : 0 < s₀) :
    Tendsto S.radius atTop (𝓝 0) :=
  Cap.dilation_radius_tendsto_zero (shrinkingHorizon_pos F.horizonScale_pos) S.time_mem
    (fun n => DatumBounds.scale_pos hs₀ (F.indices n+1))
    (shrinkingHorizon_tendsto_zero F.horizonScale) F.cold_ratio_tendsto

theorem coldFraction_mem (S : AttainedCapSequence F) (hs₀ : 0 < s₀) (n : ℕ) :
    S.coldFraction n ∈ Icc (0:ℝ) 1 :=
  Cap.cold_fraction_mem (S.time_mem n).1 (DatumBounds.scale_pos hs₀ _)

theorem normalized_time (S : AttainedCapSequence F) (hs₀ : 0 < s₀) (n : ℕ) :
    S.time n/S.radius n = 1-S.coldFraction n :=
  Cap.normalized_cap_time (S.time_mem n).1 (DatumBounds.scale_pos hs₀ _)

theorem fraction_subsequence (S : AttainedCapSequence F) (hs₀ : 0 < s₀) :
    ∃ l ∈ Icc (0:ℝ) 1, ∃ κ : ℕ → ℕ, StrictMono κ ∧
      Tendsto (fun n => S.coldFraction (κ n)) atTop (𝓝 l) :=
  isCompact_Icc.tendsto_subseq (fun n => S.coldFraction_mem hs₀ n)

theorem horizon_limit_ge_one (S : AttainedCapSequence F) (hs₀ : 0 < s₀) {U : ℝ}
    (hU : Tendsto (fun n => shrinkingHorizon F.horizonScale n/S.radius n) atTop (𝓝 U)) :
    1 ≤ U :=
  Cap.normalized_horizon_limit_ge_one (shrinkingHorizon_pos F.horizonScale_pos) S.time_mem
    (fun n => DatumBounds.scale_pos hs₀ (F.indices n+1)) F.cold_ratio_tendsto hU

end AttainedCapSequence
end BoltzmannNonuniqueness.JetCopyDatum

end

end

section

/-! # A common subsequence for the cold scale, mesh phase and time domain -/

noncomputable section

open Filter Set
open scoped Topology ENNReal

namespace BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

variable {s₀ η K α γ d₀ q : ℝ} {F : ShrinkingCapFamily s₀ η K α γ d₀ q}

def normalizedHorizon (S : AttainedCapSequence F) (n : ℕ) : ℝ≥0∞ :=
  ENNReal.ofReal (shrinkingHorizon F.horizonScale n/S.radius n)

private theorem lower_horizon_tendsto {ε : ℕ → ℝ} (hε : Tendsto ε atTop (𝓝 0)) :
    Tendsto (fun n => ENNReal.ofReal (1/(1+ε n))) atTop (𝓝 (1:ℝ≥0∞)) := by
  have hden : Tendsto (fun n => 1+ε n) atTop (𝓝 (1:ℝ)) := by
    simpa only [add_zero] using tendsto_const_nhds.add hε
  have h := (tendsto_const_nhds (x := (1:ℝ))).div hden one_ne_zero
  change Tendsto (fun n => 1/(1+ε n)) atTop (𝓝 ((1:ℝ)/1)) at h
  have hr : Tendsto (fun n => 1/(1+ε n)) atTop (𝓝 (1:ℝ)) := by simpa only [one_div_one] using h
  have hE := (ENNReal.continuous_ofReal.tendsto 1).comp hr
  change Tendsto (fun n => ENNReal.ofReal (1/(1+ε n))) atTop (𝓝 (ENNReal.ofReal 1)) at hE
  simpa only [ENNReal.ofReal_one] using hE

theorem joint_subsequence (S : AttainedCapSequence F) (hs₀ : 0 < s₀) (hη : 0 < η) :
    ∃ l ∈ Icc (0:ℝ) 1, ∃ θ ∈ Icc 1 (Real.exp η), ∃ U : ℝ≥0∞, 1 ≤ U ∧
      ∃ κ : ℕ → ℕ, StrictMono κ ∧
        Tendsto (fun n => S.coldFraction (κ n)) atTop (𝓝 l) ∧
        Tendsto (fun n => GeometricMesh.phase (s₀/S.radius (κ n)) η) atTop (𝓝 θ) ∧
        Tendsto (fun n => S.normalizedHorizon (κ n)) atTop (𝓝 U) := by
  let A : Set (ℝ × (ℝ × ℝ≥0∞)) := (Icc (0:ℝ) 1).prod ((Icc 1 (Real.exp η)).prod univ)
  have hA : IsCompact A := isCompact_Icc.prod (isCompact_Icc.prod isCompact_univ)
  have hmem (n) : (S.coldFraction n,(GeometricMesh.phase (s₀/S.radius n) η,S.normalizedHorizon n)) ∈ A :=
    ⟨S.coldFraction_mem hs₀ n,GeometricMesh.phase_bounds hη _,mem_univ _⟩
  obtain ⟨p,hp,κ,hκ,hlim⟩ := hA.tendsto_subseq hmem
  change Tendsto (fun n => (S.coldFraction (κ n),
    (GeometricMesh.phase (s₀/S.radius (κ n)) η,S.normalizedHorizon (κ n)))) atTop (𝓝 p) at hlim
  have hl : Tendsto (fun n => S.coldFraction (κ n)) atTop (𝓝 p.1) := hlim.fst_nhds
  have hθ : Tendsto (fun n => GeometricMesh.phase (s₀/S.radius (κ n)) η) atTop (𝓝 p.2.1) :=
    hlim.snd_nhds.fst_nhds
  have hU : Tendsto (fun n => S.normalizedHorizon (κ n)) atTop (𝓝 p.2.2) := hlim.snd_nhds.snd_nhds
  refine ⟨p.1,hp.1,p.2.1,hp.2.1,p.2.2,?_,κ,hκ,hl,hθ,hU⟩
  have hlo := (lower_horizon_tendsto F.cold_ratio_tendsto).comp hκ.tendsto_atTop
  apply le_of_tendsto_of_tendsto' hlo hU
  intro n
  exact ENNReal.ofReal_le_ofReal (Cap.normalized_horizon_lower
    (shrinkingHorizon_pos F.horizonScale_pos (κ n)) (S.time_mem (κ n))
    (DatumBounds.scale_pos hs₀ (F.indices (κ n)+1)))

end BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

end

end

section

/-! # Positivity, measurability and cap bounds of the actual hot remainder -/

noncomputable section

open MeasureTheory Set
open BoltzmannNonuniqueness.WeightedLocal
open BoltzmannNonuniqueness.WeightedLocalControl

namespace BoltzmannNonuniqueness.JetCopyDatum

def CapApproximation.hot {s₀ η K α γ d₀ q T : ℝ} {N : ℕ}
    (F : CapApproximation s₀ η K α γ d₀ q T N) (u : ℝ × JetPrototype.Phase) : ℝ :=
  F.solution.value u-∑' i, rebuiltColdFamily q (N+1) (damping q (N+1) F.amplitude) T
    F.solution.value (color s₀ η K α γ d₀ q N) i u

theorem CapApproximation.hot_properties {s₀ η K α γ d₀ q T : ℝ} {N : ℕ}
    (F : CapApproximation s₀ η K α γ d₀ q T N)
    (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8) (hη : 0 < η) (hηmax : η ≤ Real.log 2)
    (hK : 0 ≤ K) (hd₀ : 0 ≤ d₀) (hq : q < 2) (hT : 0 ≤ T) :
    Measurable F.hot ∧ (∀ u, 0 ≤ F.hot u) ∧
      ∀ t ∈ Icc 0 T, ∀ᵐ p ∂FlightMeasure.phaseVolume,
        F.hot (t,p) ≤ t+DatumBounds.scale s₀ η (N+1) := by
  have hδ := DatumBounds.scale_pos (η := η) hs₀ (N+1)
  have hδone : DatumBounds.scale s₀ η (N+1) ≤ 1 := by
    have h := JetGeometry.scale_antitone hs₀.le hη.le (Nat.zero_le (N+1))
    rw [show DatumBounds.scale s₀ η 0 = s₀ by simp [DatumBounds.scale]] at h
    linarith
  have hh₀ (p) : 0 ≤ F.coefficient*HotSeedProfile.normalized q (DatumBounds.scale s₀ η (N+1)) p :=
    mul_nonneg F.coefficient_mem.1 ((HotSeedProfile.normalized_bounds hδ hδone q).choose_spec.2 p).1
  have hi := initial_color_bounds hs₀ hsmax hη hηmax hK hd₀ α γ q N hh₀
  have hc₀ (i) (p) : 0 ≤ color s₀ η K α γ d₀ q N i p ∧
      color s₀ η K α γ d₀ q N i p ≤ 2*F.amplitude :=
    ⟨(hi.1 i p).1,(hi.1 i p).2.trans (F.initial_bound p)⟩
  have hL : 0 ≤ damping q (N+1) F.amplitude :=
    (bounds (q := q) (by positivity : 0 ≤ (N+1:ℝ)) F.amplitude_pos).1
  have hR : 0 ≤ 2*F.amplitude := mul_nonneg (by norm_num) F.amplitude_pos.le
  have hp := rebuiltColdFamily_properties hq (by positivity : 0 ≤ (N+1:ℝ)) hL hT hR le_rfl
    F.solution.measurable_value (measurable_color s₀ η K α γ d₀ q N)
    F.solution.value_bounds hc₀ hi.2 (F.solution.all_mild hT)
  have hhot := family_hot_bounds hq (by positivity : 0 ≤ (N+1:ℝ)) hR le_rfl
    F.solution.measurable_value hp.1 F.solution.value_bounds
    (fun i u => (hp.2.1 i u).1) hp.2.2.1
  refine ⟨hhot.1,fun u => (hhot.2.1 u).1,?_⟩
  exact PeriodicMildState.hot_bound_of_cap hq (by positivity : 0 ≤ (N+1:ℝ)) hL hT hR hδ le_rfl
    ((measurable_seed s₀ η K α γ d₀ q N).add
      ((HotSeedProfile.normalized_measurable q _).const_mul F.coefficient))
    F.initial_bound (measurable_color s₀ η K α γ d₀ q N) hc₀ hi.2 F.solution F.cap.le

end BoltzmannNonuniqueness.JetCopyDatum

end

end

section

/-! # Continuous essential size and the exact cap of a finite hot profile -/

noncomputable section

open MeasureTheory Set
open BoltzmannNonuniqueness.WeightedLocal BoltzmannNonuniqueness.WeightedLocalControl

namespace BoltzmannNonuniqueness.JetCopyDatum

theorem CapApproximation.hot_regular {s₀ η K α γ d₀ q T : ℝ} {N : ℕ}
    (F : CapApproximation s₀ η K α γ d₀ q T N)
    (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8) (hη : 0 < η) (hηmax : η ≤ Real.log 2)
    (hK : 0 ≤ K) (hd₀ : 0 ≤ d₀) (hq : q < 2) (hT : 0 ≤ T) :
    Continuous (fun t => PhaseEssSup.size (fun p => F.hot (t,p))) ∧
      ∀ t ∈ Icc 0 T, PhaseEssSup.size (fun p => F.hot (t,p)) ≤
        t+DatumBounds.scale s₀ η (N+1) := by
  have hδ := DatumBounds.scale_pos (η := η) hs₀ (N+1)
  have hδone : DatumBounds.scale s₀ η (N+1) ≤ 1 := by
    have h := JetGeometry.scale_antitone hs₀.le hη.le (Nat.zero_le (N+1))
    rw [show DatumBounds.scale s₀ η 0 = s₀ by simp [DatumBounds.scale]] at h
    linarith
  have hh₀ (p) : 0 ≤ F.coefficient*HotSeedProfile.normalized q (DatumBounds.scale s₀ η (N+1)) p :=
    mul_nonneg F.coefficient_mem.1 ((HotSeedProfile.normalized_bounds hδ hδone q).choose_spec.2 p).1
  have hi := initial_color_bounds hs₀ hsmax hη hηmax hK hd₀ α γ q N hh₀
  have hc₀ (i) (p) : 0 ≤ color s₀ η K α γ d₀ q N i p ∧
      color s₀ η K α γ d₀ q N i p ≤ 2*F.amplitude :=
    ⟨(hi.1 i p).1,(hi.1 i p).2.trans (F.initial_bound p)⟩
  have hL : 0 ≤ damping q (N+1) F.amplitude :=
    (bounds (q := q) (by positivity : 0 ≤ (N+1:ℝ)) F.amplitude_pos).1
  have hR : 0 ≤ 2*F.amplitude := mul_nonneg (by norm_num) F.amplitude_pos.le
  have hreg := rebuilt_hot_continuous hq (by positivity : 0 ≤ (N+1:ℝ)) hL hT hR le_rfl
    F.solution.measurable_value
    ((measurable_seed s₀ η K α γ d₀ q N).add
      ((HotSeedProfile.normalized_measurable q _).const_mul F.coefficient))
    (measurable_color s₀ η K α γ d₀ q N) F.solution.value_bounds F.initial_bound hc₀ hi.2
    (F.solution.all_mild hT)
  have hclamp (t : ℝ) : (fun p => F.hot (PositiveIntegral.time T t,p)) =
      (fun p => F.hot (t,p)) := by
    funext p
    unfold CapApproximation.hot
    rw [F.solution.clamped (t,p)]
    congr 1
    apply tsum_congr
    intro i
    exact rebuiltColdFamily_time_clamp hT q (N+1) (damping q (N+1) F.amplitude)
      F.solution.clamped (color s₀ η K α γ d₀ q N) i (t,p)
  have hcont := hreg.comp_continuous
    (show Continuous (PositiveIntegral.time T) by unfold PositiveIntegral.time; fun_prop)
    (fun t => PositiveIntegral.time_bounds hT t)
  change Continuous (fun t => PhaseEssSup.size (fun p => F.hot (PositiveIntegral.time T t,p))) at hcont
  refine ⟨?_,?_⟩
  · simpa only [hclamp] using hcont
  · obtain ⟨_,_,_,hpeak⟩ := Cap.peak_attained hT hδ hreg
    intro t ht
    exact (div_le_one (by linarith [ht.1] : 0 < t+DatumBounds.scale s₀ η (N+1))).mp
      ((hpeak t ht).trans F.cap.le)

end BoltzmannNonuniqueness.JetCopyDatum

end

end

section

/-! # Damping-free source bound for the actual finite cap solution -/

noncomputable section

open MeasureTheory Set
open BoltzmannNonuniqueness.WeightedLocal BoltzmannNonuniqueness.WeightedLocalControl

namespace BoltzmannNonuniqueness.JetCopyDatum

def CapApproximation.hotNetSource {s₀ η K α γ d₀ q T : ℝ} {N : ℕ}
    (F : CapApproximation s₀ η K α γ d₀ q T N) (u : ℝ × JetPrototype.Phase) : ℝ :=
  remainderForcing q (N+1) (damping q (N+1) F.amplitude) F.solution.value
    (rebuilt s₀ η K α γ d₀ q (N+1) (damping q (N+1) F.amplitude) T N F.solution.value) u-
      damping q (N+1) F.amplitude*F.hot u

theorem CapApproximation.hot_net_source_bound (hcarleman : Published.GPV2009CarlemanInput)
    {s₀ η K α γ d₀ q T : ℝ} {N : ℕ} (F : CapApproximation s₀ η K α γ d₀ q T N)
    (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8) (hη : 0 < η) (hηmax : η ≤ Real.log 2)
    (hK : 0 ≤ K) (hα : 0 < α) (hαmax : α ≤ 1) (hγ : 0 < γ)
    (hd₀ : 0 < d₀) (hd₀max : d₀ ≤ 1)
    (hsmall : JetComparisonCoefficient.coefficient K*d₀*s₀^9 ≤ 1)
    (hq₁ : 1 < q) (hq₂ : q < 2) (hT : 0 ≤ T) (hTmax : T ≤ 1/32) (A : ℝ)
    (htail : ∀ t ∈ Ioc 0 T,
      JetEscapedEnvelope.constant s₀ η α K d₀ (JetEscapedEnvelope.exponent A)*t^A ≤ 1) :
    ∀ᵐ u ∂spacetimeVolume, u.1 ∈ Ioc 0 T → F.hotNetSource u ≤
      scalarMajorant s₀ η K α γ d₀ q A N u.1 (PhaseEssSup.size (fun p => F.hot (u.1,p))) := by
  have hδ := DatumBounds.scale_pos (η := η) hs₀ (N+1)
  have hδone : DatumBounds.scale s₀ η (N+1) ≤ 1 := by
    have h := JetGeometry.scale_antitone hs₀.le hη.le (Nat.zero_le (N+1))
    rw [show DatumBounds.scale s₀ η 0 = s₀ by simp [DatumBounds.scale]] at h
    linarith
  have hh₀ (p) : 0 ≤ F.coefficient*HotSeedProfile.normalized q (DatumBounds.scale s₀ η (N+1)) p :=
    mul_nonneg F.coefficient_mem.1 ((HotSeedProfile.normalized_bounds hδ hδone q).choose_spec.2 p).1
  have hi := initial_color_bounds hs₀ hsmax hη hηmax hK hd₀.le α γ q N hh₀
  have hc₀ (i) (p) : 0 ≤ color s₀ η K α γ d₀ q N i p ∧
      color s₀ η K α γ d₀ q N i p ≤ 2*F.amplitude :=
    ⟨(hi.1 i p).1,(hi.1 i p).2.trans (F.initial_bound p)⟩
  have hL : 0 ≤ damping q (N+1) F.amplitude :=
    (bounds (q := q) (by positivity : 0 ≤ (N+1:ℝ)) F.amplitude_pos).1
  have hR : 0 ≤ 2*F.amplitude := mul_nonneg (by norm_num) F.amplitude_pos.le
  have hp := rebuiltColdFamily_properties hq₂ (by positivity : 0 ≤ (N+1:ℝ)) hL hT hR le_rfl
    F.solution.measurable_value (measurable_color s₀ η K α γ d₀ q N)
    F.solution.value_bounds hc₀ hi.2 (F.solution.all_mild hT)
  exact geometric_hot_net_source hcarleman hs₀ hsmax hη hηmax hK hα hαmax hγ hd₀ hd₀max
    hsmall hq₁ hq₂ hTmax A N F.solution.measurable_value hp.1 F.solution.value_bounds
    (fun i u => (hp.2.1 i u).1) hp.2.2.1
    (rebuilt_zero s₀ η K α γ d₀ q (N+1) (damping q (N+1) F.amplitude) T N
      (fun u => (F.solution.value_bounds u).1))
    (fun t ht i x w => rebuilt_envelope hs₀ hsmax hη hηmax hK hα.le hγ.le hd₀ hsmall
      hq₂ (by positivity) hL hT hR (hTmax.trans (by norm_num)) le_rfl N hh₀
      F.solution.measurable_value F.solution.value_bounds F.initial_bound i ht
      (JetPeriodicDatum.spatialMap x,w))
    F.solution.periodic (fun n i => rebuilt_shift n (F.solution.periodic n) i)
    (F.hot_regular hs₀ hsmax hη hηmax hK hd₀.le hq₂ hT).1.measurable htail

end BoltzmannNonuniqueness.JetCopyDatum

end

end

section

/-! # A cutoff-independent upper bound for the actual hot net source -/

noncomputable section

open MeasureTheory Set

namespace BoltzmannNonuniqueness.JetCopyDatum

theorem CapApproximation.hot_net_source_cap (hcarleman : Published.GPV2009CarlemanInput)
    {s₀ η K α γ d₀ q T : ℝ} {N : ℕ} (F : CapApproximation s₀ η K α γ d₀ q T N)
    (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8) (hη : 0 < η) (hηmax : η ≤ Real.log 2)
    (hK : 0 ≤ K) (hα : 0 < α) (hαmax : α ≤ 1) (hγ : 0 < γ)
    (hd₀ : 0 < d₀) (hd₀max : d₀ ≤ 1)
    (hsmall : JetComparisonCoefficient.coefficient K*d₀*s₀^9 ≤ 1)
    (hq₁ : 1 < q) (hq₂ : q < 2) (hT : 0 ≤ T) (hTmax : T ≤ 1/32) (m : ℕ)
    (htail : JetEscapedEnvelope.constant s₀ η α K d₀
      (JetEscapedEnvelope.exponent (m+1 : ℕ))*T^(m+1) ≤ 1) :
    ∀ᵐ u ∂WeightedLocal.spacetimeVolume, u.1 ∈ Ioc 0 T → F.hotNetSource u ≤
      2*JetMainGain.coefficient K α γ q+
      2*HotApplication.realBound q*(u.1+DatumBounds.scale s₀ η (N+1))^2+
      (2*JetMainGain.coefficient K α γ q+2*HotApplication.realBound q)*
        JetEscapedEnvelope.constant s₀ η α K d₀
          (JetEscapedEnvelope.exponent (m+1 : ℕ))*u.1^m := by
  have he := JetEscapedEnvelope.constant_nonneg hs₀ hK hd₀ η α
    (JetEscapedEnvelope.exponent (m+1 : ℕ))
  have htail' (t : ℝ) (ht : t ∈ Ioc 0 T) :
      JetEscapedEnvelope.constant s₀ η α K d₀
        (JetEscapedEnvelope.exponent (m+1 : ℕ))*t^(m+1 : ℕ) ≤ 1 :=
    tail_small he ht.1.le ht.2 htail
  have hb := F.hot_net_source_bound hcarleman hs₀ hsmax hη hηmax hK hα hαmax hγ
    hd₀ hd₀max hsmall hq₁ hq₂ hT hTmax (m+1 : ℕ)
    (by simpa only [Real.rpow_natCast] using htail')
  have hc := (F.hot_regular hs₀ hsmax hη hηmax hK hd₀.le hq₂ hT).2
  filter_upwards [hb] with u hu hut
  apply (hu hut).trans
  rw [scalarMajorant_eq_source s₀ η K α γ d₀ q N m hut.1]
  simpa only [JetGeometry.jetScale] using ZeroProfile.source_le_cap
    (mul_nonneg (by norm_num) (JetMainGain.coefficient_nonneg hK α γ q))
    (mul_nonneg (by norm_num) (HotApplication.realBound_pos q).le)
    (DatumBounds.scale_pos hs₀ (N+1)) hut.1.le (PhaseEssSup.size_nonneg _)
    (hc u.1 ⟨hut.1.le,hut.2⟩) m

end BoltzmannNonuniqueness.JetCopyDatum

end

end

section

/-! # Every compact subinterval of the limiting horizon is eventually available -/

noncomputable section

open Filter Set
open scoped Topology ENNReal

namespace BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

variable {s₀ η K α γ d₀ q : ℝ} {F : ShrinkingCapFamily s₀ η K α γ d₀ q}

theorem eventually_scaled_slab (S : AttainedCapSequence F) (hs₀ : 0 < s₀)
    {κ : ℕ → ℕ} {U : ℝ≥0∞}
    (hU : Tendsto (fun n => S.normalizedHorizon (κ n)) atTop (𝓝 U))
    {A : ℝ} (hA : ENNReal.ofReal A < U) :
    ∀ᶠ n in atTop, ∀ t ∈ Icc (0:ℝ) A,
      S.radius (κ n)*t ∈ Icc 0 (shrinkingHorizon F.horizonScale (κ n)) := by
  filter_upwards [hU.eventually (lt_mem_nhds hA)] with n hn
  have hR := S.radius_pos hs₀ (κ n)
  have hT := shrinkingHorizon_pos F.horizonScale_pos (κ n)
  have hquot : A < shrinkingHorizon F.horizonScale (κ n)/S.radius (κ n) :=
    (ENNReal.ofReal_lt_ofReal_iff (div_pos hT hR)).mp hn
  have htime : S.radius (κ n)*A < shrinkingHorizon F.horizonScale (κ n) := by
    have h := (lt_div_iff₀ hR).mp hquot
    simpa only [mul_comm] using h
  intro t ht
  exact ⟨mul_nonneg hR.le ht.1,
    (mul_le_mul_of_nonneg_left ht.2 hR.le).trans htime.le⟩

theorem eventually_scaled_time (S : AttainedCapSequence F) (hs₀ : 0 < s₀)
    {κ : ℕ → ℕ} {U : ℝ≥0∞}
    (hU : Tendsto (fun n => S.normalizedHorizon (κ n)) atTop (𝓝 U))
    {t : ℝ} (ht : 0 < t) (htU : ENNReal.ofReal t < U) :
    ∀ᶠ n in atTop, S.radius (κ n)*t ∈ Ioc 0 (shrinkingHorizon F.horizonScale (κ n)) := by
  filter_upwards [S.eventually_scaled_slab hs₀ hU htU] with n hn
  exact ⟨mul_pos (S.radius_pos hs₀ _) ht,(hn t ⟨ht.le,le_rfl⟩).2⟩

end BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

end

end

section

/-! # Physical hot densities under the attained cap dilation -/

noncomputable section

open MeasureTheory Filter Set
open scoped Topology ENNReal
open BoltzmannNonuniqueness.VelocityWeight

namespace BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

variable {s₀ η K α γ d₀ q : ℝ} {F : ShrinkingCapFamily s₀ η K α γ d₀ q}

def rescaledHot (S : AttainedCapSequence F) (n : ℕ) (u : ℝ × JetPrototype.Phase) : ℝ :=
  H q u.2.2 * (F.approximation n).hot
    (S.radius n*u.1,(S.radius n • u.2.1,u.2.2)) / S.radius n

theorem rescaledHot_measurable (S : AttainedCapSequence F)
    (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8) (hη : 0 < η) (hηmax : η ≤ Real.log 2)
    (hK : 0 ≤ K) (hd₀ : 0 ≤ d₀) (hq : q < 2) (n : ℕ) :
    Measurable (S.rescaledHot n) := by
  have hm := ((F.approximation n).hot_properties hs₀ hsmax hη hηmax hK hd₀ hq
    (shrinkingHorizon_pos F.horizonScale_pos n).le).1
  have hc : Measurable (fun u : ℝ × JetPrototype.Phase =>
      (S.radius n*u.1,(S.radius n • u.2.1,u.2.2))) := by fun_prop
  exact (((ChartKernel.measurable_H q).comp measurable_snd.snd).mul (hm.comp hc)).div_const _

theorem rescaledHot_nonneg (S : AttainedCapSequence F)
    (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8) (hη : 0 < η) (hηmax : η ≤ Real.log 2)
    (hK : 0 ≤ K) (hd₀ : 0 ≤ d₀) (hq : q < 2) (n : ℕ) (u : ℝ × JetPrototype.Phase) :
    0 ≤ S.rescaledHot n u := by
  have hp := ((F.approximation n).hot_properties hs₀ hsmax hη hηmax hK hd₀ hq
    (shrinkingHorizon_pos F.horizonScale_pos n).le).2.1
  exact div_nonneg (mul_nonneg (H_nonneg q _) (hp _)) (S.radius_pos hs₀ n).le

theorem rescaledHot_bound_at (S : AttainedCapSequence F)
    (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8) (hη : 0 < η) (hηmax : η ≤ Real.log 2)
    (hK : 0 ≤ K) (hd₀ : 0 ≤ d₀) (hq : q < 2) (n : ℕ) {t : ℝ}
    (ht : S.radius n*t ∈ Icc 0 (shrinkingHorizon F.horizonScale n)) :
    ∀ᵐ p ∂FlightMeasure.phaseVolume,
      S.rescaledHot n (t,p) ≤ (t+S.coldFraction n)*H q p.2 := by
  have hb := ((F.approximation n).hot_properties hs₀ hsmax hη hηmax hK hd₀ hq
    (shrinkingHorizon_pos F.horizonScale_pos n).le).2.2 _ ht
  have hr := S.radius_pos hs₀ n
  filter_upwards [(ColdDilationMeasure.spatial_dilation_quasiMeasurePreserving hr).ae hb]
    with p hp
  calc
    S.rescaledHot n (t,p) ≤ H q p.2 *
        (S.radius n*t+DatumBounds.scale s₀ η (F.indices n+1))/S.radius n :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hp (H_nonneg q _)) hr.le
    _ = (t+S.coldFraction n)*H q p.2 := by
      unfold coldFraction
      field_simp

theorem eventually_rescaledHot_bound (S : AttainedCapSequence F)
    (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8) (hη : 0 < η) (hηmax : η ≤ Real.log 2)
    (hK : 0 ≤ K) (hd₀ : 0 ≤ d₀) (hq : q < 2) {κ : ℕ → ℕ} {U : ℝ≥0∞}
    (hU : Tendsto (fun n => S.normalizedHorizon (κ n)) atTop (𝓝 U))
    {A : ℝ} (hA : ENNReal.ofReal A < U) :
    ∀ᶠ n in atTop, ∀ t ∈ Icc (0:ℝ) A, ∀ᵐ p ∂FlightMeasure.phaseVolume,
      S.rescaledHot (κ n) (t,p) ≤ (A+1)*H q p.2 := by
  filter_upwards [S.eventually_scaled_slab hs₀ hU hA] with n hn
  intro t ht
  filter_upwards [S.rescaledHot_bound_at hs₀ hsmax hη hηmax hK hd₀ hq (κ n) (hn t ht)]
    with p hp
  exact hp.trans (mul_le_mul_of_nonneg_right
    (add_le_add ht.2 (S.coldFraction_mem hs₀ _).2) (H_nonneg q _))

end BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

end

end

section

/-! # Zero extension of rescaled hot densities beyond their physical horizons -/

noncomputable section

open MeasureTheory Filter Set
open scoped Topology ENNReal
open BoltzmannNonuniqueness.VelocityWeight

namespace BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

variable {s₀ η K α γ d₀ q : ℝ} {F : ShrinkingCapFamily s₀ η K α γ d₀ q}

def hotTimeDomain (S : AttainedCapSequence F) (n : ℕ) : Set (ℝ × JetPrototype.Phase) :=
  {u | S.radius n*u.1 ∈ Icc 0 (shrinkingHorizon F.horizonScale n)}

theorem hotTimeDomain_measurable (S : AttainedCapSequence F) (n : ℕ) :
    MeasurableSet (S.hotTimeDomain n) :=
  measurableSet_Icc.preimage (measurable_const.mul measurable_fst)

def extendedHot (S : AttainedCapSequence F) (n : ℕ) : ℝ × JetPrototype.Phase → ℝ :=
  (S.hotTimeDomain n).indicator (S.rescaledHot n)

theorem extendedHot_measurable (S : AttainedCapSequence F)
    (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8) (hη : 0 < η) (hηmax : η ≤ Real.log 2)
    (hK : 0 ≤ K) (hd₀ : 0 ≤ d₀) (hq : q < 2) (n : ℕ) :
    Measurable (S.extendedHot n) :=
  (S.rescaledHot_measurable hs₀ hsmax hη hηmax hK hd₀ hq n).indicator
    (S.hotTimeDomain_measurable n)

theorem extendedHot_nonneg (S : AttainedCapSequence F)
    (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8) (hη : 0 < η) (hηmax : η ≤ Real.log 2)
    (hK : 0 ≤ K) (hd₀ : 0 ≤ d₀) (hq : q < 2) (n : ℕ) (u : ℝ × JetPrototype.Phase) :
    0 ≤ S.extendedHot n u :=
  indicator_nonneg (fun u _ => S.rescaledHot_nonneg hs₀ hsmax hη hηmax hK hd₀ hq n u) u

theorem extendedHot_bound_at (S : AttainedCapSequence F)
    (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8) (hη : 0 < η) (hηmax : η ≤ Real.log 2)
    (hK : 0 ≤ K) (hd₀ : 0 ≤ d₀) (hq : q < 2) (n : ℕ) {t : ℝ} (ht : 0 ≤ t) :
    ∀ᵐ p ∂FlightMeasure.phaseVolume,
      S.extendedHot n (t,p) ≤ (t+S.coldFraction n)*H q p.2 := by
  by_cases hmem : S.radius n*t ∈ Icc 0 (shrinkingHorizon F.horizonScale n)
  · simpa only [extendedHot,indicator_of_mem (show (t,_) ∈ S.hotTimeDomain n from hmem)]
      using S.rescaledHot_bound_at hs₀ hsmax hη hηmax hK hd₀ hq n hmem
  · filter_upwards [] with p
    rw [extendedHot,indicator_of_notMem (show (t,p) ∉ S.hotTimeDomain n from hmem)]
    exact mul_nonneg (add_nonneg ht (S.coldFraction_mem hs₀ n).1) (H_nonneg q _)

theorem extendedHot_uniform_bound_at (S : AttainedCapSequence F)
    (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8) (hη : 0 < η) (hηmax : η ≤ Real.log 2)
    (hK : 0 ≤ K) (hd₀ : 0 ≤ d₀) (hq : q < 2) (n : ℕ) {A t : ℝ}
    (ht : t ∈ Icc (0:ℝ) A) :
    ∀ᵐ p ∂FlightMeasure.phaseVolume, S.extendedHot n (t,p) ≤ (A+1)*H q p.2 := by
  filter_upwards [S.extendedHot_bound_at hs₀ hsmax hη hηmax hK hd₀ hq n ht.1] with p hp
  exact hp.trans (mul_le_mul_of_nonneg_right
    (add_le_add ht.2 (S.coldFraction_mem hs₀ n).2) (H_nonneg q _))

theorem eventually_extendedHot_eq (S : AttainedCapSequence F) (hs₀ : 0 < s₀)
    {κ : ℕ → ℕ} {U : ℝ≥0∞}
    (hU : Tendsto (fun n => S.normalizedHorizon (κ n)) atTop (𝓝 U))
    {A : ℝ} (hA : ENNReal.ofReal A < U) :
    ∀ᶠ n in atTop, ∀ t ∈ Icc (0:ℝ) A, ∀ p,
      S.extendedHot (κ n) (t,p) = S.rescaledHot (κ n) (t,p) := by
  filter_upwards [S.eventually_scaled_slab hs₀ hU hA] with n hn
  intro t ht p
  exact indicator_of_mem (show (t,p) ∈ S.hotTimeDomain (κ n) from hn t ht) _

end BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

end

end

section

/-! # Local uniform integrability of the actual dilated hot sequence -/

noncomputable section

open MeasureTheory Set
open scoped ENNReal
open BoltzmannNonuniqueness.VelocityWeight

namespace BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

abbrev HotKineticPhase := (ℝ × JetPrototype.Space) × Velocity

variable {s₀ η K α γ d₀ q : ℝ} {F : ShrinkingCapFamily s₀ η K α γ d₀ q}

def hotDensity (S : AttainedCapSequence F) (n : ℕ) (z : HotKineticPhase) : ℝ :=
  S.extendedHot n (z.1.1,(z.1.2,z.2))

def hotWindowVolume (A R : ℝ) : Measure HotKineticPhase :=
  ((volume.restrict (Icc (0:ℝ) A)).prod
    (volume.restrict (Metric.closedBall (0 : JetPrototype.Space) R))).prod volume

theorem hotDensity_measurable (S : AttainedCapSequence F)
    (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8) (hη : 0 < η) (hηmax : η ≤ Real.log 2)
    (hK : 0 ≤ K) (hd₀ : 0 ≤ d₀) (hq : q < 2) (n : ℕ) :
    Measurable (S.hotDensity n) :=
  (S.extendedHot_measurable hs₀ hsmax hη hηmax hK hd₀ hq n).comp
    (by fun_prop)

theorem hotDensity_nonneg (S : AttainedCapSequence F)
    (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8) (hη : 0 < η) (hηmax : η ≤ Real.log 2)
    (hK : 0 ≤ K) (hd₀ : 0 ≤ d₀) (hq : q < 2) (n : ℕ) (z : HotKineticPhase) :
    0 ≤ S.hotDensity n z :=
  S.extendedHot_nonneg hs₀ hsmax hη hηmax hK hd₀ hq n _

theorem hotDensity_bound (S : AttainedCapSequence F)
    (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8) (hη : 0 < η) (hηmax : η ≤ Real.log 2)
    (hK : 0 ≤ K) (hd₀ : 0 ≤ d₀) (hq : q < 2) (n : ℕ) (A R : ℝ) :
    ∀ᵐ z ∂hotWindowVolume A R, S.hotDensity n z ≤ (A+1)*H q z.2 := by
  let μt : Measure ℝ := volume.restrict (Icc (0:ℝ) A)
  let μx : Measure JetPrototype.Space := volume.restrict (Metric.closedBall 0 R)
  have hB : ∀ᵐ u ∂μt.prod (μx.prod volume),
      S.extendedHot n u ≤ (A+1)*H q u.2.2 := by
    apply (Measure.ae_prod_iff_ae_ae (measurableSet_le
      (S.extendedHot_measurable hs₀ hsmax hη hηmax hK hd₀ hq n)
      (((ChartKernel.measurable_H q).comp measurable_snd.snd).const_mul _))).mpr
    filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
    have hb := S.extendedHot_uniform_bound_at hs₀ hsmax hη hηmax hK hd₀ hq n ht
    have hab : μx.prod (volume : Measure Velocity) ≤ FlightMeasure.phaseVolume :=
      Measure.prod_mono Measure.restrict_le_self le_rfl
    exact hb.filter_mono (ae_mono hab)
  exact (measurePreserving_prodAssoc μt μx (volume : Measure Velocity)).quasiMeasurePreserving.ae hB

theorem hot_majorant_integrable {q : ℝ} (hq : q < 2) (A R : ℝ) :
    Integrable (fun z : HotKineticPhase => (A+1)*H q z.2) (hotWindowVolume A R) := by
  unfold hotWindowVolume
  have : IsFiniteMeasure ((volume : Measure JetPrototype.Space).restrict
      (Metric.closedBall 0 R)) :=
    isFiniteMeasure_restrict.mpr (isCompact_closedBall (0 : JetPrototype.Space) R).measure_lt_top.ne
  exact ((integrable_H hq).const_mul (A+1)).comp_snd _

theorem hotDensity_uniformIntegrable (S : AttainedCapSequence F)
    (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8) (hη : 0 < η) (hηmax : η ≤ Real.log 2)
    (hK : 0 ≤ K) (hd₀ : 0 ≤ d₀) (hq : q < 2) (A R : ℝ) :
    UniformIntegrable S.hotDensity 1 (hotWindowVolume A R) := by
  apply CollisionCompactness.uniformIntegrable_mono_nonneg
    (uniformIntegrable_const (by norm_num) (by norm_num)
      (memLp_one_iff_integrable.mpr (hot_majorant_integrable hq A R)))
    (fun n => (S.hotDensity_measurable hs₀ hsmax hη hηmax hK hd₀ hq n).aestronglyMeasurable)
    (fun n => ae_of_all _ (S.hotDensity_nonneg hs₀ hsmax hη hηmax hK hd₀ hq n))
  exact fun n => S.hotDensity_bound hs₀ hsmax hη hηmax hK hd₀ hq n A R

theorem hotDensity_unifTight (S : AttainedCapSequence F)
    (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8) (hη : 0 < η) (hηmax : η ≤ Real.log 2)
    (hK : 0 ≤ K) (hd₀ : 0 ≤ d₀) (hq : q < 2) {A : ℝ} (hA : 0 ≤ A) (R : ℝ) :
    UnifTight S.hotDensity 1 (hotWindowVolume A R) := by
  apply Compactness.unifTight_of_integrable_majorant (hot_majorant_integrable hq A R)
    (fun n => (S.hotDensity_measurable hs₀ hsmax hη hηmax hK hd₀ hq n).aestronglyMeasurable)
  intro n
  filter_upwards [S.hotDensity_bound hs₀ hsmax hη hηmax hK hd₀ hq n A R] with z hz
  apply enorm_le_iff_norm_le.mpr
  rw [Real.norm_of_nonneg (S.hotDensity_nonneg hs₀ hsmax hη hηmax hK hd₀ hq n z),
    Real.norm_of_nonneg (mul_nonneg (by linarith) (H_nonneg q _))]
  exact hz

end BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

end

end

section

/-! # Uniform integrability and tightness of the actual dilated hot pairs -/

noncomputable section

open MeasureTheory Filter Set
open scoped ENNReal

namespace BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

abbrev HotPairPhase := (ℝ × JetPrototype.Space) × (Velocity × Velocity)

def hotBaseWindowVolume (A R : ℝ) : Measure (ℝ × JetPrototype.Space) :=
  (volume.restrict (Icc (0:ℝ) A)).prod
    (volume.restrict (Metric.closedBall (0 : JetPrototype.Space) R))

def hotPairWindowVolume (A R : ℝ) : Measure HotPairPhase :=
  (hotBaseWindowVolume A R).prod volume

variable {s₀ η K α γ d₀ q : ℝ} {F : ShrinkingCapFamily s₀ η K α γ d₀ q}

theorem hotPair_bounds (S : AttainedCapSequence F)
    (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8) (hη : 0 < η) (hηmax : η ≤ Real.log 2)
    (hK : 0 ≤ K) (hd₀ : 0 ≤ d₀) (hq : q < 2) {A : ℝ} (hA : 0 ≤ A) (R : ℝ) :
    UniformIntegrable (fun n => CollisionCompactness.pairProduct (S.hotDensity n)) 1
      (hotPairWindowVolume A R) ∧
    UnifTight (fun n => CollisionCompactness.pairProduct (S.hotDensity n)) 1
      (hotPairWindowVolume A R) := by
  have : IsFiniteMeasure ((volume : Measure JetPrototype.Space).restrict
      (Metric.closedBall 0 R)) :=
    isFiniteMeasure_restrict.mpr (isCompact_closedBall (0 : JetPrototype.Space) R).measure_lt_top.ne
  have : IsFiniteMeasure (hotBaseWindowVolume A R) := by
    unfold hotBaseWindowVolume
    infer_instance
  have hm n := S.hotDensity_measurable hs₀ hsmax hη hηmax hK hd₀ hq n
  have hn n := S.hotDensity_nonneg hs₀ hsmax hη hηmax hK hd₀ hq n
  have hb n : ∀ᵐ x ∂hotBaseWindowVolume A R, ∀ᵐ v : Velocity,
      x ∉ (∅ : Set (ℝ × JetPrototype.Space)) →
        S.hotDensity n (x,v) ≤ (A+1)*VelocityWeight.H q v := by
    have ht := Measure.ae_ae_of_ae_prod
      (S.hotDensity_bound hs₀ hsmax hη hηmax hK hd₀ hq n A R)
    filter_upwards [ht] with x hx
    exact hx.mono (fun _ h _ => h)
  have hui := CollisionCompactness.outer_pairs_uniformIntegrable hq
    (by linarith : 0 ≤ A+1) MeasurableSet.empty hm hn hb
  have ht := CollisionCompactness.outer_pairs_unifTight hq
    (by linarith : 0 ≤ A+1) hm hn MeasurableSet.empty hb
  simp only [Compactness.outerCutoff,compl_empty,preimage_univ,indicator_univ] at hui ht
  exact ⟨CollisionCompactness.pairProduct_uniformIntegrable hm hn hui,
    CollisionCompactness.pairProduct_unifTight hm hn ht⟩

end BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

end

end

section

/-! # Compactness bounds for the hard-sphere weighted hot pair density -/

noncomputable section

open MeasureTheory Filter Set
open scoped ENNReal

namespace BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

variable {s₀ η K α γ d₀ q : ℝ} {F : ShrinkingCapFamily s₀ η K α γ d₀ q}

theorem hotWeightedPair_bounds (S : AttainedCapSequence F)
    (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8) (hη : 0 < η) (hηmax : η ≤ Real.log 2)
    (hK : 0 ≤ K) (hd₀ : 0 ≤ d₀) (hq : q < 2) {A : ℝ} (hA : 0 ≤ A) (R : ℝ) :
    UniformIntegrable (fun n => CollisionCompactness.pairDensity (S.hotDensity n)) 1
      (hotPairWindowVolume A R) ∧
    UnifTight (fun n => CollisionCompactness.pairDensity (S.hotDensity n)) 1
      (hotPairWindowVolume A R) := by
  have : IsFiniteMeasure ((volume : Measure JetPrototype.Space).restrict
      (Metric.closedBall 0 R)) :=
    isFiniteMeasure_restrict.mpr (isCompact_closedBall (0 : JetPrototype.Space) R).measure_lt_top.ne
  have : IsFiniteMeasure (hotBaseWindowVolume A R) := by
    unfold hotBaseWindowVolume
    infer_instance
  have hm n := S.hotDensity_measurable hs₀ hsmax hη hηmax hK hd₀ hq n
  have hn n := S.hotDensity_nonneg hs₀ hsmax hη hηmax hK hd₀ hq n
  have hb n : ∀ᵐ x ∂hotBaseWindowVolume A R, ∀ᵐ v : Velocity,
      x ∉ (∅ : Set (ℝ × JetPrototype.Space)) →
        S.hotDensity n (x,v) ≤ (A+1)*VelocityWeight.H q v := by
    have ht := Measure.ae_ae_of_ae_prod
      (S.hotDensity_bound hs₀ hsmax hη hηmax hK hd₀ hq n A R)
    filter_upwards [ht] with x hx
    exact hx.mono (fun _ h _ => h)
  have hui := CollisionCompactness.outer_pairs_uniformIntegrable hq
    (by linarith : 0 ≤ A+1) MeasurableSet.empty hm hn hb
  have ht := CollisionCompactness.outer_pairs_unifTight hq
    (by linarith : 0 ≤ A+1) hm hn MeasurableSet.empty hb
  simp only [Compactness.outerCutoff,compl_empty,preimage_univ,indicator_univ] at hui ht
  exact ⟨hui,ht⟩

end BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

end

end

section

/-! # The actual hot cap as a spacetime almost-everywhere estimate -/

noncomputable section

open MeasureTheory MeasureTheory.Measure Set
open BoltzmannNonuniqueness.WeightedLocal

namespace BoltzmannNonuniqueness.JetCopyDatum

theorem CapApproximation.hot_spacetime_cap {s₀ η K α γ d₀ q T : ℝ} {N : ℕ}
    (F : CapApproximation s₀ η K α γ d₀ q T N)
    (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8) (hη : 0 < η) (hηmax : η ≤ Real.log 2)
    (hK : 0 ≤ K) (hd₀ : 0 ≤ d₀) (hq : q < 2) (hT : 0 ≤ T) :
    ∀ᵐ u ∂spacetimeVolume, u.1 ∈ Icc 0 T →
      F.hot u ≤ u.1+DatumBounds.scale s₀ η (N+1) := by
  have hp := F.hot_properties hs₀ hsmax hη hηmax hK hd₀ hq hT
  have hm : MeasurableSet {u : ℝ × JetPrototype.Phase | u.1 ∈ Icc 0 T →
      F.hot u ≤ u.1+DatumBounds.scale s₀ η (N+1)} := by
    simp only [imp_iff_not_or]
    exact (measurableSet_Icc.preimage measurable_fst).compl.union
      (measurableSet_le hp.1 (measurable_fst.add measurable_const))
  apply (ae_prod_iff_ae_ae hm).mpr
  apply ae_of_all
  intro t
  by_cases ht : t ∈ Icc 0 T
  · exact (hp.2.2 t ht).mono (fun _ h _ => h)
  · exact ae_of_all _ (fun _ h => (ht h).elim)

end BoltzmannNonuniqueness.JetCopyDatum

end

end

end OAI
