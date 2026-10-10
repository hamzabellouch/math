import Mathlib
import OAI.Geometry.CAT0Fillings.Currents.MassBounds

namespace OAI

section
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal

namespace CAT0Fillings
attribute [local instance] Classical.propDecidable
universe u
section Foundations
variable {X : Type u} [MetricSpace X] [MeasurableSpace X]
open scoped BoundedContinuousFunction

variable [BorelSpace X]
lemma controls_of_weak_limits {ι : Type*} {l : Filter ι} [NeBot l]
    {k : ℕ} {Ts : ι → Functional X k} {T : Functional X k}
    {μs : ι → FiniteMeasure X} {μ : FiniteMeasure X}
    (hμ : Tendsto μs l (𝓝 μ)) (hc : ∀ j, Controls (Ts j) (μs j : Measure X))
    (hT : ∀ b π, Admissible b π →
      Tendsto (fun j => Ts j b π) l (𝓝 (T b π))) : Controls T (μ : Measure X) := by
  intro b π hb hπ
  exact le_of_tendsto_of_tendsto
    (Filter.Tendsto.abs (hT b π ⟨hb, fun i => ⟨1, hπ i⟩⟩))
    ((continuous_integral_abs_boundedLip hb).tendsto μ |>.comp hμ)
    (Eventually.of_forall fun j => hc j b π hb hπ)

lemma exists_controls_of_bounded_weak_limit [CompactSpace X]
    {ι : Type*} {l : Filter ι} [NeBot l] {k : ℕ}
    {Ts : ι → Functional X k} {T : Functional X k} (M : ℝ≥0)
    (hTs : ∀ j, IsMetricCurrent (Ts j)) (hbound : ∀ j, mass (Ts j) ≤ (M : ℝ))
    (hlim : ∀ b π, Admissible b π → Tendsto (fun j => Ts j b π) l (𝓝 (T b π))) :
    ∃ μ : Measure X, IsFiniteMeasure μ ∧ Controls T μ ∧ μ.real univ ≤ (M : ℝ) := by
  choose μj hfin hcontrol heq using fun j => (hTs j).exists_controls_mass_eq
  let νs : ι → FiniteMeasure X := fun j => ⟨μj j, hfin j⟩
  have hbound' : ∀ j, νs j ∈ {ν : FiniteMeasure X | ν.mass ≤ M} := by
    intro j
    change (νs j).mass ≤ M
    apply NNReal.coe_le_coe.mp
    change (μj j).real univ ≤ (M : ℝ)
    rw [← heq]
    exact hbound j
  obtain ⟨ν, hν, hcluster⟩ :=
    (isCompact_setOfPred_finiteMeasure_le_of_compactSpace X M).exists_mapClusterPt_of_frequently (l := l)
      (Eventually.of_forall hbound').frequently
  let l' := comap νs (𝓝 ν) ⊓ l
  have hl' : NeBot l' := neBot_inf_comap_iff_map'.mpr hcluster
  let := hl'
  have hνs : Tendsto νs l' (𝓝 ν) := tendsto_iff_comap.mpr inf_le_left
  have hctrl : Controls T (ν : Measure X) :=
    controls_of_weak_limits hνs hcontrol (fun b π h => (hlim b π h).mono_left inf_le_right)
  exact ⟨ν, inferInstance, hctrl, NNReal.coe_le_coe.mpr hν⟩

lemma mass_le_of_bounded_weak_limit [CompactSpace X]
    {ι : Type*} {l : Filter ι} [NeBot l] {k : ℕ}
    {Ts : ι → Functional X k} {T : Functional X k} (M : ℝ≥0)
    (hTs : ∀ j, IsMetricCurrent (Ts j)) (hbound : ∀ j, mass (Ts j) ≤ (M : ℝ))
    (hlim : ∀ b π, Admissible b π → Tendsto (fun j => Ts j b π) l (𝓝 (T b π))) :
    mass T ≤ (M : ℝ) := by
  obtain ⟨μ, hfin, hcontrol, hmass⟩ :=
    exists_controls_of_bounded_weak_limit M hTs hbound hlim
  exact (mass_le_measure hfin hcontrol).trans hmass

omit [MeasurableSpace X] [BorelSpace X] in
lemma BoundedLip.mul {b c : X → ℝ} (hb : BoundedLip b) (hc : BoundedLip c) :
    BoundedLip (fun x => b x * c x) := by
  obtain ⟨⟨Kb, hKb⟩, Mb, hMb⟩ := hb
  obtain ⟨⟨Kc, hKc⟩, Mc, hMc⟩ := hc
  let B : ℝ≥0 := ⟨max Mb 0, le_max_right _ _⟩
  let C : ℝ≥0 := ⟨max Mc 0, le_max_right _ _⟩
  have hB (x : X) : |b x| ≤ (B : ℝ) := (hMb x).trans (le_max_left _ _)
  have hC (x : X) : |c x| ≤ (C : ℝ) := (hMc x).trans (le_max_left _ _)
  refine ⟨⟨B * Kc + C * Kb, ?_⟩, (B : ℝ) * (C : ℝ), ?_⟩
  · apply lipschitzWith_iff_dist_le_mul.mpr
    intro x y
    rw [Real.dist_eq]
    calc |b x * c x - b y * c y| = |b x * (c x - c y) + (b x - b y) * c y| := by
            congr 1; ring
      _ ≤ |b x| * |c x - c y| + |b x - b y| * |c y| := by
            simpa only [abs_mul] using abs_add_le (b x * (c x - c y)) ((b x - b y) * c y)
      _ ≤ (B : ℝ) * ((Kc : ℝ) * dist x y) + ((Kb : ℝ) * dist x y) * (C : ℝ) := by
            apply add_le_add
            · exact mul_le_mul (hB x) (hKc.dist_le_mul x y) (abs_nonneg _) B.coe_nonneg
            · exact mul_le_mul (hKb.dist_le_mul x y) (hC y) (abs_nonneg _)
                (mul_nonneg Kb.coe_nonneg dist_nonneg)
      _ = ((B * Kc + C * Kb : ℝ≥0) : ℝ) * dist x y := by push_cast; ring
  · intro x
    rw [abs_mul]
    exact mul_le_mul (hB x) (hC x) (abs_nonneg _) B.coe_nonneg

lemma IsMetricCurrent.mass_bound_uniform [CompactSpace X]
    {k : ℕ} {T : Functional X k} (hT : IsMetricCurrent T)
    {b : X → ℝ} (hb : BoundedLip b) {π : Fin k → X → ℝ}
    (K : Fin k → ℝ≥0) (hK : ∀ i, LipschitzWith (K i) (π i))
    {M : ℝ} (hM : ∀ x, |b x| ≤ M) :
    |T b π| ≤ ((∏ i, (K i : ℝ)) * M) * mass T := by
  obtain ⟨μ, hfin, hcontrol, heq⟩ := hT.exists_controls_mass_eq
  let := hfin
  have hint : Integrable (fun x => |b x|) μ := (hb.toBoundedContinuous.integrable μ).abs
  have hbound : (∫ x, |b x| ∂μ) ≤ μ.real univ * M := by
    simpa using integral_mono hint (integrable_const M) hM
  calc |T b π| ≤ (∏ i, (K i : ℝ)) * ∫ x, |b x| ∂μ := hT.mass_bound hcontrol hb K hK
    _ ≤ (∏ i, (K i : ℝ)) * (μ.real univ * M) :=
      mul_le_mul_of_nonneg_left hbound (Finset.prod_nonneg fun i _ => (K i).coe_nonneg)
    _ = ((∏ i, (K i : ℝ)) * M) * mass T := by rw [heq]; ring

lemma IsMetricCurrent.eq_zero_of_mass_eq_zero [CompactSpace X]
    {k : ℕ} {T : Functional X k} (hT : IsMetricCurrent T) (hm : mass T = 0) :
    T = fun _ _ => 0 := by
  funext b π
  by_cases h : Admissible b π
  · choose K hK using h.2
    obtain ⟨M, hM⟩ := h.1.2
    have hle := hT.mass_bound_uniform h.1 K hK hM
    rw [hm, mul_zero] at hle
    exact abs_eq_zero.mp (le_antisymm hle (abs_nonneg _))
  · exact hT.offDomain b π h

end Foundations
end CAT0Fillings
end

end OAI
