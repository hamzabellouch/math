import OAI.NumberTheory.DukePrimeDegree.Dynamics.FlowMaximal
import Mathlib.MeasureTheory.OuterMeasure.BorelCantelli
import Mathlib.MeasureTheory.Measure.Regular
import Mathlib.Analysis.SpecificLimits.Basic

namespace OAI

/-!
# Compact simultaneous returns outside a prescribed null set

A summable sequence of maximal-inequality exceptional sets gives one
conull set on which any two points return to a common compact set with
uniformly positive overlap. No ergodicity of the individual flow is used.
-/

noncomputable section
open Set Filter MeasureTheory
open scoped ENNReal Topology

namespace DukePrimeDegree

theorem exists_eventual_flow_good_sets
    {Y : Type*} [MeasurableSpace Y]
    (μ : Measure Y) [IsFiniteMeasure μ]
    {Φ : ℝ → Y → Y} (hΦ : Measurable (fun p : Y × ℝ => Φ p.2 p.1))
    (hzero : ∀ x, Φ 0 x = x) (hadd : ∀ s t x, Φ (s + t) x = Φ s (Φ t x))
    (hpres : ∀ t, MeasurePreserving (Φ t) μ μ)
    (K : ℕ → Set Y) (hK : ∀ m, MeasurableSet (K m))
    (hsmall : ∀ m, μ (K m)ᶜ < ENNReal.ofReal (((1 / 2 : ℝ) ^ m) / 8)) :
    ∃ G : ℕ → Set Y, (∀ m, MeasurableSet (G m)) ∧
      (∀ᵐ x ∂μ, ∀ᶠ m in atTop, x ∈ G m) ∧
      ∀ m x, x ∈ G m → ∀ T : ℝ, 1 ≤ T →
        volume.real (Ioc 0 T ∩ {t | Φ t x ∉ K m}) ≤ T / 4 := by
  have hG (m : ℕ) := exists_flow_return_good_set μ hΦ hzero hadd hpres
    (hK m).compl (1 / 4) (by norm_num)
  choose G hGmeas hGmass hgood using hG
  have hmass (m : ℕ) : μ (G m)ᶜ ≤ (2⁻¹ : ℝ≥0∞) ^ m := by
    have hr : μ.real (K m)ᶜ ≤ ((1 / 2 : ℝ) ^ m) / 8 := by
      have h := (ENNReal.toReal_le_toReal (measure_ne_top μ _)
        ENNReal.ofReal_ne_top).mpr (hsmall m).le
      rw [ENNReal.toReal_ofReal (by positivity)] at h
      exact h
    calc
      μ (G m)ᶜ ≤ ENNReal.ofReal (2 * μ.real (K m)ᶜ / (1 / 4)) := hGmass m
      _ ≤ ENNReal.ofReal ((1 / 2 : ℝ) ^ m) := ENNReal.ofReal_le_ofReal (by linarith)
      _ = (2⁻¹ : ℝ≥0∞) ^ m := by
        rw [ENNReal.ofReal_pow (by norm_num)]
        congr 1
        rw [ENNReal.ofReal_div_of_pos (by norm_num)]
        norm_num
  have hs : (∑' m, μ (G m)ᶜ) ≠ ∞ := by
    apply ne_top_of_le_ne_top (by norm_num : (2 : ℝ≥0∞) ≠ ∞)
    calc
      (∑' m, μ (G m)ᶜ) ≤ ∑' m, (2⁻¹ : ℝ≥0∞) ^ m := ENNReal.tsum_le_tsum hmass
      _ = 2 := ENNReal.tsum_geometric_two
  refine ⟨G, hGmeas, ?_, ?_⟩
  · simpa only [notMem_compl_iff] using (ae_eventually_notMem hs)
  · intro m x hx T hT
    simpa only [mem_compl_iff, one_div, div_eq_mul_inv, one_mul, mul_comm] using hgood m x hx T hT

theorem exists_compact_flow_return_family
    {Y : Type*} [TopologicalSpace Y] [T2Space Y] [MeasurableSpace Y] [BorelSpace Y]
    (μ : Measure Y) [IsFiniteMeasure μ] [Measure.InnerRegularCompactLTTop μ]
    {Φ : ℝ → Y → Y} (hΦ : Measurable (fun p : Y × ℝ => Φ p.2 p.1))
    (hzero : ∀ x, Φ 0 x = x) (hadd : ∀ s t x, Φ (s + t) x = Φ s (Φ t x))
    (hpres : ∀ t, MeasurePreserving (Φ t) μ μ)
    (N : Set Y) (hN : MeasurableSet N) (hNzero : μ N = 0) :
    ∃ K G : ℕ → Set Y,
      (∀ m, IsCompact (K m) ∧ K m ⊆ Nᶜ ∧ MeasurableSet (G m)) ∧
      (∀ᵐ x ∂μ, ∀ᶠ m in atTop, x ∈ G m) ∧
      ∀ m x, x ∈ G m → ∀ T : ℝ, 1 ≤ T →
        volume.real (Ioc 0 T ∩ {t | Φ t x ∉ K m}) ≤ T / 4 := by
  have hK (m : ℕ) : ∃ K : Set Y, IsCompact K ∧ K ⊆ Nᶜ ∧
      μ Kᶜ < ENNReal.ofReal (((1 / 2 : ℝ) ^ m) / 8) := by
    have he : ENNReal.ofReal (((1 / 2 : ℝ) ^ m) / 8) ≠ 0 :=
      (ENNReal.ofReal_pos.mpr (by positivity)).ne'
    obtain ⟨K, hKN, hK, hsmall⟩ := hN.compl.exists_isCompact_sdiff_lt
      (measure_ne_top μ Nᶜ) he
    refine ⟨K, hK, hKN, ?_⟩
    have hset : Nᶜ \ K = Kᶜ \ N := by ext x; simp only [Set.mem_sdiff, mem_compl_iff, and_comm]
    rwa [hset, measure_sdiff_null hNzero] at hsmall
  choose K hcompact hKN hsmall using hK
  obtain ⟨G, hG, hae, hgood⟩ := exists_eventual_flow_good_sets μ hΦ hzero hadd hpres
    K (fun m => (hcompact m).isClosed.measurableSet) hsmall
  exact ⟨K, G, fun m => ⟨hcompact m, hKN m, hG m⟩, hae, hgood⟩

theorem exists_late_simultaneous_compact_return
    {Y : Type*} (Φ : ℝ → Y → Y) (K : Set Y) (x y : Y)
    (hx : ∀ T : ℝ, 1 ≤ T →
      volume.real (Ioc 0 T ∩ {t | Φ t x ∉ K}) ≤ T / 4)
    (hy : ∀ T : ℝ, 1 ≤ T →
      volume.real (Ioc 0 T ∩ {t | Φ t y ∉ K}) ≤ T / 4)
    (R : ℝ) : ∃ t : ℝ, R < t ∧ Φ t x ∈ K ∧ Φ t y ∈ K := by
  let T : ℝ := 4 * (max R 1 + 1)
  have hT : 1 ≤ T := by dsimp [T]; linarith [le_max_right R 1]
  have hTpos : 0 < T := by linarith
  let A : Set ℝ := Ioc 0 T ∩ {t | Φ t x ∉ K}
  let B : Set ℝ := Ioc 0 T ∩ {t | Φ t y ∉ K}
  by_contra h
  have hcover : Ioc (T / 4) T ⊆ A ∪ B := by
    intro t ht
    have ht0 : t ∈ Ioc 0 T := ⟨by linarith [ht.1], ht.2⟩
    by_cases htx : Φ t x ∈ K
    · apply Or.inr
      refine ⟨ht0, ?_⟩
      intro hty
      apply h ⟨t, ?_, htx, hty⟩
      dsimp [T] at ht
      linarith [ht.1, le_max_left R 1]
    · exact Or.inl ⟨ht0, htx⟩
  have hsub : A ∪ B ⊆ Ioc 0 T := union_subset inter_subset_left inter_subset_left
  have hfinite : volume (A ∪ B) ≠ ∞ :=
    measure_ne_top_of_subset hsub (by rw [Real.volume_Ioc]; exact ENNReal.ofReal_ne_top)
  have hle := measureReal_mono hcover hfinite
  have hu := measureReal_union_le (μ := volume) A B
  have hAx : volume.real A ≤ T / 4 := hx T hT
  have hBy : volume.real B ≤ T / 4 := hy T hT
  rw [Real.volume_real_Ioc_of_le (by linarith : T / 4 ≤ T)] at hle
  linarith

theorem exists_conull_simultaneous_compact_returns
    {Y : Type*} [TopologicalSpace Y] [T2Space Y] [MeasurableSpace Y] [BorelSpace Y]
    (μ : Measure Y) [IsFiniteMeasure μ] [Measure.InnerRegularCompactLTTop μ]
    {Φ : ℝ → Y → Y} (hΦ : Measurable (fun p : Y × ℝ => Φ p.2 p.1))
    (hzero : ∀ x, Φ 0 x = x) (hadd : ∀ s t x, Φ (s + t) x = Φ s (Φ t x))
    (hpres : ∀ t, MeasurePreserving (Φ t) μ μ)
    (N : Set Y) (hN : MeasurableSet N) (hNzero : μ N = 0) :
    ∃ M : Set Y, MeasurableSet M ∧ μ M = 0 ∧
      ∀ x ∉ M, ∀ y ∉ M, ∃ K : Set Y, IsCompact K ∧ K ⊆ Nᶜ ∧
        ∀ R : ℝ, ∃ t : ℝ, R < t ∧ Φ t x ∈ K ∧ Φ t y ∈ K := by
  obtain ⟨K, G, hKG, hae, hgood⟩ :=
    exists_compact_flow_return_family μ hΦ hzero hadd hpres N hN hNzero
  obtain ⟨M, hbad, hM, hMzero⟩ := exists_measurable_superset_of_null (ae_iff.mp hae)
  refine ⟨M, hM, hMzero, ?_⟩
  intro x hx y hy
  have hxG : ∀ᶠ m in atTop, x ∈ G m := by
    by_contra h
    exact hx (hbad h)
  have hyG : ∀ᶠ m in atTop, y ∈ G m := by
    by_contra h
    exact hy (hbad h)
  obtain ⟨m, hxm, hym⟩ := (hxG.and hyG).exists
  exact ⟨K m, (hKG m).1, (hKG m).2.1,
    exists_late_simultaneous_compact_return Φ (K m) x y
      (hgood m x hxm) (hgood m y hym)⟩

end DukePrimeDegree

end

end OAI
