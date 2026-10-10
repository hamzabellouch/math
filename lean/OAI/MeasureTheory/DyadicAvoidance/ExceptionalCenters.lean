import Mathlib

namespace OAI

noncomputable section

open Set Filter Topology

namespace Problem310.Auxiliary

section

/-- Centers at which some normalized scale avoids all the selected tests. -/
def exceptionalCenters (B : Set ℝ) (N : Set ℕ) (a : ℕ → ℝ) : Set ℝ :=
  {x | ∃ t ∈ Icc (1 : ℝ) 2, ∀ n ∈ N, x + t * a n ∉ B}

/-- Compactness of the normalized scale interval makes the exceptional centers closed. -/
theorem isClosed_exceptionalCenters (B : Set ℝ) (hB : IsOpen B)
    (N : Set ℕ) (a : ℕ → ℝ) : IsClosed (exceptionalCenters B N a) := by
  let K := Icc (1 : ℝ) 2
  let S : Set (ℝ × K) := {z | ∀ n ∈ N, z.1 + (z.2 : ℝ) * a n ∉ B}
  have hS : IsClosed S := by
    have heq : S = ⋂ n ∈ N, {z : ℝ × K | z.1 + (z.2 : ℝ) * a n ∉ B} := by
      ext z
      simp [S]
    rw [heq]
    refine isClosed_iInter fun n => isClosed_iInter fun _ => ?_
    exact hB.isClosed_compl.preimage (continuous_fst.add
      ((continuous_subtype_val.comp continuous_snd).mul_const (a n)))
  have hK : IsCompact K := isCompact_Icc
  let : CompactSpace K := isCompact_iff_compactSpace.mp hK
  have hproj : IsClosed (Prod.fst '' S) := isClosedMap_fst_of_compactSpace S hS
  convert hproj using 1
  ext x
  simp only [exceptionalCenters, S, K, mem_ofPred_eq, mem_image]
  constructor
  · rintro ⟨t, ht, h⟩
    exact ⟨(x, ⟨t, ht⟩), h, rfl⟩
  · rintro ⟨⟨y, t, ht⟩, h, rfl⟩
    exact ⟨t, ht, h⟩

/-- Periodicity passes from the selected set to its exceptional centers. -/
theorem exceptionalCenters_periodic (B : Set ℝ)
    (hB : ∀ x : ℝ, x + 1 ∈ B ↔ x ∈ B) (N : Set ℕ) (a : ℕ → ℝ) :
    ∀ x : ℝ, x + 1 ∈ exceptionalCenters B N a ↔
      x ∈ exceptionalCenters B N a := by
  intro x
  simp only [exceptionalCenters, mem_ofPred_eq]
  constructor
  · rintro ⟨t, ht, h⟩
    refine ⟨t, ht, fun n hn hm => h n hn ?_⟩
    rw [show x + 1 + t * a n = (x + t * a n) + 1 by ring]
    exact (hB _).mpr hm
  · rintro ⟨t, ht, h⟩
    refine ⟨t, ht, fun n hn hm => h n hn ?_⟩
    apply (hB _).mp
    convert hm using 1; ring

/-- An open neighborhood of a limit point meets every tail of a converging sequence. -/
theorem exists_tail_mem_of_tendsto (a : ℕ → ℝ) (ha : Tendsto a atTop (𝓝 0))
    (V : Set ℝ) (hV : IsOpen V) (x : ℝ) (hx : x ∈ V) (t : ℝ) :
    ∃ n : ℕ, 1 ≤ n ∧ x + t * a n ∈ V := by
  have hlim : Tendsto (fun n => x + t * a n) atTop (𝓝 x) := by
    simpa using tendsto_const_nhds.add (tendsto_const_nhds.mul ha)
  have hev : ∀ᶠ n in atTop, x + t * a n ∈ V := hlim.eventually (hV.mem_nhds hx)
  obtain ⟨n, hn, hmem⟩ := (eventually_ge_atTop 1 |>.and hev).exists
  exact ⟨n, hn, hmem⟩

/-- Open-neighborhood repair turns tests away from exceptional centers into hits everywhere. -/
theorem exceptionalCenters_repair (B V : Set ℝ) (N : Set ℕ) (a : ℕ → ℝ)
    (ha : Tendsto a atTop (𝓝 0)) (hN : ∀ n ∈ N, 1 ≤ n)
    (hV : IsOpen V) (hcover : exceptionalCenters B N a ⊆ V) :
    ∀ x t : ℝ, t ∈ Icc (1 : ℝ) 2 →
      ∃ n : ℕ, 1 ≤ n ∧ x + t * a n ∈ B ∪ V := by
  intro x t ht
  by_cases hx : x ∈ exceptionalCenters B N a
  · obtain ⟨n, hn, hmem⟩ := exists_tail_mem_of_tendsto a ha V hV x (hcover hx) t
    exact ⟨n, hn, Or.inr hmem⟩
  · have htest : ∃ n ∈ N, x + t * a n ∈ B := by
      by_contra! h
      exact hx ⟨t, ht, h⟩
    obtain ⟨n, hn, hmem⟩ := htest
    exact ⟨n, hN n hn, Or.inl hmem⟩

open Set Filter Topology MeasureTheory Metric

/-- Thickening preserves one-periodicity. -/
theorem thickening_periodic (R : Set ℝ)
    (hR : ∀ x : ℝ, x + 1 ∈ R ↔ x ∈ R) (ε : ℝ) :
    ∀ x : ℝ, x + 1 ∈ thickening ε R ↔ x ∈ thickening ε R := by
  intro x
  simp only [mem_thickening_iff]
  constructor
  · rintro ⟨z, hz, hdist⟩
    refine ⟨z - 1, ?_, ?_⟩
    · apply (hR (z - 1)).mp
      simpa using hz
    · simpa [Real.dist_eq, sub_sub] using hdist
  · rintro ⟨z, hz, hdist⟩
    refine ⟨z + 1, (hR z).mpr hz, ?_⟩
    simpa using hdist

/-- A closed periodic set admits an open periodic neighborhood with arbitrarily
small increase of its measure in one period. -/
theorem exists_open_periodic_superset (R : Set ℝ) (hRc : IsClosed R)
    (hRp : ∀ x : ℝ, x + 1 ∈ R ↔ x ∈ R) (ε : ℝ) (hε : 0 < ε) :
    ∃ V : Set ℝ, IsOpen V ∧
      (∀ x : ℝ, x + 1 ∈ V ↔ x ∈ V) ∧ R ⊆ V ∧
      volume (V ∩ Icc (0 : ℝ) 1) ≤
        volume (R ∩ Icc (0 : ℝ) 1) + ENNReal.ofReal ε := by
  let μ : Measure ℝ := volume.restrict (Icc (0 : ℝ) 1)
  have hfinite : IsFiniteMeasure μ := by
    dsimp [μ]
    infer_instance
  let := hfinite
  have hlim : Tendsto (fun r => μ (thickening r R)) (𝓝[>] 0) (𝓝 (μ R)) :=
    tendsto_measure_thickening_of_isClosed ⟨1, zero_lt_one, measure_ne_top μ _⟩ hRc
  have hlt : μ R < μ R + ENNReal.ofReal ε :=
    ENNReal.lt_add_right (measure_ne_top μ R) (by positivity)
  have hev : ∀ᶠ r in 𝓝[>] (0 : ℝ), μ (thickening r R) < μ R + ENNReal.ofReal ε :=
    hlim.eventually (eventually_lt_nhds hlt)
  have hpos : ∀ᶠ r in 𝓝[>] (0 : ℝ), 0 < r := self_mem_nhdsWithin
  obtain ⟨r, hr, hbound⟩ := (hpos.and hev).exists
  refine ⟨thickening r R, isOpen_thickening, thickening_periodic R hRp r,
    self_subset_thickening hr R, ?_⟩
  simpa [μ, Measure.restrict_apply, isOpen_thickening.measurableSet,
    hRc.measurableSet] using hbound.le

end

open Set Filter Topology MeasureTheory

/-- Deterministic completion of the probabilistic construction: once the density of
an open test set plus its exceptional centers is small, a genuinely hitting open
periodic set is available at arbitrarily small additional density cost. -/
theorem repair_open_periodic_hitting
    (B : Set ℝ) (hBo : IsOpen B)
    (hBp : ∀ x : ℝ, x + 1 ∈ B ↔ x ∈ B)
    (N : Set ℕ) (hN : ∀ n ∈ N, 1 ≤ n)
    (a : ℕ → ℝ) (ha : Tendsto a atTop (𝓝 0))
    (c : ENNReal)
    (hbound : volume (B ∩ Icc (0 : ℝ) 1) +
      volume (exceptionalCenters B N a ∩ Icc (0 : ℝ) 1) ≤ c)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ H : Set ℝ, IsOpen H ∧
      (∀ x : ℝ, x + 1 ∈ H ↔ x ∈ H) ∧
      volume (H ∩ Icc (0 : ℝ) 1) ≤ c + ENNReal.ofReal ε ∧
      ∀ x t : ℝ, t ∈ Icc (1 : ℝ) 2 →
        ∃ n : ℕ, 1 ≤ n ∧ x + t * a n ∈ H := by
  obtain ⟨V, hVo, hVp, hRV, hVm⟩ := exists_open_periodic_superset
    (exceptionalCenters B N a) (isClosed_exceptionalCenters B hBo N a)
    (exceptionalCenters_periodic B hBp N a) ε hε
  refine ⟨B ∪ V, hBo.union hVo, ?_, ?_,
    exceptionalCenters_repair B V N a ha hN hVo hRV⟩
  · intro x
    simp only [mem_union, hBp, hVp]
  · calc
      volume ((B ∪ V) ∩ Icc (0 : ℝ) 1)
          ≤ volume (B ∩ Icc (0 : ℝ) 1) + volume (V ∩ Icc (0 : ℝ) 1) := by
            rw [union_inter_distrib_right]
            exact measure_union_le _ _
      _ ≤ volume (B ∩ Icc (0 : ℝ) 1) +
          (volume (exceptionalCenters B N a ∩ Icc (0 : ℝ) 1) +
            ENNReal.ofReal ε) := add_le_add le_rfl hVm
      _ ≤ c + ENNReal.ofReal ε := by
        rw [← add_assoc]
        exact add_le_add hbound le_rfl

/-- The dyadic sequence converges to zero. -/
theorem dyadic_tendsto_zero :
    Tendsto (fun n : ℕ => (2 : ℝ)⁻¹ ^ n) atTop (𝓝 0) := by
  exact tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)

theorem periodic_hitting_of_small_exceptional
    (p : ℝ) (hp : 0 < p) (B : Set ℝ) (hBo : IsOpen B)
    (hBp : ∀ x : ℝ, x + 1 ∈ B ↔ x ∈ B)
    (N : Set ℕ) (hN : ∀ n ∈ N, 1 ≤ n)
    (hbound : volume (B ∩ Icc (0 : ℝ) 1) +
      volume (exceptionalCenters B N (fun n => (2 : ℝ)⁻¹ ^ n) ∩ Icc (0 : ℝ) 1)
        ≤ ENNReal.ofReal (5 * p)) :
    ∃ H : Set ℝ, IsOpen H ∧
      (∀ x : ℝ, x + 1 ∈ H ↔ x ∈ H) ∧
      volume (H ∩ Icc (0 : ℝ) 1) ≤ ENNReal.ofReal (6 * p) ∧
      ∀ x t : ℝ, t ∈ Icc (1 : ℝ) 2 →
        ∃ n : ℕ, 1 ≤ n ∧ x + t * ((2 : ℝ)⁻¹ ^ n) ∈ H := by
  obtain ⟨H, hHo, hHp, hHm, hHit⟩ := repair_open_periodic_hitting
    B hBo hBp N hN (fun n => (2 : ℝ)⁻¹ ^ n) dyadic_tendsto_zero
    (ENNReal.ofReal (5 * p)) hbound p hp
  refine ⟨H, hHo, hHp, ?_, hHit⟩
  convert hHm using 1
  rw [← ENNReal.ofReal_add (by positivity) (le_of_lt hp)]
  congr 1
  ring

end Problem310.Auxiliary

end

end OAI
