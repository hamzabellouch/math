/-
Portions of this file have been adapted from an external source.
The source copyright header and license information are preserved below.
-/

import OAI.Analysis.Brenier.DensityCDF

namespace OAI

noncomputable section
open MeasureTheory Set Filter Topology

namespace Problem358

/-- Comparison with the unique inverse point of a monotone real function. -/
lemma unique_monotone_inverse_lt_iff {F : ℝ → ℝ} (hF : Monotone F)
    {t x : ℝ} (hx : F x = t) (huniq : ∀ y, F y = t → y = x) (q : ℝ) :
    x < q ↔ t < F q := by
  constructor
  · intro hxq
    have hle : t ≤ F q := hx ▸ hF hxq.le
    refine lt_of_le_of_ne hle ?_
    intro heq
    have hqx := huniq q heq.symm
    exact hxq.ne hqx.symm
  · intro htq
    by_contra h
    have hqx : q ≤ x := le_of_not_gt h
    have hle := hF hqx
    rw [hx] at hle
    exact (not_lt_of_ge hle) htq

/-- Parameter-dependent monotone inverses are measurable whenever their CDF
sections and selected levels are measurable. Unique fibers remove any need
for a measurable-choice theorem. -/
theorem exists_measurable_monotone_inverse
    {A : Type*} [MeasurableSpace A] (F : A → ℝ → ℝ) (t : A → ℝ)
    (hmono : ∀ a, Monotone (F a))
    (hsection : ∀ q : ℝ, Measurable (fun a => F a q))
    (ht : Measurable t) (hex : ∀ a, ∃! x : ℝ, F a x = t a) :
    ∃ Q : A → ℝ, Measurable Q ∧ ∀ a, F a (Q a) = t a := by
  classical
  choose Q hQ huniq using hex
  refine ⟨Q, ?_, hQ⟩
  apply measurable_of_Iio
  intro q
  have heq : Q ⁻¹' Iio q = {a | t a < F a q} := by
    ext a
    exact unique_monotone_inverse_lt_iff (hmono a) (hQ a) (huniq a) q
  rw [heq]
  exact measurableSet_lt ht (hsection q)

/-- Inverse points of a monotone function are necessarily ordered with their
levels, even if the original function has flat regions away from those fibers. -/
lemma inverse_points_strictMono {F : ℝ → ℝ} (hF : Monotone F)
    {S : Set ℝ} {Q : S → ℝ} (hQ : ∀ t, F (Q t) = (t : ℝ)) :
    StrictMono Q := by
  intro s t hst
  by_contra h
  have hle : Q t ≤ Q s := le_of_not_gt h
  have hh := hF hle
  rw [hQ t, hQ s] at hh
  exact (not_le_of_gt hst) hh

/-- A continuous strictly increasing interval reaches each intermediate level
at a unique point, provided the ambient extension remains monotone. -/
lemma exists_unique_monotone_inverse_of_interval {F : ℝ → ℝ} {a b t : ℝ}
    (hab : a ≤ b) (hcont : ContinuousOn F (Icc a b)) (hmono : Monotone F)
    (hstrict : StrictMonoOn F (Icc a b)) (ht : t ∈ Ioo (F a) (F b)) :
    ∃! x : ℝ, F x = t := by
  obtain ⟨x, hx, hxt⟩ := intermediate_value_Ioo hab hcont ht
  refine ⟨x, hxt, ?_⟩
  intro y hyt
  have hya : a < y := by
    by_contra hy
    have hh := hmono (le_of_not_gt hy)
    rw [hyt] at hh
    exact (not_le_of_gt ht.1) hh
  have hyb : y < b := by
    by_contra hy
    have hh := hmono (le_of_not_gt hy)
    rw [hyt] at hh
    exact (not_le_of_gt ht.2) hh
  exact hstrict.injOn ⟨hya.le, hyb.le⟩ ⟨hx.1.le, hx.2.le⟩ (hyt.trans hxt.symm)

/-- A local inverse of a monotone real function is continuous at every level
whose fiber is a singleton. No differentiability or strict global monotonicity
is required. -/
lemma continuousAt_monotone_inverse {F Q : ℝ → ℝ} {t : ℝ}
    (hmono : Monotone F) (hlocal : ∀ᶠ s in 𝓝 t, F (Q s) = s)
    (huniq : ∀ x, F x = t → x = Q t) : ContinuousAt Q t := by
  have hQt : F (Q t) = t := hlocal.self_of_nhds
  apply tendsto_order.mpr
  constructor
  · intro q hq
    have hFt : F q < t := by
      have hle : F q ≤ t := by simpa only [hQt] using hmono hq.le
      refine lt_of_le_of_ne hle ?_
      intro heq
      exact hq.ne (huniq q heq)
    filter_upwards [eventually_gt_nhds hFt, hlocal] with s hs hQs
    by_contra h
    have hh := hmono (le_of_not_gt h)
    rw [hQs] at hh
    exact (not_le_of_gt hs) hh
  · intro q hq
    have htF : t < F q := (unique_monotone_inverse_lt_iff hmono hQt huniq q).mp hq
    filter_upwards [eventually_lt_nhds htF, hlocal] with s hs hQs
    by_contra h
    have hh := hmono (le_of_not_gt h)
    rw [hQs] at hh
    exact (not_le_of_gt hs) hh

/-- The reciprocal-density derivative formula for a local monotone inverse. -/
lemma hasDerivAt_monotone_inverse {F Q : ℝ → ℝ} {t c : ℝ}
    (hmono : Monotone F) (hlocal : ∀ᶠ s in 𝓝 t, F (Q s) = s)
    (huniq : ∀ x, F x = t → x = Q t)
    (hderiv : HasDerivAt F c (Q t)) (hc : c ≠ 0) :
    HasDerivAt Q c⁻¹ t := by
  exact HasDerivAt.of_local_left_inverse
    (continuousAt_monotone_inverse hmono hlocal huniq) hderiv hc hlocal

lemma unique_monotone_inverse_le_iff {F : ℝ → ℝ} (hF : Monotone F)
    {t x : ℝ} (hx : F x = t) (huniq : ∀ y, F y = t → y = x) (q : ℝ) :
    x ≤ q ↔ t ≤ F q := by
  constructor
  · intro hxq
    simpa only [hx] using hF hxq
  · intro htq
    by_contra h
    have hqx : q < x := lt_of_not_ge h
    have hle : F q ≤ t := by simpa only [hx] using hF hqx.le
    have heq : F q = t := le_antisymm hle htq
    exact hqx.ne (huniq q heq)

lemma volume_Iic_inter_unitInterval (c : ℝ) (hc : c ≤ 1) :
    volume (Iic c ∩ Ioo (0 : ℝ) 1) = ENNReal.ofReal c := by
  rcases lt_or_eq_of_le hc with hc | rfl
  · have heq : Iic c ∩ Ioo (0 : ℝ) 1 = Ioc 0 c := by
      ext t
      simp only [mem_inter_iff, mem_Iic, mem_Ioo, mem_Ioc]
      constructor
      · rintro ⟨htc, ht0, ht1⟩
        exact ⟨ht0, htc⟩
      · rintro ⟨ht0, htc⟩
        exact ⟨htc, ht0, htc.trans_lt hc⟩
    rw [heq, Real.volume_Ioc, sub_zero]
  · have heq : Iic (1 : ℝ) ∩ Ioo 0 1 = Ioo 0 1 := by
      exact inter_eq_right.mpr (fun _ hx => hx.2.le)
    rw [heq, Real.volume_Ioo]
    norm_num

/-- A measurable inverse of a probability CDF transports unit-interval
Lebesgue measure to the probability law. This is the one-dimensional law
identity used in triangular quantile constructions. -/
theorem map_inverse_cdf_eq (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {Q : ℝ → ℝ} (hQ : Measurable Q)
    (hsolve : ∀ t ∈ Ioo (0 : ℝ) 1, ProbabilityTheory.cdf μ (Q t) = t)
    (huniq : ∀ t ∈ Ioo (0 : ℝ) 1, ∀ x,
      ProbabilityTheory.cdf μ x = t → x = Q t) :
    Measure.map Q (volume.restrict (Ioo (0 : ℝ) 1)) = μ := by
  let : IsFiniteMeasure (volume.restrict (Ioo (0 : ℝ) 1)) := ⟨by
    simp only [Measure.restrict_apply_univ, Real.volume_Ioo]
    exact ENNReal.ofReal_lt_top⟩
  apply Measure.ext_of_Iic
  intro x
  rw [Measure.map_apply hQ measurableSet_Iic,
    Measure.restrict_apply (hQ measurableSet_Iic)]
  have heq : Q ⁻¹' Iic x ∩ Ioo (0 : ℝ) 1 =
      Iic (ProbabilityTheory.cdf μ x) ∩ Ioo (0 : ℝ) 1 := by
    ext t
    simp only [mem_inter_iff, mem_preimage, mem_Iic]
    constructor
    · rintro ⟨htx, ht⟩
      exact ⟨(unique_monotone_inverse_le_iff (ProbabilityTheory.monotone_cdf μ)
        (hsolve t ht) (huniq t ht) x).mp htx, ht⟩
    · rintro ⟨htx, ht⟩
      exact ⟨(unique_monotone_inverse_le_iff (ProbabilityTheory.monotone_cdf μ)
        (hsolve t ht) (huniq t ht) x).mpr htx, ht⟩
  rw [heq, volume_Iic_inter_unitInterval _ (ProbabilityTheory.cdf_le_one μ x),
    ProbabilityTheory.ofReal_cdf]

/-- A probability law with unique inverse CDF points at every level in `(0,1)`
has a measurable quantile transport, continuous at every such level. -/
theorem exists_measurable_cdf_transport (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hex : ∀ t ∈ Ioo (0 : ℝ) 1, ∃! x : ℝ, ProbabilityTheory.cdf μ x = t) :
    ∃ Q : ℝ → ℝ, Measurable Q ∧
      Measure.map Q (volume.restrict (Ioo (0 : ℝ) 1)) = μ ∧
      (∀ t ∈ Ioo (0 : ℝ) 1, ProbabilityTheory.cdf μ (Q t) = t) ∧
      ∀ t ∈ Ioo (0 : ℝ) 1, ContinuousAt Q t := by
  obtain ⟨Q₀, hQ₀, hsolve₀⟩ := exists_measurable_monotone_inverse
    (fun (_ : Ioo (0 : ℝ) 1) x => ProbabilityTheory.cdf μ x)
    (fun t : Ioo (0 : ℝ) 1 => (t : ℝ))
    (fun _ => ProbabilityTheory.monotone_cdf μ) (fun _ => measurable_const)
    measurable_subtype_coe (fun t => hex t t.property)
  obtain ⟨Q, hQ, hext⟩ := (MeasurableEmbedding.subtype_coe measurableSet_Ioo).exists_measurable_extend
    hQ₀ (fun _ => inferInstance)
  have hsolve : ∀ t ∈ Ioo (0 : ℝ) 1, ProbabilityTheory.cdf μ (Q t) = t := by
    intro t ht
    have he := congrFun hext (⟨t, ht⟩ : Ioo (0 : ℝ) 1)
    change Q t = Q₀ ⟨t, ht⟩ at he
    rw [he]
    exact hsolve₀ ⟨t, ht⟩
  have huniq : ∀ t ∈ Ioo (0 : ℝ) 1, ∀ x,
      ProbabilityTheory.cdf μ x = t → x = Q t := by
    intro t ht x hx
    obtain ⟨z, hz, hu⟩ := hex t ht
    exact (hu x hx).trans (hu (Q t) (hsolve t ht)).symm
  refine ⟨Q, hQ, map_inverse_cdf_eq μ hQ hsolve huniq, hsolve, ?_⟩
  intro t ht
  apply continuousAt_monotone_inverse (ProbabilityTheory.monotone_cdf μ) _ (huniq t ht)
  filter_upwards [isOpen_Ioo.mem_nhds ht] with s hs
  exact hsolve s hs

/-- Jointly measurable quantiles for a family of one-dimensional probability
laws. Only measurability of each CDF section is needed in the parameter. -/
theorem exists_measurable_cdf_family_transport
    {A : Type*} [MeasurableSpace A] (κ : A → Measure ℝ)
    [∀ a, IsProbabilityMeasure (κ a)]
    (hsection : ∀ q : ℝ, Measurable (fun a => ProbabilityTheory.cdf (κ a) q))
    (hex : ∀ a t, t ∈ Ioo (0 : ℝ) 1 → ∃! x : ℝ, ProbabilityTheory.cdf (κ a) x = t) :
    ∃ Q : A × ℝ → ℝ, Measurable Q ∧
      (∀ a, Measure.map (fun t => Q (a, t)) (volume.restrict (Ioo (0 : ℝ) 1)) = κ a) ∧
      (∀ a t, t ∈ Ioo (0 : ℝ) 1 → ProbabilityTheory.cdf (κ a) (Q (a, t)) = t) ∧
      ∀ a t, t ∈ Ioo (0 : ℝ) 1 → ContinuousAt (fun s => Q (a, s)) t := by
  classical
  let level : ℝ → ℝ := (Ioo (0 : ℝ) 1).piecewise id (fun _ => 1 / 2)
  have hmlevel : Measurable level := measurable_id.piecewise measurableSet_Ioo measurable_const
  have hlevel (t : ℝ) : level t ∈ Ioo (0 : ℝ) 1 := by
    by_cases ht : t ∈ Ioo (0 : ℝ) 1
    · simpa only [level, piecewise_eq_of_mem _ _ _ ht, id_eq] using ht
    · simp only [level, piecewise_eq_of_notMem _ _ _ ht]
      norm_num
  have hlevel_eq {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) : level t = t := by
    simp only [level, piecewise_eq_of_mem _ _ _ ht, id_eq]
  obtain ⟨Q, hQ, hsolve₀⟩ := exists_measurable_monotone_inverse
    (fun (p : A × ℝ) x => ProbabilityTheory.cdf (κ p.1) x)
    (fun p : A × ℝ => level p.2)
    (fun p => ProbabilityTheory.monotone_cdf (κ p.1))
    (fun q => (hsection q).comp measurable_fst) (hmlevel.comp measurable_snd)
    (fun p => hex p.1 (level p.2) (hlevel p.2))
  have hsolve : ∀ a t, t ∈ Ioo (0 : ℝ) 1 → ProbabilityTheory.cdf (κ a) (Q (a, t)) = t := by
    intro a t ht
    exact (hsolve₀ (a, t)).trans (hlevel_eq ht)
  have huniq : ∀ a t, t ∈ Ioo (0 : ℝ) 1 → ∀ x,
      ProbabilityTheory.cdf (κ a) x = t → x = Q (a, t) := by
    intro a t ht x hx
    obtain ⟨z, hz, hu⟩ := hex a t ht
    exact (hu x hx).trans (hu (Q (a, t)) (hsolve a t ht)).symm
  refine ⟨Q, hQ, ?_, hsolve, ?_⟩
  · intro a
    exact map_inverse_cdf_eq (κ a) (hQ.comp (measurable_const.prodMk measurable_id))
      (hsolve a) (huniq a)
  · intro a t ht
    apply continuousAt_monotone_inverse (ProbabilityTheory.monotone_cdf (κ a)) _ (huniq a t ht)
    filter_upwards [isOpen_Ioo.mem_nhds ht] with s hs
    exact hsolve a s hs

/-- CDF sections of a real-valued Markov kernel are measurable. -/
lemma measurable_cdf_kernel_section {A : Type*} [MeasurableSpace A]
    (κ : ProbabilityTheory.Kernel A ℝ) [ProbabilityTheory.IsMarkovKernel κ] (q : ℝ) :
    Measurable (fun a => ProbabilityTheory.cdf (κ a) q) := by
  simp_rw [ProbabilityTheory.cdf_eq_real]
  exact (κ.measurable_coe measurableSet_Iic).ennreal_toReal

/-- Kernel specialization: unique interior CDF fibers suffice for a jointly
measurable sampler with the exact conditional law and continuous fibers. -/
theorem exists_measurable_cdf_kernel_transport
    {A : Type*} [MeasurableSpace A] (κ : ProbabilityTheory.Kernel A ℝ)
    [ProbabilityTheory.IsMarkovKernel κ]
    (hex : ∀ a t, t ∈ Ioo (0 : ℝ) 1 → ∃! x : ℝ, ProbabilityTheory.cdf (κ a) x = t) :
    ∃ Q : A × ℝ → ℝ, Measurable Q ∧
      (∀ a, Measure.map (fun t => Q (a, t)) (volume.restrict (Ioo (0 : ℝ) 1)) = κ a) ∧
      (∀ a t, t ∈ Ioo (0 : ℝ) 1 → ProbabilityTheory.cdf (κ a) (Q (a, t)) = t) ∧
      ∀ a t, t ∈ Ioo (0 : ℝ) 1 → ContinuousAt (fun s => Q (a, s)) t :=
  exists_measurable_cdf_family_transport (fun a => κ a)
    (measurable_cdf_kernel_section κ) hex

end Problem358

end

/-
The quantile construction follows Mathlib.Probability.Kernel.Representation
(copyright 2025 Gaëtan Serré; authors Gaëtan Serré and Rémy Degenne),
retaining its order information for the midpoint-coupling application.
License: Apache License 2.0.

This code has been modified.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Set ENNReal unitInterval Filter Topology Function

namespace Problem358.KernelQuantile
variable {X : Type*} [MeasurableSpace X]

/-- Ordered generalized inverse of the kernel's conditional distribution function. -/
def quantile (κ : Kernel X I) (a : X) (t : I) : I :=
  sSup {x | (κ a).real (Icc 0 x) < t}

lemma measurable_quantile (κ : Kernel X I) [IsMarkovKernel κ] :
    Measurable (uncurry (quantile κ)) := by
  refine measurable_of_Ioi fun a ↦ ?_
  simp only [preimage, uncurry, mem_Ioi]
  have h_monotone s : Monotone (fun x ↦ (κ s).real (Icc 0 x)) :=
    fun x y hxy ↦ measureReal_mono (by gcongr)
  have sSup_eq_iUnion_rat : {x : X × I | a < quantile κ x.1 x.2} =
      ⋃ (q : ℚ) (hqI : ↑q ∈ I) (_ : a < (q : ℝ)), {e | (κ e.1).real (Icc 0 ⟨q, hqI⟩) < e.2} := by
    ext e
    simp_all only [lt_sSup_iff, mem_ofPred_eq, Subtype.exists, mem_Icc, Rat.cast_nonneg,
      mem_iUnion, exists_prop, exists_and_left, quantile]
    constructor
    · rintro ⟨y, hyI, y_mem, (hy : a.1 < y)⟩
      obtain ⟨q, hqa, hqy⟩ := exists_rat_btwn hy
      refine ⟨q, hqa, ⟨?_, hqy.le.trans hyI.2⟩, lt_of_lt_of_le' y_mem (h_monotone e.1 hqy.le)⟩
      simp [← Rat.cast_nonneg (K := ℝ), a.2.1.trans hqa.le]
    · intro he
      obtain ⟨q, hqa, hqI, h⟩ := he
      refine ⟨q, ⟨by simp [hqI.1], hqI.2⟩, h, ?_⟩
      change a.1 < q
      simp [hqa]
  rw [sSup_eq_iUnion_rat]
  refine MeasurableSet.iUnion (fun b ↦ MeasurableSet.iUnion
    (fun bI ↦ MeasurableSet.iUnion (fun _ ↦ ?_)))
  refine measurableSet_lt ?_ measurable_snd.subtype_val
  simp_rw [measureReal_def]
  have hκ := κ.measurable_coe (s := Icc 0 ⟨b, bI⟩) measurableSet_Icc
  fun_prop

lemma monotone_quantile (κ : Kernel X I) (a : X) : Monotone (quantile κ a) := by
  intro t u htu
  apply sSup_le_sSup
  intro x hx
  change (κ a).real (Icc 0 x) < (u : ℝ)
  exact lt_of_lt_of_le hx htu

/-- The defining order equivalence, including the endpoints of the parameter interval. -/
lemma quantile_le_iff (κ : Kernel X I) [IsMarkovKernel κ] (a : X) (ξ x : I) :
    quantile κ a ξ ≤ x ↔ (ξ : ℝ) ≤ (κ a).real (Icc 0 x) := by
  constructor
  · intro (hξ : quantile κ a ξ ≤ x)
    by_cases hx : x = 1
    · simp [hx, ← univ_eq_Icc, ξ.2.2]
    let g := fun y ↦ (κ a).real (Icc 0 y)
    let nebot : NeBot (𝓝[>] x) := by
      refine nhdsGT_neBot_of_exists_gt ?_
      use 1
      exact lt_of_le_of_ne x.2.2 hx
    refine le_of_tendsto_of_tendsto (b := 𝓝[>] x) (g := g) continuousWithinAt_const ?_ ?_
    · let h := cdf ((κ a).map Subtype.val)
      have h_continuousWithinAt := continuousWithinAt_Ioi_iff_Ici.mpr (h.right_continuous x)
      simp_rw [g, ← unitInterval.cdf_eq_real (κ a)]
      exact h_continuousWithinAt.comp (Continuous.continuousWithinAt (by fun_prop)) (fun y hy ↦ hy)
    · refine eventually_nhdsWithin_of_forall fun y hy ↦ ?_
      by_contra! h
      simp only [sSup_le_iff, quantile] at hξ
      specialize hξ y h
      grind
  · intro (hξ : ξ ≤ (κ a).real (Icc 0 x))
    simp only [sSup_le_iff, quantile]
    intro c hc
    by_contra! h
    have h_lt : ¬ (κ a).real (Icc 0 x) ≤ (κ a).real (Icc 0 c) := not_le.mpr (lt_of_le_of_lt' hξ hc)
    refine h_lt ?_
    gcongr
    simp

lemma map_quantile (κ : Kernel X I) [IsMarkovKernel κ] (a : X) :
    volume.map (quantile κ a) = κ a := by
  apply (volume.map (quantile κ a)).ext_of_Iic (κ a)
  intro x
  have Iic_to_Icc : Iic x = Icc 0 x := by ext; simp
  have κ_in_I : ((κ a).real (Icc 0 x)) ∈ I := ⟨measureReal_nonneg, measureReal_le_one⟩
  simp_rw [volume.map_apply (measurable_quantile κ).of_uncurry_left measurableSet_Iic,
    preimage, mem_Iic, Iic_to_Icc, ← ofReal_measureReal (measure_ne_top (κ a) _),
    ← volume_Iic ⟨_, κ_in_I⟩]
  congr with ξ
  exact quantile_le_iff κ a ξ x

/-- Every unit-interval probability kernel has a jointly measurable monotone sampler. -/
theorem exists_monotone_unitInterval_sampler (κ : Kernel X I) [IsMarkovKernel κ] :
    ∃ (f : X → I → I), Measurable (uncurry f) ∧ (∀ a, Monotone (f a)) ∧
      ∀ a, volume.map (f a) = κ a :=
  ⟨quantile κ, measurable_quantile κ, monotone_quantile κ, map_quantile κ⟩

/-- At a strictly increasing conditional CDF, the quantile is its ordinary inverse. -/
lemma quantile_eq_of_cdf_eq (κ : Kernel X I) [IsMarkovKernel κ]
    (a : X) (hstrict : StrictMono (fun x : I => (κ a).real (Icc 0 x)))
    {t x : I} (hx : (κ a).real (Icc 0 x) = (t : ℝ)) :
    quantile κ a t = x := by
  apply le_antisymm
  · exact (quantile_le_iff κ a t x).mpr hx.ge
  · apply hstrict.le_iff_le.mp
    rw [hx]
    exact (quantile_le_iff κ a t (quantile κ a t)).mp le_rfl

lemma quantile_cdf (κ : Kernel X I) [IsMarkovKernel κ]
    (a : X) (hstrict : StrictMono (fun x : I => (κ a).real (Icc 0 x))) (x : I) :
    quantile κ a ⟨(κ a).real (Icc 0 x), measureReal_nonneg, measureReal_le_one⟩ = x :=
  quantile_eq_of_cdf_eq κ a hstrict rfl

/-- Clamp affine coordinates into the unit interval. -/
def toUnit (l u x : ℝ) : I :=
  Set.projIcc 0 1 (by norm_num) ((x - l) / (u - l))

/-- Undo affine unit-interval coordinates. -/
def fromUnit (l u : ℝ) (t : I) : ℝ := l + (u - l) * (t : ℝ)

lemma continuous_toUnit (l u : ℝ) : Continuous (toUnit l u) := by
  exact continuous_projIcc.comp (by fun_prop)

lemma continuous_fromUnit (l u : ℝ) : Continuous (fromUnit l u) := by
  unfold fromUnit
  fun_prop

lemma monotone_fromUnit {l u : ℝ} (hlu : l ≤ u) : Monotone (fromUnit l u) := by
  intro t s hts
  change (t : ℝ) ≤ (s : ℝ) at hts
  simpa only [fromUnit, add_comm] using
    add_le_add_left (mul_le_mul_of_nonneg_left hts (sub_nonneg.mpr hlu)) l

lemma fromUnit_toUnit {l u x : ℝ} (hlu : l < u) (hx : x ∈ Icc l u) :
    fromUnit l u (toUnit l u x) = x := by
  have hden : 0 < u - l := sub_pos.mpr hlu
  have ht : (x - l) / (u - l) ∈ Icc (0 : ℝ) 1 := by
    constructor
    · exact div_nonneg (sub_nonneg.mpr hx.1) hden.le
    · apply (div_le_iff₀ hden).mpr
      linarith [hx.2]
  simp only [toUnit, Set.projIcc_of_mem _ ht, fromUnit]
  field_simp
  ring

/-- Ordered conditional sampling is available uniformly for any kernel supported in a
fixed nondegenerate bounded real interval. -/
theorem exists_monotone_real_sampler (κ : Kernel X ℝ) [IsMarkovKernel κ]
    (l u : ℝ) (hlu : l < u)
    (hsupp : ∀ a, ∀ᵐ x ∂κ a, x ∈ Icc l u) :
    ∃ f : X → I → ℝ, Measurable (uncurry f) ∧ (∀ a, Monotone (f a)) ∧
      (∀ a, volume.map (f a) = κ a) ∧ (∀ a t, f a t ∈ Icc l u) := by
  let c := toUnit l u
  let e := fromUnit l u
  have hc : Measurable c := (continuous_toUnit l u).measurable
  have he : Measurable e := (continuous_fromUnit l u).measurable
  let η := κ.map c
  let : IsMarkovKernel η := Kernel.IsMarkovKernel.map κ hc
  let f : X → I → ℝ := fun a t => e (quantile η a t)
  have hf : Measurable (uncurry f) := he.comp (measurable_quantile η)
  refine ⟨f, hf, fun a => (monotone_fromUnit hlu.le).comp (monotone_quantile η a), ?_, ?_⟩
  · intro a
    change volume.map (e ∘ quantile η a) = κ a
    rw [← Measure.map_map he (measurable_quantile η).of_uncurry_left, map_quantile]
    change Measure.map e ((κ.map c) a) = κ a
    rw [Kernel.map_apply κ hc, Measure.map_map he hc]
    have hident : e ∘ c =ᵐ[κ a] id := by
      filter_upwards [hsupp a] with x hx
      exact fromUnit_toUnit hlu hx
    rw [Measure.map_congr hident, Measure.map_id]
  · intro a t
    change l ≤ l + (u - l) * (quantile η a t : ℝ) ∧
      l + (u - l) * (quantile η a t : ℝ) ≤ u
    constructor
    · nlinarith [mul_nonneg (sub_nonneg.mpr hlu.le) (quantile η a t).property.1]
    · nlinarith [mul_nonneg (sub_nonneg.mpr hlu.le)
        (sub_nonneg.mpr (quantile η a t).property.2)]

/-- A jointly measurable family of normalized bounded densities admits ordered conditional
samples. This is the law-producing part of the triangular quantile construction. -/
theorem exists_monotone_density_sampler
    (p : X → ℝ → ℝ≥0∞) (hp : Measurable (uncurry p))
    (hnorm : ∀ a, ∫⁻ x, p a x = 1) (l u : ℝ) (hlu : l < u)
    (hsupp : ∀ a x, x ∉ Icc l u → p a x = 0) :
    ∃ f : X → I → ℝ, Measurable (uncurry f) ∧ (∀ a, Monotone (f a)) ∧
      (∀ a, volume.map (f a) = volume.withDensity (p a)) ∧
      (∀ a t, f a t ∈ Icc l u) := by
  let κ := (Kernel.const X (volume : Measure ℝ)).withDensity p
  have hκ : ∀ a, κ a = volume.withDensity (p a) := by
    intro a
    exact Kernel.withDensity_apply _ hp a
  let : IsMarkovKernel κ := ⟨fun a => ⟨by
    rw [hκ, MeasureTheory.withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
    exact hnorm a⟩⟩
  have hsupport : ∀ a, ∀ᵐ x ∂κ a, x ∈ Icc l u := by
    intro a
    rw [hκ, MeasureTheory.ae_withDensity_iff hp.of_uncurry_left]
    apply Eventually.of_forall
    intro x hx
    by_contra hnot
    exact hx (hsupp a x hnot)
  obtain ⟨f, hf, hmono, hlaw, hrange⟩ := exists_monotone_real_sampler κ l u hlu hsupport
  exact ⟨f, hf, hmono, fun a => (hlaw a).trans (hκ a), hrange⟩

/-- For a continuous strictly increasing CDF with no endpoint atom, sampling inverts
that CDF in both directions. -/
lemma cdf_quantile (κ : Kernel X I) [IsMarkovKernel κ]
    (a : X) (hstrict : StrictMono (fun x : I => (κ a).real (Icc 0 x)))
    (hcont : Continuous (fun x : I => (κ a).real (Icc 0 x)))
    (hzero : (κ a).real (Icc 0 (0 : I)) = 0) (t : I) :
    (κ a).real (Icc 0 (quantile κ a t)) = (t : ℝ) := by
  have hone : (κ a).real (Icc 0 (1 : I)) = 1 := by
    rw [← unitInterval.univ_eq_Icc]
    simp
  have ht : (t : ℝ) ∈ Icc ((κ a).real (Icc 0 (0 : I)))
      ((κ a).real (Icc 0 (1 : I))) := by
    rw [hzero, hone]
    exact t.property
  obtain ⟨x, hx, hxt⟩ := intermediate_value_Icc (show (0 : I) ≤ 1 from zero_le_one)
    hcont.continuousOn ht
  rw [quantile_eq_of_cdf_eq κ a hstrict hxt]
  exact hxt

lemma strictMono_quantile (κ : Kernel X I) [IsMarkovKernel κ]
    (a : X) (hstrict : StrictMono (fun x : I => (κ a).real (Icc 0 x)))
    (hcont : Continuous (fun x : I => (κ a).real (Icc 0 x)))
    (hzero : (κ a).real (Icc 0 (0 : I)) = 0) :
    StrictMono (quantile κ a) := by
  apply (monotone_quantile κ a).strictMono_of_injective
  intro t u heq
  apply Subtype.ext
  rw [← cdf_quantile κ a hstrict hcont hzero t,
    ← cdf_quantile κ a hstrict hcont hzero u, heq]

end Problem358.KernelQuantile

end

noncomputable section
open MeasureTheory Set Filter Topology

namespace Problem358
namespace PositiveIntervalDensity

/-- The cumulative integral is clamped to its genuine support interval. -/
def clippedCDF (D : PositiveIntervalDensity) (x : ℝ) : ℝ :=
  D.cdf (Set.projIcc D.lower D.upper D.lower_lt_upper.le x)

lemma clippedCDF_of_mem (D : PositiveIntervalDensity) {x : ℝ}
    (hx : x ∈ Icc D.lower D.upper) : D.clippedCDF x = D.cdf x := by
  rw [clippedCDF, Set.projIcc_of_mem _ hx]

lemma clippedCDF_of_le_lower (D : PositiveIntervalDensity) {x : ℝ}
    (hx : x ≤ D.lower) : D.clippedCDF x = 0 := by
  rw [clippedCDF, Set.projIcc_of_le_left D.lower_lt_upper.le hx]
  exact D.cdf_lower

lemma clippedCDF_of_upper_le (D : PositiveIntervalDensity) {x : ℝ}
    (hx : D.upper ≤ x) : D.clippedCDF x = 1 := by
  rw [clippedCDF, Set.projIcc_of_right_le D.lower_lt_upper.le hx]
  exact D.cdf_upper

lemma clippedCDF_monotone (D : PositiveIntervalDensity) : Monotone D.clippedCDF := by
  intro x y hxy
  exact D.cdf_strictMonoOn.monotoneOn
    (Set.projIcc D.lower D.upper D.lower_lt_upper.le x).property
    (Set.projIcc D.lower D.upper D.lower_lt_upper.le y).property
    (Set.monotone_projIcc D.lower_lt_upper.le hxy)

lemma clippedCDF_eq_ite (D : PositiveIntervalDensity) (x : ℝ) :
    D.clippedCDF x = if x ≤ D.lower then 0 else if D.upper ≤ x then 1 else D.cdf x := by
  by_cases hlo : x ≤ D.lower
  · rw [ite_eq_left hlo, D.clippedCDF_of_le_lower hlo]
  · rw [ite_eq_right hlo]
    by_cases hup : D.upper ≤ x
    · rw [ite_eq_left hup, D.clippedCDF_of_upper_le hup]
    · rw [ite_eq_right hup, D.clippedCDF_of_mem ⟨(lt_of_not_ge hlo).le, (lt_of_not_ge hup).le⟩]

lemma existsUnique_clippedCDF_eq (D : PositiveIntervalDensity) {t : ℝ}
    (ht : t ∈ Ioo (0 : ℝ) 1) : ∃! x : ℝ, D.clippedCDF x = t := by
  refine ⟨D.quantileReal t, ?_, ?_⟩
  · change D.clippedCDF (D.quantileReal t) = t
    rw [D.clippedCDF_of_mem (D.quantileReal_mem t)]
    exact D.cdf_quantileReal ⟨ht.1.le, ht.2.le⟩
  · intro x hx
    have hlo : D.lower < x := by
      by_contra h
      rw [D.clippedCDF_of_le_lower (le_of_not_gt h)] at hx
      linarith [ht.1]
    have hup : x < D.upper := by
      by_contra h
      rw [D.clippedCDF_of_upper_le (le_of_not_gt h)] at hx
      linarith [ht.2]
    rw [D.clippedCDF_of_mem ⟨hlo.le, hup.le⟩] at hx
    exact D.cdf_strictMonoOn.injOn ⟨hlo.le, hup.le⟩ (D.quantileReal_mem t)
      (hx.trans (D.cdf_quantileReal ⟨ht.1.le, ht.2.le⟩).symm)

lemma measurable_clippedCDF_section {A : Type*} [MeasurableSpace A]
    (D : A → PositiveIntervalDensity)
    (hlower : Measurable (fun a => (D a).lower))
    (hupper : Measurable (fun a => (D a).upper))
    (hcdf : ∀ q : ℝ, Measurable (fun a => (D a).cdf q)) (q : ℝ) :
    Measurable (fun a => (D a).clippedCDF q) := by
  simp_rw [clippedCDF_eq_ite]
  exact Measurable.ite (measurableSet_le measurable_const hlower) measurable_const
    (Measurable.ite (measurableSet_le hupper measurable_const) measurable_const (hcdf q))

/-- A family of positive interval densities admits a jointly measurable family
of exact quantile samplers. Endpoints and cumulative-integral sections must be
measurable in the parameter; no parameter differentiability is required. -/
theorem exists_measurable_quantile_family {A : Type*} [MeasurableSpace A]
    (D : A → PositiveIntervalDensity)
    (hlower : Measurable (fun a => (D a).lower))
    (hupper : Measurable (fun a => (D a).upper))
    (hcdf : ∀ q : ℝ, Measurable (fun a => (D a).cdf q)) :
    ∃ Q : A × ℝ → ℝ, Measurable Q ∧
      (∀ a t, t ∈ Ioo (0 : ℝ) 1 → Q (a, t) = (D a).quantileReal t) ∧
      (∀ a, Measure.map (fun t => Q (a, t)) (volume.restrict (Ioo (0 : ℝ) 1)) =
        (D a).densityMeasure) ∧
      ∀ a t, t ∈ Ioo (0 : ℝ) 1 →
        HasDerivAt (fun s => Q (a, s)) ((D a).density (Q (a, t)))⁻¹ t := by
  classical
  let level : ℝ → ℝ := (Ioo (0 : ℝ) 1).piecewise id (fun _ => 1 / 2)
  have hmlevel : Measurable level := measurable_id.piecewise measurableSet_Ioo measurable_const
  have hlevel (t : ℝ) : level t ∈ Ioo (0 : ℝ) 1 := by
    by_cases ht : t ∈ Ioo (0 : ℝ) 1
    · simpa only [level, piecewise_eq_of_mem _ _ _ ht, id_eq] using ht
    · simp only [level, piecewise_eq_of_notMem _ _ _ ht]
      norm_num
  have hlevel_eq {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) : level t = t := by
    simp only [level, piecewise_eq_of_mem _ _ _ ht, id_eq]
  obtain ⟨Q, hQ, hsolve₀⟩ := exists_measurable_monotone_inverse
    (fun (p : A × ℝ) x => (D p.1).clippedCDF x)
    (fun p : A × ℝ => level p.2)
    (fun p => (D p.1).clippedCDF_monotone)
    (fun q => (measurable_clippedCDF_section D hlower hupper hcdf q).comp measurable_fst)
    (hmlevel.comp measurable_snd)
    (fun p => (D p.1).existsUnique_clippedCDF_eq (hlevel p.2))
  have hmatch : ∀ a t, t ∈ Ioo (0 : ℝ) 1 → Q (a, t) = (D a).quantileReal t := by
    intro a t ht
    have hx : (D a).clippedCDF (Q (a, t)) = t :=
      (hsolve₀ (a, t)).trans (hlevel_eq ht)
    obtain ⟨z, hz, hu⟩ := (D a).existsUnique_clippedCDF_eq ht
    have hq : (D a).clippedCDF ((D a).quantileReal t) = t := by
      rw [(D a).clippedCDF_of_mem ((D a).quantileReal_mem t)]
      exact (D a).cdf_quantileReal ⟨ht.1.le, ht.2.le⟩
    exact (hu _ hx).trans (hu _ hq).symm
  refine ⟨Q, hQ, hmatch, ?_, ?_⟩
  · intro a
    calc
      Measure.map (fun t => Q (a, t)) (volume.restrict (Ioo (0 : ℝ) 1)) =
          Measure.map (D a).quantileReal (volume.restrict (Ioo (0 : ℝ) 1)) := by
        apply Measure.map_congr
        filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
        exact hmatch a t ht
      _ = (D a).densityMeasure := (D a).map_quantileReal_uniform
  · intro a t ht
    rw [hmatch a t ht]
    apply ((D a).quantileReal_hasDerivAt ht).congr_of_eventuallyEq
    filter_upwards [isOpen_Ioo.mem_nhds ht] with s hs
    exact hmatch a s hs

lemma clippedCDF_mem_unitInterval (D : PositiveIntervalDensity) (x : ℝ) :
    D.clippedCDF x ∈ Icc (0 : ℝ) 1 := by
  rw [← D.cdf_image]
  exact ⟨Set.projIcc D.lower D.upper D.lower_lt_upper.le x,
    (Set.projIcc D.lower D.upper D.lower_lt_upper.le x).property, rfl⟩

/-- The clamped primitive is the actual probability CDF of the density law. -/
lemma cdf_densityMeasure_eq_clippedCDF (D : PositiveIntervalDensity) (x : ℝ) :
    ProbabilityTheory.cdf D.densityMeasure x = D.clippedCDF x := by
  have hbounds := D.clippedCDF_mem_unitInterval x
  have hm : D.densityMeasure (Iic x) = ENNReal.ofReal (D.clippedCDF x) := by
    rw [← D.map_quantileReal_uniform,
      Measure.map_apply D.quantileReal_continuous.measurable measurableSet_Iic,
      Measure.restrict_apply (D.quantileReal_continuous.measurable measurableSet_Iic)]
    have heq : D.quantileReal ⁻¹' Iic x ∩ Ioo (0 : ℝ) 1 =
        Iic (D.clippedCDF x) ∩ Ioo (0 : ℝ) 1 := by
      ext t
      simp only [mem_inter_iff, mem_preimage, mem_Iic]
      have hequiv (ht : t ∈ Ioo (0 : ℝ) 1) :
          D.quantileReal t ≤ x ↔ t ≤ D.clippedCDF x := by
        have hq : D.clippedCDF (D.quantileReal t) = t := by
          rw [D.clippedCDF_of_mem (D.quantileReal_mem t)]
          exact D.cdf_quantileReal ⟨ht.1.le, ht.2.le⟩
        apply unique_monotone_inverse_le_iff D.clippedCDF_monotone hq
        intro y hy
        obtain ⟨z, hz, hu⟩ := D.existsUnique_clippedCDF_eq ht
        exact (hu y hy).trans (hu _ hq).symm
      constructor
      · rintro ⟨hx, ht⟩
        exact ⟨(hequiv ht).mp hx, ht⟩
      · rintro ⟨hx, ht⟩
        exact ⟨(hequiv ht).mpr hx, ht⟩
    rw [heq, volume_Iic_inter_unitInterval _ hbounds.2]
  have hh := congrArg ENNReal.toReal ((ProbabilityTheory.ofReal_cdf D.densityMeasure x).trans hm)
  simpa only [ENNReal.toReal_ofReal (ProbabilityTheory.cdf_nonneg D.densityMeasure x),
    ENNReal.toReal_ofReal hbounds.1] using hh

lemma existsUnique_probability_cdf_eq (D : PositiveIntervalDensity) {t : ℝ}
    (ht : t ∈ Ioo (0 : ℝ) 1) :
    ∃! x : ℝ, ProbabilityTheory.cdf D.densityMeasure x = t := by
  simpa only [D.cdf_densityMeasure_eq_clippedCDF] using D.existsUnique_clippedCDF_eq ht

/-- A measurable kernel of positive interval-density laws has jointly
measurable quantiles with exact conditional laws and inverse-density derivatives.
No measurability of chosen support endpoints is separately required. -/
theorem exists_measurable_density_kernel_quantiles {A : Type*} [MeasurableSpace A]
    (D : A → PositiveIntervalDensity) (κ : ProbabilityTheory.Kernel A ℝ)
    [ProbabilityTheory.IsMarkovKernel κ]
    (hκ : ∀ a, κ a = (D a).densityMeasure) :
    ∃ Q : A × ℝ → ℝ, Measurable Q ∧
      (∀ a, Measure.map (fun t => Q (a, t)) (volume.restrict (Ioo (0 : ℝ) 1)) = κ a) ∧
      (∀ a t, t ∈ Ioo (0 : ℝ) 1 → Q (a, t) = (D a).quantileReal t) ∧
      ∀ a t, t ∈ Ioo (0 : ℝ) 1 →
        HasDerivAt (fun s => Q (a, s)) ((D a).density (Q (a, t)))⁻¹ t := by
  have hex : ∀ a t, t ∈ Ioo (0 : ℝ) 1 →
      ∃! x : ℝ, ProbabilityTheory.cdf (κ a) x = t := by
    intro a t ht
    rw [hκ a]
    exact (D a).existsUnique_probability_cdf_eq ht
  obtain ⟨Q, hQ, hlaw, hsolve, hcont⟩ := exists_measurable_cdf_kernel_transport κ hex
  have hmatch : ∀ a t, t ∈ Ioo (0 : ℝ) 1 → Q (a, t) = (D a).quantileReal t := by
    intro a t ht
    have hsol := hsolve a t ht
    rw [hκ a, (D a).cdf_densityMeasure_eq_clippedCDF] at hsol
    have hq : (D a).clippedCDF ((D a).quantileReal t) = t := by
      rw [(D a).clippedCDF_of_mem ((D a).quantileReal_mem t)]
      exact (D a).cdf_quantileReal ⟨ht.1.le, ht.2.le⟩
    obtain ⟨z, hz, hu⟩ := (D a).existsUnique_clippedCDF_eq ht
    exact (hu _ hsol).trans (hu _ hq).symm
  refine ⟨Q, hQ, hlaw, hmatch, ?_⟩
  intro a t ht
  rw [hmatch a t ht]
  apply ((D a).quantileReal_hasDerivAt ht).congr_of_eventuallyEq
  filter_upwards [isOpen_Ioo.mem_nhds ht] with s hs
  exact hmatch a s hs

end PositiveIntervalDensity
end Problem358

end

end OAI
