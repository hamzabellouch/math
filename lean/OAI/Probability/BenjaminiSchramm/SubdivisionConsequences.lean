import OAI.Probability.BenjaminiSchramm.Consequences
import OAI.Probability.BenjaminiSchramm.SubdivisionGeometry
import OAI.Probability.BenjaminiSchramm.EventMeasurability

namespace OAI

open MeasureTheory
open scoped Topology

namespace Percolation.BenjaminiSchramm

universe u v
variable {V : Type u} {E : Type v}

theorem percolationProbability_subdivision [Countable V] [Countable E]
    (G : BondGraph V E) (hloc : LocallyFinite G) (q : unitInterval) (x : V) :
    percolationProbability (subdivision G) q (.inl x) =
      percolationProbability G (q ^ 2) x := by
  unfold percolationProbability
  congr 1
  rw [← law_map_subdivisionOpen G q,
    Measure.map_apply (measurable_subdivisionOpen G)
      (measurableSet_infinite_cluster (subdivision G) (.inl x)),
    ← law_map_seriesOpen q,
    Measure.map_apply measurable_seriesOpen (measurableSet_infinite_cluster G x)]
  congr 1
  ext ν
  exact not_congr (finite_cluster_subdivision_iff G hloc ν x)

theorem subdivision_parameter_gap [Countable V] [Countable E]
    (G : BondGraph V E) (hloc : LocallyFinite G) (q : unitInterval) :
    ((q ^ 2 : unitInterval) : ℝ) - (pc G : ℝ) =
      ((q : ℝ) - pc (subdivision G)) * ((q : ℝ) + pc (subdivision G)) := by
  have hc := congrArg Subtype.val (pc_subdivision_sq G hloc)
  change (q : ℝ) ^ 2 - (pc G : ℝ) = _
  change (pc (subdivision G) : ℝ) ^ 2 = (pc G : ℝ) at hc
  rw [← hc]
  ring

theorem probabilityLaw_of_subdivision [Countable V] [Countable E]
    (G : BondGraph V E) (hloc : LocallyFinite G) (hqt : QuasiTransitive G)
    (hθ : PercolationProbabilityLaw (subdivision G)) :
    PercolationProbabilityLaw G := by
  have hc : (0 : ℝ) < pc (subdivision G) :=
    pc_pos (subdivision G) (subdivision_locallyFinite G hloc)
      (subdivision_quasiTransitive G hloc hqt)
  intro x
  obtain ⟨c, C, δ, hcp, hCp, hδ, hb⟩ := hθ (.inl x)
  refine ⟨c / 2, C / (pc (subdivision G) : ℝ), δ * pc (subdivision G),
    by positivity, div_pos hCp hc, mul_pos hδ hc, ?_⟩
  intro p hp hnear
  let q := squareParameter.symm p
  have hq2 : q ^ 2 = p := squareParameter.apply_symm_apply p
  have hq : pc (subdivision G) < q := by
    apply squareParameter.lt_iff_lt.mp
    change pc (subdivision G) ^ 2 < q ^ 2
    rw [pc_subdivision_sq G hloc, hq2]
    exact hp
  have hgap := subdivision_parameter_gap G hloc q
  rw [hq2] at hgap
  have hqreal : (0 : ℝ) < (q : ℝ) - pc (subdivision G) := sub_pos.mpr hq
  have hnearq : (q : ℝ) - pc (subdivision G) < δ := by
    have hprod := mul_nonneg hqreal.le q.2.1
    nlinarith only [hgap, hnear, hprod, hc]
  obtain ⟨hlo, hhi⟩ := hb q hq hnearq
  rw [percolationProbability_subdivision G hloc q x, hq2] at hlo hhi
  have hfac : (q : ℝ) + pc (subdivision G) ≤ 2 :=
    (add_le_add q.2.2 (pc (subdivision G)).2.2).trans_eq (by norm_num)
  have hprod := mul_nonneg hqreal.le (sub_nonneg.mpr hfac)
  have hbound : (p : ℝ) - pc G ≤ 2 * ((q : ℝ) - pc (subdivision G)) := by
    nlinarith only [hgap, hprod]
  constructor
  · have hh := mul_le_mul_of_nonneg_left hbound hcp.le
    nlinarith only [hlo, hh]
  · apply hhi.trans
    rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ hc).mpr
    have hh := mul_le_mul_of_nonneg_left
      (show ((q : ℝ) - pc (subdivision G)) * pc (subdivision G) ≤
          (p : ℝ) - pc G by
        have hprod := mul_nonneg hqreal.le q.2.1
        nlinarith only [hgap, hprod]) hCp.le
    simpa only [mul_assoc] using hh

theorem graphDistance_subdivision (G : BondGraph V E) (x y : V) :
    graphDistance (subdivision G) (.inl x) (.inl y) = 2 * graphDistance G x y :=
  subdivision_ambient_distance G x y

theorem susceptibility_subdivision_bounds [Countable V] [Countable E] [Nonempty V]
    (G : BondGraph V E) (hloc : LocallyFinite G) (hqt : QuasiTransitive G)
    (d : ℕ) (hd : ∀ x, degree G x ≤ d) (q : unitInterval)
    (hq : q < pc (subdivision G)) (x : V) :
    susceptibility G (q ^ 2) x ≤ susceptibility (subdivision G) q (.inl x) ∧
      susceptibility (subdivision G) q (.inl x) ≤
        ((d : ℝ) + 1) * susceptibility G (q ^ 2) x := by
  have hp : q ^ 2 < pc G := by
    rw [← pc_subdivision_sq G hloc]
    exact squareParameter.strictMono hq
  let f := fun ω : Set E => ((cluster G ω x).ncard : ℝ)
  let g := fun ω : Set (SubdivisionEdge G) =>
    ((cluster (subdivision G) ω (.inl x)).ncard : ℝ)
  have hf : Measurable f :=
    (measurable_of_countable (fun n : ℕ => (n : ℝ))).comp (measurable_cluster_ncard G hloc x)
  have hg : Measurable g :=
    (measurable_of_countable (fun n : ℕ => (n : ℝ))).comp
      (measurable_cluster_ncard (subdivision G) (subdivision_locallyFinite G hloc) (.inl x))
  obtain ⟨hfi, hfe⟩ := susceptibility_eq_integral G hloc hqt (q ^ 2) hp x
  obtain ⟨hgi, hge⟩ := susceptibility_eq_integral (subdivision G)
    (subdivision_locallyFinite G hloc) (subdivision_quasiTransitive G hloc hqt) q hq (.inl x)
  have hmpf : MeasurePreserving seriesOpen (law q : Measure (Set (E × Bool))) (law (q ^ 2)) :=
    ⟨measurable_seriesOpen, law_map_seriesOpen q⟩
  have hmpg : MeasurePreserving (subdivisionOpen G)
      (law q : Measure (Set (E × Bool))) (law q) :=
    ⟨measurable_subdivisionOpen G, law_map_subdivisionOpen G q⟩
  have hfic : Integrable (f ∘ seriesOpen) (law q) := hmpf.integrable_comp_of_integrable hfi
  have hgic : Integrable (g ∘ subdivisionOpen G) (law q) := hmpg.integrable_comp_of_integrable hgi
  have hfe' : susceptibility G (q ^ 2) x = ∫ ν, f (seriesOpen ν) ∂law q := by
    rw [hfe, ← law_map_seriesOpen q]
    exact integral_map measurable_seriesOpen.aemeasurable hf.aestronglyMeasurable
  have hge' : susceptibility (subdivision G) q (.inl x) =
      ∫ ν, g (subdivisionOpen G ν) ∂law q := by
    rw [hge, ← law_map_subdivisionOpen G q]
    exact integral_map (measurable_subdivisionOpen G).aemeasurable hg.aestronglyMeasurable
  have hfin : ∀ᵐ ν ∂(law q : Measure (Set (E × Bool))), (cluster G (seriesOpen ν) x).Finite := by
    apply ae_of_ae_map (μ := (law q : Measure (Set (E × Bool))))
      (p := fun ω : Set E => (cluster G ω x).Finite) measurable_seriesOpen.aemeasurable
    rw [law_map_seriesOpen]
    exact subcritical_cluster_finite_ae G (q ^ 2) hp x
  have hb : ∀ᵐ ν ∂(law q : Measure (Set (E × Bool))),
      f (seriesOpen ν) ≤ g (subdivisionOpen G ν) ∧
        g (subdivisionOpen G ν) ≤ ((d : ℝ) + 1) * f (seriesOpen ν) := by
    filter_upwards [hfin] with ν hν
    obtain ⟨hlo, hhi⟩ := subdivision_cluster_ncard_bounds G hloc d hd ν x hν
    constructor
    · dsimp only [f, g]
      exact_mod_cast hlo
    · dsimp only [f, g]
      exact_mod_cast hhi
  rw [hfe', hge']
  refine ⟨integral_mono_ae hfic hgic (hb.mono fun _ h => h.1), ?_⟩
  rw [← integral_const_mul]
  exact integral_mono_ae hgic (hfic.const_mul _) (hb.mono fun _ h => h.2)

theorem susceptibilityLaw_of_subdivision [Countable V] [Countable E] [Nonempty V]
    (G : BondGraph V E) (hloc : LocallyFinite G) (hqt : QuasiTransitive G)
    (hχ : SusceptibilityLaw (subdivision G)) : SusceptibilityLaw G := by
  obtain ⟨d, _hdpos, hd⟩ := exists_degree_bound G hqt
  have hc : (0 : ℝ) < pc (subdivision G) :=
    pc_pos (subdivision G) (subdivision_locallyFinite G hloc)
      (subdivision_quasiTransitive G hloc hqt)
  intro x
  obtain ⟨c, C, δ, hcp, hCp, hδ, hb⟩ := hχ (.inl x)
  refine ⟨c * pc (subdivision G) / ((d : ℝ) + 1), 2 * C, δ * pc (subdivision G),
    by positivity, by positivity, mul_pos hδ hc, ?_⟩
  intro p hp hnear
  let q := squareParameter.symm p
  have hq2 : q ^ 2 = p := squareParameter.apply_symm_apply p
  have hq : q < pc (subdivision G) := by
    apply squareParameter.lt_iff_lt.mp
    change q ^ 2 < pc (subdivision G) ^ 2
    rw [pc_subdivision_sq G hloc, hq2]
    exact hp
  have hgap : (pc G : ℝ) - p =
      ((pc (subdivision G) : ℝ) - q) * ((q : ℝ) + pc (subdivision G)) := by
    have hh := subdivision_parameter_gap G hloc q
    rw [hq2] at hh
    nlinarith only [hh]
  have hqreal : (0 : ℝ) < (pc (subdivision G) : ℝ) - q := sub_pos.mpr hq
  have hnearq : (pc (subdivision G) : ℝ) - q < δ := by
    have hprod := mul_nonneg hqreal.le q.2.1
    nlinarith only [hgap, hnear, hprod, hc]
  obtain ⟨hlo, hhi⟩ := hb q hq hnearq
  obtain ⟨hcomp₁, hcomp₂⟩ := susceptibility_subdivision_bounds G hloc hqt d hd q hq x
  rw [hq2] at hcomp₁ hcomp₂
  have hpReal : (0 : ℝ) < (pc G : ℝ) - p := sub_pos.mpr hp
  have hdReal : (0 : ℝ) < (d : ℝ) + 1 := by positivity
  have hfac : (q : ℝ) + pc (subdivision G) ≤ 2 :=
    (add_le_add q.2.2 (pc (subdivision G)).2.2).trans_eq (by norm_num)
  have hlarge : ((pc (subdivision G) : ℝ) - q) * pc (subdivision G) ≤
      (pc G : ℝ) - p := by
    have hprod := mul_nonneg hqreal.le q.2.1
    nlinarith only [hgap, hprod]
  have hsmall : (pc G : ℝ) - p ≤ 2 * ((pc (subdivision G) : ℝ) - q) := by
    have hprod := mul_nonneg hqreal.le (sub_nonneg.mpr hfac)
    nlinarith only [hgap, hprod]
  constructor
  · have hbound := hlo.trans hcomp₂
    have hh := (div_le_iff₀ hqreal).mp hbound
    apply (div_le_iff₀ hpReal).mpr
    apply (div_le_iff₀ hdReal).mpr
    have hχnonneg := susceptibility_nonneg G p x
    have hmul := mul_le_mul_of_nonneg_right hlarge hχnonneg
    have hmul' := mul_le_mul_of_nonneg_right hh hc.le
    nlinarith only [hmul, hmul']
  · apply hcomp₁.trans
    apply hhi.trans
    apply (div_le_div_iff₀ hqreal hpReal).mpr
    simpa only [mul_assoc, mul_left_comm] using mul_le_mul_of_nonneg_left hsmall hCp.le

theorem PowerTail.of_sandwich {f g : ℕ → ℝ} {α : ℝ} (hg : PowerTail g α)
    (k : ℕ) (hk : 0 < k)
    (hlo : ∀ n, 0 < n → g (k * n) ≤ f n)
    (hhi : ∀ n, 0 < n → f n ≤ g n) : PowerTail f α := by
  obtain ⟨c, C, hc, hC, hb⟩ := hg
  refine ⟨c * (k : ℝ) ^ (-α), C,
    mul_pos hc (Real.rpow_pos_of_pos (Nat.cast_pos.mpr hk) _), hC, ?_⟩
  intro n hn
  constructor
  · calc
      c * (k : ℝ) ^ (-α) * (n : ℝ) ^ (-α) = c * ((k * n : ℕ) : ℝ) ^ (-α) := by
        rw [Nat.cast_mul, Real.mul_rpow (Nat.cast_nonneg k) (Nat.cast_nonneg n)]
        ring
      _ ≤ g (k * n) := (hb (k * n) (Nat.mul_pos hk hn)).1
      _ ≤ f n := hlo n hn
  · exact (hhi n hn).trans (hb n hn).2

theorem PowerTail.of_rescale {f g : ℕ → ℝ} {α : ℝ} (hg : PowerTail g α)
    (k : ℕ) (hk : 0 < k) (heq : ∀ n, 0 < n → f n = g (k * n)) :
    PowerTail f α := by
  obtain ⟨c, C, hc, hC, hb⟩ := hg
  have hkpow : 0 < (k : ℝ) ^ (-α) := Real.rpow_pos_of_pos (Nat.cast_pos.mpr hk) _
  refine ⟨c * (k : ℝ) ^ (-α), C * (k : ℝ) ^ (-α), mul_pos hc hkpow, mul_pos hC hkpow, ?_⟩
  intro n hn
  rw [heq n hn]
  have he (a : ℝ) : a * (k : ℝ) ^ (-α) * (n : ℝ) ^ (-α) =
      a * ((k * n : ℕ) : ℝ) ^ (-α) := by
    rw [Nat.cast_mul, Real.mul_rpow (Nat.cast_nonneg k) (Nat.cast_nonneg n)]
    ring
  rw [he c, he C]
  exact hb (k * n) (Nat.mul_pos hk hn)

theorem subdivision_event_probability_le [Countable V] [Countable E]
    (G : BondGraph V E) (q : unitInterval)
    (A : Set (Set (SubdivisionEdge G))) (B : Set (Set E))
    (hA : MeasurableSet A) (hB : MeasurableSet B)
    (h : ∀ ν, subdivisionOpen G ν ∈ A → seriesOpen ν ∈ B) :
    (law q).real A ≤ (law (q ^ 2)).real B := by
  rw [measureReal_def, measureReal_def,
    ← law_map_subdivisionOpen G q,
    Measure.map_apply (measurable_subdivisionOpen G) hA,
    ← law_map_seriesOpen q, Measure.map_apply measurable_seriesOpen hB]
  apply ENNReal.toReal_mono (measure_ne_top _ _)
  exact measure_mono h

theorem subdivision_event_probability_ge [Countable V] [Countable E]
    (G : BondGraph V E) (q : unitInterval)
    (A : Set (Set (SubdivisionEdge G))) (B : Set (Set E))
    (hA : MeasurableSet A) (hB : MeasurableSet B)
    (h : ∀ ν, seriesOpen ν ∈ B → subdivisionOpen G ν ∈ A) :
    (law (q ^ 2)).real B ≤ (law q).real A := by
  rw [measureReal_def, measureReal_def,
    ← law_map_subdivisionOpen G q,
    Measure.map_apply (measurable_subdivisionOpen G) hA,
    ← law_map_seriesOpen q, Measure.map_apply measurable_seriesOpen hB]
  apply ENNReal.toReal_mono (measure_ne_top _ _)
  exact measure_mono h

theorem criticalTailLaws_of_subdivision [Countable V] [Countable E]
    (G : BondGraph V E) (hloc : LocallyFinite G) (hqt : QuasiTransitive G)
    (h : CriticalTailLaws (subdivision G)) : CriticalTailLaws G := by
  obtain ⟨d, _hd, hd⟩ := exists_degree_bound G hqt
  intro x
  obtain ⟨hv, hi, he⟩ := h (.inl x)
  have hlocH := subdivision_locallyFinite G hloc
  have hpc := pc_subdivision_sq G hloc
  have hvolume₁ (n : ℕ) :
      criticalTail G (volumeEvent G) x n ≤
        criticalTail (subdivision G) (volumeEvent (subdivision G)) (.inl x) n := by
    unfold criticalTail
    rw [← hpc]
    exact subdivision_event_probability_ge G (pc (subdivision G)) _ _
      (measurableSet_volumeEvent _ _ _) (measurableSet_volumeEvent _ _ _)
      (fun ν => subdivision_volumeEvent_lower G ν x n)
  have hvolume₂ (n : ℕ) :
      criticalTail (subdivision G) (volumeEvent (subdivision G)) (.inl x) ((d + 1) * n) ≤
        criticalTail G (volumeEvent G) x n := by
    unfold criticalTail
    rw [← hpc]
    exact subdivision_event_probability_le G (pc (subdivision G)) _ _
      (measurableSet_volumeEvent _ _ _) (measurableSet_volumeEvent _ _ _)
      (fun ν => subdivision_volumeEvent_upper G hloc d hd ν x n)
  have hiEq (n : ℕ) : criticalTail G (intrinsicRadiusEvent G) x n =
      criticalTail (subdivision G) (intrinsicRadiusEvent (subdivision G)) (.inl x) (2 * n) := by
    apply le_antisymm
    · unfold criticalTail
      rw [← hpc]
      exact subdivision_event_probability_ge G (pc (subdivision G)) _ _
        (measurableSet_intrinsicRadiusEvent _ hlocH _ _) (measurableSet_intrinsicRadiusEvent _ hloc _ _)
        (fun ν => (subdivision_intrinsicRadiusEvent G ν x n).mpr)
    · unfold criticalTail
      rw [← hpc]
      exact subdivision_event_probability_le G (pc (subdivision G)) _ _
        (measurableSet_intrinsicRadiusEvent _ hlocH _ _) (measurableSet_intrinsicRadiusEvent _ hloc _ _)
        (fun ν => (subdivision_intrinsicRadiusEvent G ν x n).mp)
  have heEq (n : ℕ) : criticalTail G (extrinsicRadiusEvent G) x n =
      criticalTail (subdivision G) (extrinsicRadiusEvent (subdivision G)) (.inl x) (2 * n) := by
    apply le_antisymm
    · unfold criticalTail
      rw [← hpc]
      exact subdivision_event_probability_ge G (pc (subdivision G)) _ _
        (measurableSet_extrinsicRadiusEvent _ _ _) (measurableSet_extrinsicRadiusEvent _ _ _)
        (fun ν => (subdivision_extrinsicRadiusEvent G ν x n).mpr)
    · unfold criticalTail
      rw [← hpc]
      exact subdivision_event_probability_le G (pc (subdivision G)) _ _
        (measurableSet_extrinsicRadiusEvent _ _ _) (measurableSet_extrinsicRadiusEvent _ _ _)
        (fun ν => (subdivision_extrinsicRadiusEvent G ν x n).mp)
  exact ⟨hv.of_sandwich (d + 1) (by omega) (fun n _ => hvolume₂ n) (fun n _ => hvolume₁ n),
    hi.of_rescale 2 (by norm_num) (fun n _ => hiEq n),
    he.of_rescale 2 (by norm_num) (fun n _ => heEq n)⟩

end Percolation.BenjaminiSchramm

end OAI
