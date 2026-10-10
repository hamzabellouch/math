import OAI.NumberTheory.TotientAsymptotic.FiniteCoefficient

namespace OAI

/-! The exact union-volume coefficient and its finite-tail limit. -/

noncomputable section
open scoped BigOperators Topology
open Filter MeasureTheory
attribute [local instance] Classical.propDecidable

namespace TotientAsymptotic

def witnessFinset (H : ℕ) (s : ℝ) (d : ℕ) : Finset (TailDatum H) :=
  (allTailData H).filter (fun η => η ∈ witnesses H s d)

lemma mem_witnessFinset {H : ℕ} {s : ℝ} {d : ℕ} {η : TailDatum H}
    (hs : s ∈ Set.Ico (0 : ℝ) 1) :
    η ∈ witnessFinset H s d ↔ η ∈ witnesses H s d := by
  simp only [witnessFinset, Finset.mem_filter]
  exact ⟨And.right, fun h => ⟨witness_mem_allTailData hs h.1, h⟩⟩

lemma measurableSet_tailPrefixRegion (x : ℝ) (H : ℕ) (η : TailDatum H) :
    MeasurableSet (tailPrefixRegion x H η) := by
  unfold tailPrefixRegion
  rw [prefixRegion_eq_simplex_preimage]
  exact (prefixAffine_preserves_volume _ _).measurable
    (measurableSet_weightedSimplex _ _)

lemma volume_tailPrefixRegion_ne_top {x : ℝ} {H : ℕ} (hR : 0 < R x H)
    (η : TailDatum H) : volume (tailPrefixRegion x H η) ≠ ⊤ := by
  unfold tailPrefixRegion
  rw [volume_prefixRegion_explicit _ hR]
  exact ENNReal.ofReal_ne_top

def unionVolumeCoefficient (H : ℕ) (f : ℝ → ℝ) (x : ℝ) : ℝ :=
  ∑ d ∈ Finset.Icc 1 (tailValueBound H),
    if IsTotient d then f ((ell d : ℝ)/d)/d *
      (volume (⋃ η ∈ witnessFinset H (theta x) d, tailPrefixRegion x H η)).toReal /
        G x (m x)
    else 0

lemma subset_witnessFinset {H : ℕ} {s : ℝ} {d : ℕ} (hs : s ∈ Set.Ico (0 : ℝ) 1)
    (T : Finset (TailDatum H)) :
    T ⊆ witnessFinset H s d ↔ (↑T : Set (TailDatum H)) ⊆ witnesses H s d := by
  exact ⟨fun h η hη => (mem_witnessFinset hs).mp (h hη),
    fun h η hη => (mem_witnessFinset hs).mpr (h hη)⟩

lemma union_volume_inclusion_exclusion {x : ℝ} {H : ℕ} {s : ℝ}
    (hs : s ∈ Set.Ico (0 : ℝ) 1) (hR : 0 < R x H) (d : ℕ) :
    (volume (⋃ η ∈ witnessFinset H s d, tailPrefixRegion x H η)).toReal =
      ∑ T ∈ nonemptyTailSubsets H,
        if (↑T : Set (TailDatum H)) ⊆ witnesses H s d then
          (-1 : ℝ)^(T.card-1) * (volume (tailIntersection x H T)).toReal else 0 := by
  rw [show (volume (⋃ η ∈ witnessFinset H s d, tailPrefixRegion x H η)).toReal =
      volume.real (⋃ η ∈ witnessFinset H s d, tailPrefixRegion x H η) from rfl,
    measureReal_biUnion_eq_sum_powerset
      (fun η _ => measurableSet_tailPrefixRegion x H η)
      (fun η _ => volume_tailPrefixRegion_ne_top hR η)]
  let W := (witnessFinset H s d).powerset.filter Finset.Nonempty
  have hsub : W ⊆ nonemptyTailSubsets H := by
    intro T hT
    obtain ⟨hTW, hne⟩ := Finset.mem_filter.mp hT
    refine Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr ?_, hne⟩
    exact (Finset.mem_powerset.mp hTW).trans (Finset.filter_subset _ _)
  calc
    _ = ∑ T ∈ W, if (↑T : Set (TailDatum H)) ⊆ witnesses H s d then
        (-1 : ℝ)^(T.card-1)*(volume (tailIntersection x H T)).toReal else 0 := by
      apply Finset.sum_congr rfl
      intro T hT
      obtain ⟨hTW, hne⟩ := Finset.mem_filter.mp hT
      rw [ite_eq_left ((subset_witnessFinset hs T).mp (Finset.mem_powerset.mp hTW))]
      have hc : T.card+1 = T.card-1+2 := by
        have := Finset.card_pos.mpr hne
        omega
      rw [hc, pow_add]
      norm_num
      change (volume (⋂ i ∈ T, tailPrefixRegion x H i)).toReal = _
      congr 2
      ext u
      simp [tailIntersection]
    _ = _ := Finset.sum_subset hsub (by
      intro T hT hnot
      rw [ite_eq_right]
      intro hW
      exact hnot (Finset.mem_filter.mpr
        ⟨Finset.mem_powerset.mpr ((subset_witnessFinset hs T).mpr hW),
          (Finset.mem_filter.mp hT).2⟩))

lemma unionVolumeCoefficient_eq {x : ℝ} {H : ℕ} (f : ℝ → ℝ)
    (hs : theta x ∈ Set.Ico (0 : ℝ) 1) (hR : 0 < R x H) :
    unionVolumeCoefficient H f x = finiteTailCoefficient H f (theta x)
      (fun T => (volume (tailIntersection x H T)).toReal/G x (m x)) := by
  unfold unionVolumeCoefficient finiteTailCoefficient
  apply Finset.sum_congr rfl
  intro d hd
  split_ifs with hdt
  · rw [union_volume_inclusion_exclusion hs hR d, mul_div_assoc]
    congr 1
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro T hT
    split_ifs <;> ring
  · rfl

lemma tendsto_ite_zero {ι : Type*} {l : Filter ι} (p : ι → Prop) (F : ι → ℝ)
    (hF : Tendsto F l (nhds 0)) :
    Tendsto (fun x => if p x then F x else 0) l (nhds 0) := by
  apply squeeze_zero_norm' (a := fun x => ‖F x‖)
  · exact Eventually.of_forall (fun x => by split_ifs <;> simp)
  · simpa using hF.norm

theorem unionVolumeCoefficient_limit (hford : FordRenewalInput) (H : ℕ)
    (f : ℝ → ℝ) :
    Tendsto (fun x => unionVolumeCoefficient H f x-AH H f (theta x)) atTop (nhds 0) := by
  let E : ℕ → Finset (TailDatum H) → ℝ → ℝ := fun d T x =>
    if IsTotient d then
      if (↑T : Set (TailDatum H)) ⊆ witnesses H (theta x) d then
        f ((ell d : ℝ)/d)/d * (-1 : ℝ)^(T.card-1) *
          ((volume (tailIntersection x H T)).toReal/G x (m x)-intersectionWeight (theta x) T)
      else 0
    else 0
  have he (d : ℕ) (T : Finset (TailDatum H)) (hT : T ∈ nonemptyTailSubsets H) :
      Tendsto (E d T) atTop (nhds 0) := by
    by_cases hd : IsTotient d
    · by_cases hadm : ∃ s ∈ Set.Ico (0 : ℝ) 1, ∀ η ∈ T, IsWitness H s η
      · obtain ⟨s, hs, hTs⟩ := hadm
        have hh := (normalized_intersection_volume_limit hford T
          (Finset.mem_filter.mp hT).2 hTs).const_mul
          (f ((ell d : ℝ)/d)/d * (-1 : ℝ)^(T.card-1))
        simpa only [E, ite_eq_left hd] using tendsto_ite_zero
          (fun x => (↑T : Set (TailDatum H)) ⊆ witnesses H (theta x) d) _
          (by simpa using hh)
      · apply tendsto_const_nhds.congr'
        filter_upwards [theta_eventually_mem] with x hx
        dsimp [E]
        rw [ite_eq_left hd, ite_eq_right]
        intro hsub
        exact hadm ⟨theta x, hx, fun η hη => (hsub hη).1⟩
    · simpa only [E, ite_eq_right hd] using (tendsto_const_nhds (x := (0 : ℝ)))
  have hh := tendsto_finsetSum (Finset.Icc 1 (tailValueBound H))
    (fun d _ => tendsto_finsetSum (nonemptyTailSubsets H) (he d))
  simp only [Finset.sum_const_zero] at hh
  apply hh.congr'
  filter_upwards [theta_eventually_mem,
    m_tendsto.eventually (eventually_gt_atTop H)] with x hx hm
  rw [unionVolumeCoefficient_eq f hx (by dsimp [R]; omega),
    AH_eq_finiteTailCoefficient H f hx]
  unfold finiteTailCoefficient
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro d hd
  by_cases hdt : IsTotient d
  · simp only [ite_eq_left hdt]
    rw [← mul_sub, ← Finset.sum_sub_distrib, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro T hT
    dsimp [E]
    rw [ite_eq_left hdt]
    split_ifs <;> ring
  · simp only [E, ite_eq_right hdt, sub_self, Finset.sum_const_zero]

end TotientAsymptotic

end

end OAI
