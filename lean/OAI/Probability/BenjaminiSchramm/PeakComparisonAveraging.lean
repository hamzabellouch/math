import OAI.Probability.BenjaminiSchramm.PeakCountComparison

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped Classical ENNReal BigOperators

namespace Percolation.BenjaminiSchramm
variable {V E : Type*} [Countable V] [Countable E] (G : BondGraph V E)

theorem peak_layer_comparison_averaged_in_domain (p : unitInterval)
    (D D' K J : Set E) (hKD : K ⊆ D) (hJD : J ⊆ D) (hJK : Disjoint J K)
    (hKD' : K ⊆ D') (hJD' : J ⊆ D')
    (x : V) (U T W : Set V) (b : ℝ≥0∞)
    (hfin : ∀ v, ∀ᵐ ω ∂law p, (cluster G (ω ∩ D) v).Finite)
    (hbound : ∀ u ∈ U, b ≤
      ∑' w, if w ∈ W then law p (connectionAvoidingHit G D J u w T) else 0) :
    law p ((restrictedHit G D x T)ᶜ ∩ restrictedHit G K x U)*b ≤
      ∫⁻ ω, (restrictedHit G D x T)ᶜ.indicator
        (fun ω => restrictedLayerCount G D' W ω x) ω ∂law p := by
  let P := (restrictedHit G D x T)ᶜ
  let ι := {A : Finset V // ((A : Set V) ∩ U).Nonempty ∧ Disjoint (A : Set V) T}
  let C (i : ι) : Set (Set E) := {ω | cluster G (ω ∩ K) x=(i.val : Set V)} ∩ P
  have hm (i : ι) : MeasurableSet (C i) :=
    (measurableSet_restricted_exactCluster G K x _).inter
      (measurableSet_restrictedHit G D x T).compl
  have hd : Pairwise (fun i j : ι => Disjoint (C i) (C j)) := by
    intro i j hij
    apply Set.disjoint_left.mpr
    rintro ω ⟨hi,_⟩ ⟨hj,_⟩
    exact hij (Subtype.ext (Finset.coe_injective (hi.symm.trans hj)))
  have hpart : law p (P ∩ restrictedHit G K x U)=∑' i : ι, law p (C i) := by
    calc
      _ = law p (⋃ i : ι, C i) := by
        apply measure_congr
        filter_upwards [hfin x] with ω hω
        apply propext
        constructor
        · rintro ⟨hp,u,hu,hxu⟩
          have hfK : (cluster G (ω ∩ K) x).Finite := hω.subset fun v hv =>
            conn_mono G (Set.inter_subset_inter_right _ hKD) hv
          let A := hfK.toFinset
          have hA : cluster G (ω ∩ K) x=(A : Set V) := hfK.coe_toFinset.symm
          have hU : ((A : Set V) ∩ U).Nonempty := ⟨u,hA ▸ hxu,hu⟩
          have hT : Disjoint (A : Set V) T := by
            apply Set.disjoint_left.mpr
            intro v hv hvT
            apply hp
            refine ⟨v,hvT,conn_mono G (Set.inter_subset_inter_right _ hKD) ?_⟩
            change v ∈ cluster G (ω ∩ K) x
            rwa [hA]
          exact Set.mem_iUnion.mpr ⟨⟨A,hU,hT⟩,hA,hp⟩
        · intro hh
          obtain ⟨i,hi,hp⟩ := Set.mem_iUnion.mp hh
          obtain ⟨u,hu,huU⟩ := i.property.1
          refine ⟨hp,u,huU,?_⟩
          change u ∈ cluster G (ω ∩ K) x
          rwa [hi]
      _ = _ := measure_iUnion hd hm
  have hcell (i : ι) : law p (C i)*b ≤
      ∫⁻ ω, (C i).indicator (fun ω => restrictedLayerCount G D' W ω x) ω ∂law p := by
    obtain ⟨u,hu,huU⟩ := i.property.1
    have hJI : J ⊆ D \ (K ∩ ballIncidentEdges G (i.val : Set V)) := by
      intro e he
      exact ⟨hJD he,fun h => Set.disjoint_left.mp hJK he h.1⟩
    have hf : ∀ᵐ ω ∂law p,
        (cluster G (ω ∩ (D \ (K ∩ ballIncidentEdges G (i.val : Set V)))) u).Finite := by
      filter_upwards [hfin u] with ω hω
      exact hω.subset fun v hv => conn_mono G
        (Set.inter_subset_inter_right _ Set.sdiff_subset) hv
    exact (mul_le_mul' le_rfl (hbound u huU)).trans
      (upper_cluster_peak_layer_comparison_in_domain G p D D' K J hKD hKD' hJD' x u _ T W hu i.property.2 hJI hf)
  calc
    _ = ∑' i : ι, law p (C i)*b := by rw [hpart,ENNReal.tsum_mul_right]
    _ ≤ ∑' i : ι, ∫⁻ ω, (C i).indicator
        (fun ω => restrictedLayerCount G D' W ω x) ω ∂law p := ENNReal.tsum_le_tsum hcell
    _ = ∫⁻ ω in ⋃ i : ι, C i, restrictedLayerCount G D' W ω x ∂law p := by
      simp_rw [lintegral_indicator (hm _)]
      exact (lintegral_iUnion hm hd _).symm
    _ ≤ ∫⁻ ω in P, restrictedLayerCount G D' W ω x ∂law p := by
      apply lintegral_mono_set
      intro ω hω
      obtain ⟨i,hi⟩ := Set.mem_iUnion.mp hω
      exact hi.2
    _ = _ := (lintegral_indicator (measurableSet_restrictedHit G D x T).compl
      (fun ω => restrictedLayerCount G D' W ω x)).symm

theorem peak_layer_comparison_averaged (p : unitInterval)
    (D K J : Set E) (hKD : K ⊆ D) (hJD : J ⊆ D) (hJK : Disjoint J K)
    (x : V) (U T W : Set V) (b : ℝ≥0∞)
    (hfin : ∀ v, ∀ᵐ ω ∂law p, (cluster G (ω ∩ D) v).Finite)
    (hbound : ∀ u ∈ U, b ≤
      ∑' w, if w ∈ W then law p (connectionAvoidingHit G D J u w T) else 0) :
    law p ((restrictedHit G D x T)ᶜ ∩ restrictedHit G K x U)*b ≤
      ∫⁻ ω, (restrictedHit G D x T)ᶜ.indicator
        (fun ω => restrictedLayerCount G D W ω x) ω ∂law p :=
  peak_layer_comparison_averaged_in_domain G p D D K J hKD hJD hJK hKD hJD x U T W b hfin hbound

end Percolation.BenjaminiSchramm

end

end OAI
