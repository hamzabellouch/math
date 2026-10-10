import OAI.Probability.BenjaminiSchramm.PeakSprinklingCell
import OAI.Probability.BenjaminiSchramm.PeakLayerCost
import OAI.Probability.BenjaminiSchramm.SprinklingAvoidanceProfile

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped Classical ENNReal BigOperators

namespace CriticalPercolation.BondGraph
open BernoulliProduct Percolation.BenjaminiSchramm
variable {V E : Type*} [Countable V] [Countable E] (G : BondGraph V E)

lemma exactCluster_partition_measure (p : unitInterval) (x : V)
    (hfin : ∀ᵐ ω ∂G.law p, (G.cluster ω x).Finite)
    (B : Set (Set E)) (hB : MeasurableSet B) :
    G.law p B=∑' S : Finset V, G.law p ({ω | G.cluster ω x=(S : Set V)} ∩ B) := by
  have hdis : Pairwise (fun S T : Finset V => Disjoint
      ({ω | G.cluster ω x=(S : Set V)} ∩ B) ({ω | G.cluster ω x=(T : Set V)} ∩ B)) := by
    intro S T hne
    apply Set.disjoint_left.mpr
    rintro ω ⟨hS,_⟩ ⟨hT,_⟩
    exact hne (Finset.coe_injective (hS.symm.trans hT))
  calc
    _ = G.law p (⋃ S : Finset V, {ω | G.cluster ω x=(S : Set V)} ∩ B) := by
      apply measure_congr
      filter_upwards [hfin] with ω hω
      apply propext
      constructor
      · intro hBω
        exact Set.mem_iUnion.mpr ⟨hω.toFinset,hω.coe_toFinset.symm,hBω⟩
      · intro hω'
        obtain ⟨S,_hS,hBω⟩ := Set.mem_iUnion.mp hω'
        exact hBω
    _ = _ := measure_iUnion hdis fun S => (G.measurableSet_exactCluster x _).inter hB

theorem peak_sprinkling_average (q b p : unitInterval)
    (hparam : Percolation.sprinkleParameter q b=p)
    (a : V → ℝ) (R : ℝ) (hR : 0 < R) (ell : ℝ) (x : V)
    (g : ℕ → ℝ) (hg : ∀ l, 0 ≤ g l) (t : ℝ) (ht : 0 ≤ t)
    (hfin : ∀ᵐ ω ∂G.law q, (G.cluster ω x).Finite)
    (havoid : ∀ (S : Finset V) (u : V), u ∈ S → G.orbitAdjustedHeight a x u ≤ 0 →
      Real.exp (-g (-G.adjustedLayerIndex a R 0 x u).toNat) ≤
        (BernoulliProduct.law (fun e => Percolation.sprinkleParameter
          (erasedWhiteParameters (fun _ => q) (G.incidentEdges (S : Set V)) e) b)).real
            (exteriorEscape G.ends (S : Set V) (G.orbitAdjustedHeight a x) x u)ᶜ)
    (B : Set (Set E)) (hB : MeasurableSet B)
    (hBpeak : B ⊆ G.fullPeakDownHit a ell x)
    (hBcost : ∀ ω ∈ B, G.downwardLayerCost a R g ω x ≤ ENNReal.ofReal t) :
    G.law q B*ENNReal.ofReal (Real.exp (-t)) ≤ G.law p (G.fullPeakDownHit a ell x) := by
  let μ := BernoulliProduct.law (pairedParameters (fun _ : E => q) (fun _ => b))
  let C (S : Finset V) : Set (Set (E × Bool)) :=
    ({ω | G.cluster (whiteProjection ω) x=(S : Set V)} ∩
      (pairedUnion ∘ forceOn (whiteBlock (G.incidentEdges (S : Set V))) ∅) ⁻¹'
        G.exteriorAvoidance (S : Set V) a x) ∩ pairedUnion ⁻¹' G.fullPeakDownHit a ell x
  have hCm (S : Finset V) : MeasurableSet (C S) :=
    (((G.measurableSet_exactCluster x _).preimage measurable_whiteProjection).inter
      ((G.measurableSet_exteriorAvoidance _ a x).preimage
        (measurable_pairedUnion.comp (measurable_forceOn _ _)))).inter
      ((G.measurableSet_fullPeakDownHit a ell x).preimage measurable_pairedUnion)
  have hCdis : Pairwise (fun S T : Finset V => Disjoint (C S) (C T)) := by
    intro S T hne
    apply Set.disjoint_left.mpr
    rintro ω ⟨⟨hS,_⟩,_⟩ ⟨⟨hT,_⟩,_⟩
    exact hne (Finset.coe_injective (hS.symm.trans hT))
  have hlocal (S : Finset V) :
      G.law q ({ω | G.cluster ω x=(S : Set V)} ∩ B)*ENNReal.ofReal (Real.exp (-t)) ≤ μ (C S) := by
    by_cases he : ({ω | G.cluster ω x=(S : Set V)} ∩ B).Nonempty
    · obtain ⟨ω,hS,hBω⟩ := he
      have hprop : G.peakDownClusterProperty a ell x (S : Set V) := by
        have hh := (G.fullPeakDownHit_iff_cluster_property a ell x ω).mp (hBpeak hBω)
        rwa [hS] at hh
      have hbelow (u : V) (hu : u ∈ S) : G.orbitAdjustedHeight a x u ≤ 0 := by
        by_cases hux : u=x
        · simp only [hux,G.orbitAdjustedHeight_self,le_refl]
        · exact (hprop.1 u hu hux).le
      have hSc : Percolation.cluster G.ends ω x=(S : Set V) := by
        rwa [←G.cluster_eq_percolationCluster]
      have hcostreal : (∑ u ∈ S, g (-G.adjustedLayerIndex a R 0 x u).toNat) ≤ t := by
        have hh := hBcost ω hBω
        rw [G.downwardLayerCost_of_exact_cluster a R g ω x S hSc
          (fun u hu => (G.nonpositive_height_depth a R hR x u (hbelow u hu)).1)] at hh
        rw [←ENNReal.ofReal_sum_of_nonneg (fun u _ => hg _)] at hh
        exact (ENNReal.ofReal_le_ofReal_iff ht).mp hh
      have hsubset :
          ({η | G.cluster (whiteProjection η) x=(S : Set V)} ∩
            (pairedUnion ∘ forceOn (whiteBlock (G.incidentEdges (S : Set V))) ∅) ⁻¹'
              G.exteriorAvoidance (S : Set V) a x) ⊆ pairedUnion ⁻¹' G.fullPeakDownHit a ell x := by
        rintro η ⟨hη,hηavoid⟩
        exact G.peak_survives_white_cell a ell x _ hprop η hη hηavoid
      have hCeq : C S=
          {η | G.cluster (whiteProjection η) x=(S : Set V)} ∩
            (pairedUnion ∘ forceOn (whiteBlock (G.incidentEdges (S : Set V))) ∅) ⁻¹'
              G.exteriorAvoidance (S : Set V) a x := Set.inter_eq_left.mpr hsubset
      rw [hCeq]
      calc
        _ ≤ G.law q {η | G.cluster η x=(S : Set V)}*
            ENNReal.ofReal (Real.exp (-(∑ u ∈ S, g (-G.adjustedLayerIndex a R 0 x u).toNat))) := by
          apply mul_le_mul' (measure_mono Set.inter_subset_left)
          exact ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr (neg_le_neg hcostreal))
        _ ≤ _ := G.peak_sprinkling_cell_lower q b a x S
          (fun u => g (-G.adjustedLayerIndex a R 0 x u).toNat)
          (fun u hu => havoid S u hu (hbelow u hu))
    · rw [Set.not_nonempty_iff_eq_empty.mp he,measure_empty,zero_mul]
      exact bot_le
  calc
    _ = ∑' S : Finset V, G.law q ({ω | G.cluster ω x=(S : Set V)} ∩ B)*
        ENNReal.ofReal (Real.exp (-t)) := by
      rw [G.exactCluster_partition_measure q x hfin B hB,←ENNReal.tsum_mul_right]
    _ ≤ ∑' S : Finset V, μ (C S) := ENNReal.tsum_le_tsum hlocal
    _ = μ (⋃ S : Finset V, C S) := (measure_iUnion hCdis hCm).symm
    _ ≤ μ (pairedUnion ⁻¹' G.fullPeakDownHit a ell x) := measure_mono
      (Set.iUnion_subset fun S _ h => h.2)
    _ = _ := by
      rw [←Measure.map_apply measurable_pairedUnion (G.measurableSet_fullPeakDownHit a ell x)]
      dsimp [μ]
      rw [paired_union_law,hparam,BernoulliProduct.law_const]
      rfl

theorem weighted_peak_sprinkling_average (O : G.OrbitRepresentatives)
    (q b p : unitInterval) (hparam : Percolation.sprinkleParameter q b=p)
    (a : V → ℝ) (R : ℝ) (hR : 0 < R) (ell : ℝ)
    (g : ℕ → ℝ) (hg : ∀ l, 0 ≤ g l) (t : ℝ) (ht : 0 ≤ t)
    (hfin : ∀ x, ∀ᵐ ω ∂G.law q, (G.cluster ω x).Finite)
    (havoid : ∀ (x : V) (S : Finset V) (u : V), u ∈ S → G.orbitAdjustedHeight a x u ≤ 0 →
      Real.exp (-g (-G.adjustedLayerIndex a R 0 x u).toNat) ≤
        (BernoulliProduct.law (fun e => Percolation.sprinkleParameter
          (erasedWhiteParameters (fun _ => q) (G.incidentEdges (S : Set V)) e) b)).real
            (exteriorEscape G.ends (S : Set V) (G.orbitAdjustedHeight a x) x u)ᶜ)
    (B : V → Set (Set E)) (hB : ∀ x, MeasurableSet (B x))
    (hBpeak : ∀ x, B x ⊆ G.fullPeakDownHit a ell x)
    (hBcost : ∀ x ω, ω ∈ B x → G.downwardLayerCost a R g ω x ≤ ENNReal.ofReal t) :
    ENNReal.ofReal (Real.exp (-t))*(∑ x ∈ O.roots, ENNReal.ofReal (a x)*G.law q (B x)) ≤
      G.fullPeakDownProbability O a p ell := by
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro x _
  calc
    _ = ENNReal.ofReal (a x)*(G.law q (B x)*ENNReal.ofReal (Real.exp (-t))) := by ring
    _ ≤ _ := mul_le_mul' le_rfl (G.peak_sprinkling_average q b p hparam a R hR ell x
      g hg t ht (hfin x) (havoid x) (B x) (hB x) (hBpeak x) (hBcost x))

end CriticalPercolation.BondGraph

end

end OAI
