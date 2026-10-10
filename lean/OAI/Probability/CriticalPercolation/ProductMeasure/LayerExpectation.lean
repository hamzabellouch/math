import Mathlib
import OAI.Probability.CriticalPercolation.ProductMeasure.TailProduct
import OAI.Probability.CriticalPercolation.Criticality.TwoPoint
import OAI.Probability.CriticalPercolation.Criticality.LayerCounting
import OAI.Probability.CriticalPercolation.Exploration.LayerExposure

namespace OAI

section
noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped Classical ENNReal BigOperators

namespace CriticalPercolation

def vertexCount {V : Type*} (S : Set V) : ℝ≥0∞ := ∑' x : V, if x∈S then 1 else 0

lemma vertexCount_finite {V : Type*} (S : Set V) (hS : S.Finite) :
    vertexCount S=S.ncard := by
  unfold vertexCount
  rw [tsum_eq_sum (s := hS.toFinset) (fun x hx => ite_eq_right (fun h => hx (hS.mem_toFinset.mpr h)))]
  rw [Set.ncard_eq_toFinset_card S hS]
  calc
    _ = ∑ x∈hS.toFinset, (1:ℝ≥0∞) := by
      apply Finset.sum_congr rfl
      intro x hx
      exact ite_eq_left (hS.mem_toFinset.mp hx)
    _ = _ := by simp

lemma vertexCount_mono {V : Type*} {S T : Set V} (h : S⊆T) : vertexCount S≤vertexCount T := by
  apply ENNReal.tsum_le_tsum
  intro x
  by_cases hx : x∈S
  · rw [ite_eq_left hx,ite_eq_left (h hx)]
  · rw [ite_eq_right hx]; exact zero_le

lemma measurable_vertexCount {V Ω : Type*} [Countable V] [MeasurableSpace Ω]
    (S : Ω → Set V) (hS : ∀ x, MeasurableSet {ω | x∈S ω}) : Measurable (fun ω => vertexCount (S ω)) := by
  apply Measurable.tsum
  intro x
  exact measurable_const.ite (hS x) measurable_const

lemma lintegral_vertexCount {V Ω : Type*} [Countable V] [MeasurableSpace Ω]
    (μ : Measure Ω) (S : Ω → Set V) (hS : ∀ x, MeasurableSet {ω | x∈S ω}) :
    (∫⁻ ω, vertexCount (S ω) ∂μ)=∑' x, μ {ω | x∈S ω} := by
  unfold vertexCount
  rw [lintegral_tsum (fun x => (measurable_const.ite (hS x) measurable_const).aemeasurable)]
  apply tsum_congr
  intro x
  exact lintegral_indicator_one (hS x)

namespace BondGraph
open BernoulliProduct

variable {V E : Type*} (G : BondGraph V E)

def seedExpectation (q : unitInterval) (D : Set V) (o : V) : ℝ≥0∞ :=
  ∑' x, G.law q {ω | x∈G.entrySeeds D o ω}

def goodEntrySeeds (D H : Set V) (o : V) (N M : ℕ) (ω : Set E) : Set V :=
  G.entrySeeds D o ω ∩ {x | x∉H ∧ ω∈G.boundedDomainFreshExitEvent D Hᶜ x N M}

lemma measurableSet_goodEntrySeed [Countable V] [Countable E]
    (D H : Set V) (o x : V) (N M : ℕ) :
    MeasurableSet {ω | x∈G.goodEntrySeeds D H o N M ω} := by
  by_cases hx : x∈H
  · have he : {ω | x∈G.goodEntrySeeds D H o N M ω}=∅ := by
      ext ω; simp [goodEntrySeeds,hx]
    rw [he]; exact MeasurableSet.empty
  · have he : {ω | x∈G.goodEntrySeeds D H o N M ω}=
        {ω | x∈G.entrySeeds D o ω}∩G.boundedDomainFreshExitEvent D Hᶜ x N M := by
      ext ω; simp [goodEntrySeeds,hx]
    rw [he]
    exact ((blockSigma_le _) _ (G.measurableSet_entrySeed D o x)).inter
      (G.measurableSet_boundedDomainFreshExit D Hᶜ x hx N M)

lemma lintegral_entrySeeds [Countable V] [Countable E]
    (q : unitInterval) (D : Set V) (o : V) :
    (∫⁻ ω, vertexCount (G.entrySeeds D o ω) ∂G.law q)=G.seedExpectation q D o :=
  lintegral_vertexCount _ _ (fun x => (blockSigma_le _) _ (G.measurableSet_entrySeed D o x))

lemma subcritical_seedExpectation_bound [Countable V] [Countable E]
    (hl : G.LocallyFinite) (hq : G.QuasiTransitive)
    (q : unitInterval) (hqc : q<G.criticalProbability) (o : V) :
    ∃ C : ℝ≥0∞, C≠∞ ∧ ∀ D : Set V, G.seedExpectation q D o≤C := by
  let C := ∑' x, ENNReal.ofReal (Sharpness.twoPoint G q o x)
  refine ⟨C,(Sharpness.summable_subcritical_twoPoint G hl hq q hqc o).tsum_ofReal_ne_top,?_⟩
  intro D
  apply ENNReal.tsum_le_tsum
  intro x
  have he : ENNReal.ofReal (Sharpness.twoPoint G q o x)=G.law q (G.hitEvent o {x}) := by
    exact ENNReal.ofReal_toReal (measure_ne_top _ _)
  rw [he]
  apply measure_mono
  intro ω hω
  rw [Sharpness.hit_singleton_eq]
  exact G.entrySeeds_subset_cluster D o ω hω

lemma seedExpectation_self_le [Countable V] [Countable E] (q : unitInterval)
    (D : Set V) (o : V) (ho : o∈D) : 1≤G.seedExpectation q D o := by
  have he : {ω : Set E | o∈G.entrySeeds D o ω}=Set.univ := by
    ext ω
    simp only [Set.mem_ofPred_eq,Set.mem_univ,iff_true]
    exact ⟨SimpleGraph.Reachable.refl o,ho⟩
  have hh := ENNReal.le_tsum (f := fun x => G.law q {ω | x∈G.entrySeeds D o ω}) o
  rw [he,measure_univ] at hh
  exact hh

lemma expected_goodSeeds_lower [Countable V] [Countable E]
    (q : unitInterval) (D H : Set V) (o : V) (N M : ℕ) (θ : ℝ≥0∞)
    (hband : ∀ x, (∃ ω, x∈G.entrySeeds D o ω) → x∉H)
    (hprob : ∀ x, (∃ ω, x∈G.entrySeeds D o ω) →
      θ≤G.law q (G.boundedDomainFreshExitEvent D Hᶜ x N M)) :
    θ*G.seedExpectation q D o≤
      ∫⁻ ω, vertexCount (G.goodEntrySeeds D H o N M ω) ∂G.law q := by
  rw [lintegral_vertexCount _ _ (fun x => G.measurableSet_goodEntrySeed D H o x N M)]
  unfold seedExpectation
  rw [←ENNReal.tsum_mul_left]
  apply ENNReal.tsum_le_tsum
  intro x
  by_cases hx : ∃ ω, x∈G.entrySeeds D o ω
  · have he : {ω | x∈G.goodEntrySeeds D H o N M ω}=
        {ω | x∈G.entrySeeds D o ω}∩G.boundedDomainFreshExitEvent D Hᶜ x N M := by
      ext ω; simp [goodEntrySeeds,hband x hx]
    rw [he,G.entry_good_independent q D H o x (hband x hx) N M,mul_comm θ]
    exact mul_le_mul_right (hprob x hx) _
  · have he : {ω | x∈G.entrySeeds D o ω}=∅ := by
      ext ω
      simp only [Set.mem_ofPred_eq,Set.mem_empty_iff_false,iff_false]
      exact fun hh => hx ⟨ω,hh⟩
    rw [he,measure_empty,mul_zero]
    exact zero_le

lemma expected_layer_expansion [Countable V] [Countable E]
    (hc : G.fullGraph.Connected) (hl : G.LocallyFinite)
    (q : unitInterval) (hqc : q<G.criticalProbability)
    (D H : Set V) (hHD : H⊆D) (o : V) (a T : ℝ) (ha : 0<a) (hT : 0<T)
    (M N K d : ℕ) (hMK : (M:ℝ)≤a*K) (hd : ∀ v, (G.incidentEdges {v}).ncard≤d)
    (θ : ℝ≥0∞)
    (hband : ∀ ω x, x∈G.entrySeeds D o ω →
      x∉H ∧ a*T≤G.modularRatio x o ∧ G.modularRatio x o≤T)
    (hprob : ∀ x, (∃ ω, x∈G.entrySeeds D o ω) →
      θ≤G.law q (G.boundedDomainFreshExitEvent D Hᶜ x N M)) :
    N*θ*G.seedExpectation q D o≤(K*d)*G.seedExpectation q H o := by
  have hcount : ∀ᵐ ω ∂G.law q, (N:ℝ≥0∞)*vertexCount (G.goodEntrySeeds D H o N M ω)≤
      ((K*d:ℕ):ℝ≥0∞)*vertexCount (G.entrySeeds H o ω) := by
    filter_upwards [G.finite_clusters_ae_of_subcritical q hqc] with ω hω
    have hfD : (G.entrySeeds D o ω).Finite := (hω o).subset (G.entrySeeds_subset_cluster D o ω)
    have hfH : (G.entrySeeds H o ω).Finite := (hω o).subset (G.entrySeeds_subset_cluster H o ω)
    have hfA : (G.goodEntrySeeds D H o N M ω).Finite := hfD.subset Set.inter_subset_left
    have hh := G.layer_seed_counting hc hl D H hHD ω o hfA.toFinset a T ha hT M N K d hMK hd hfH
      (fun x hx => by
        have hx' := hfA.mem_toFinset.mp hx
        exact ⟨hx'.1,(hband ω x hx'.1).1,(hband ω x hx'.1).2.1,(hband ω x hx'.1).2.2,hx'.2.2⟩)
    rw [vertexCount_finite _ hfA,vertexCount_finite _ hfH,Set.ncard_eq_toFinset_card _ hfA]
    exact_mod_cast hh
  have hi := lintegral_mono_ae hcount
  rw [lintegral_const_mul _ (measurable_vertexCount _ (fun x => G.measurableSet_goodEntrySeed D H o x N M)),
    lintegral_const_mul _ (measurable_vertexCount _ (fun x =>
      (blockSigma_le _) _ (G.measurableSet_entrySeed H o x))),G.lintegral_entrySeeds q H o] at hi
  have hlow := G.expected_goodSeeds_lower q D H o N M θ
    (fun x ⟨ω,hω⟩ => (hband ω x hω).1) hprob
  calc
    _ ≤ (N:ℝ≥0∞)*(∫⁻ ω, vertexCount (G.goodEntrySeeds D H o N M ω) ∂G.law q) := by
      simpa only [mul_assoc] using mul_le_mul_right hlow (N:ℝ≥0∞)
    _ ≤ _ := by simpa only [Nat.cast_mul] using hi

end BondGraph
end CriticalPercolation
end
end

end OAI
