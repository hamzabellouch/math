import OAI.Probability.BenjaminiSchramm.PeakFrontierTruncation
import OAI.Probability.BenjaminiSchramm.LayerFrontierExpectation

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped Classical ENNReal

namespace Percolation.BenjaminiSchramm
variable {V E : Type*} [Countable V] [Countable E] (G : BondGraph V E)

lemma lowerFrontier_partition_measure (hloc : LocallyFinite G) (p : unitInterval)
    (I J : Set E) (x : V) (hfin : ∀ᵐ ω ∂law p, (cluster G (ω ∩ I) x).Finite)
    (B : Set (Set E)) (hB : MeasurableSet B) :
    law p B = ∑' A : Finset V × Finset V,
      law p (lowerFrontierCell G I J x (A.1 : Set V) (A.2 : Set V) ∩ B) := by
  have hfin' : ∀ᵐ ω ∂CriticalPercolation.BernoulliProduct.law (fun _ : E => p),
      (cluster G (ω ∩ I) x).Finite := by
    simpa only [CriticalPercolation.BernoulliProduct.law_const,Percolation.law] using hfin
  have hh := lintegral_lowerFrontier_partition G hloc (fun _ : E => p) I J x hfin'
    (B.indicator (fun _ => (1 : ℝ≥0∞))) (measurable_const.indicator hB)
  rw [CriticalPercolation.BernoulliProduct.law_const] at hh
  change (∫⁻ ω, B.indicator (fun _ => (1 : ℝ≥0∞)) ω ∂law p) = _ at hh
  rw [←lintegral_indicator_fun_one hB]
  apply hh.trans
  apply tsum_congr
  intro A
  have he : (lowerFrontierCell G I J x (A.1 : Set V) (A.2 : Set V)).indicator
      (B.indicator (fun _ => (1 : ℝ≥0∞))) =
      (lowerFrontierCell G I J x (A.1 : Set V) (A.2 : Set V) ∩ B).indicator
        (fun _ => (1 : ℝ≥0∞)) := by
    funext ω
    by_cases ha : ω ∈ lowerFrontierCell G I J x (A.1 : Set V) (A.2 : Set V)
    <;> by_cases hb : ω ∈ B <;> simp [Set.indicator,ha,hb]
  rw [he,lintegral_indicator_fun_one ((measurableSet_lowerFrontierCell G I J x _ _).inter hB)]
  rfl

lemma peak_probability_of_frontier_surgery (hloc : LocallyFinite G) (p : unitInterval)
    (I J : Set E) (x : V) (hfin : ∀ᵐ ω ∂law p, (cluster G (ω ∩ I) x).Finite)
    (B : Set (Set E)) (hB : MeasurableSet B) (N L d : ℕ) (δ : ℝ)
    (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1)
    (hlocal : ∀ (S F : Finset V),
      (lowerFrontierCell G I J x (S : Set V) (F : Set V)).Nonempty →
      (0 < F.card ∧ F.card ≤ N) →
      law p (lowerFrontierCell G I J x (S : Set V) (F : Set V))*
        ENNReal.ofReal (δ^(d*(F.card+L+1))) ≤
          law p (lowerFrontierCell G I J x (S : Set V) (F : Set V) ∩ B)) :
    law p {ω | 0 < frontierCount G I J ω x ∧ frontierCount G I J ω x ≤ (N : ℝ≥0∞)}*
      ENNReal.ofReal (δ^(d*(N+L+1))) ≤ law p B := by
  let C : Set (Set E) := {ω | 0 < frontierCount G I J ω x ∧ frontierCount G I J ω x ≤ (N : ℝ≥0∞)}
  have hC : MeasurableSet C :=
    (measurableSet_lt measurable_const (measurable_frontierCount G I J x)).inter
      (measurableSet_le (measurable_frontierCount G I J x) measurable_const)
  rw [show law p {ω | 0 < frontierCount G I J ω x ∧ frontierCount G I J ω x ≤ (N : ℝ≥0∞)}=law p C from rfl,
    lowerFrontier_partition_measure G hloc p I J x hfin C hC,
    lowerFrontier_partition_measure G hloc p I J x hfin B hB,←ENNReal.tsum_mul_right]
  apply ENNReal.tsum_le_tsum
  intro A
  let cell := lowerFrontierCell G I J x (A.1 : Set V) (A.2 : Set V)
  by_cases hgood : 0 < A.2.card ∧ A.2.card ≤ N
  · by_cases hcell : cell.Nonempty
    · calc
        _ ≤ law p cell*ENNReal.ofReal (δ^(d*(N+L+1))) := mul_le_mul' (measure_mono Set.inter_subset_left) le_rfl
        _ ≤ law p cell*ENNReal.ofReal (δ^(d*(A.2.card+L+1))) :=
          mul_le_mul' le_rfl (ENNReal.ofReal_le_ofReal (pow_le_pow_of_le_one hδ hδ1 (Nat.mul_le_mul_left d (by omega))))
        _ ≤ _ := hlocal A.1 A.2 hcell hgood
    · have he : cell=∅ := Set.not_nonempty_iff_eq_empty.mp hcell
      change law p (cell ∩ C)*_ ≤ law p (cell ∩ B)
      simp only [he,Set.empty_inter,measure_empty,zero_mul,le_refl]
  · have he : cell ∩ C=∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      rintro ω ⟨hω,hωC⟩
      have hcard := frontierCount_eq_card_on_cell G I J x _ A.2 hω
      have hgood' : (0 : ℝ≥0∞) < (A.2.card : ℝ≥0∞) ∧ (A.2.card : ℝ≥0∞) ≤ (N : ℝ≥0∞) := by
        simpa only [C,Set.mem_ofPred_eq,hcard] using hωC
      exact hgood (by exact_mod_cast hgood')
    change law p (cell ∩ C)*_ ≤ _
    rw [he,measure_empty,zero_mul]
    exact bot_le

end Percolation.BenjaminiSchramm

end

end OAI
