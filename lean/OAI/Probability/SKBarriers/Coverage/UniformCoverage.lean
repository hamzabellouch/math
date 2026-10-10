import Mathlib
import OAI.Probability.SKBarriers.Coverage.CoverageTrimming
import OAI.Probability.SKBarriers.Coverage.CoverageProbability

namespace OAI

section

section
noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic

def freshCoverageGain (n : ℕ) (b q : ℝ) : ℝ :=
  b^2*((n:ℝ)-1)/4-Real.log 2-
    Real.sqrt (2*(logPartitionProxy b n:ℝ)*(b^2*(n:ℝ)*q^2/2+Real.log 8))-
    Real.sqrt (2*(logPartitionProxy b n:ℝ)*Real.log 2)

def coveragePairBad (n : ℕ) (β m r q : ℝ) : Set (Disorder n) :=
  {J | ∃ S : Finset (Config n), m ≤ finiteMass (gibbs β J) S ∧
    finiteOverlapMass (gibbs β J) S q < r*(finiteMass (gibbs β J) S)^2}

theorem continuous_gibbsMass {n : ℕ} (β : ℝ) (S : Finset (Config n)) :
    Continuous (fun J : Disorder n => finiteMass (gibbs β J) S) :=
  continuous_finsetSum _ (fun x _ => continuous_gibbs β x)

theorem continuous_gibbsOverlapMass {n : ℕ} (β q : ℝ) (S : Finset (Config n)) :
    Continuous (fun J : Disorder n => finiteOverlapMass (gibbs β J) S q) := by
  apply continuous_finsetSum
  intro x _
  apply continuous_finsetSum
  intro y _
  by_cases h : q ≤ |overlap x y|
  · simp only [ite_eq_left h]
    exact (continuous_gibbs β x).mul (continuous_gibbs β y)
  · simp only [ite_eq_right h]
    exact continuous_const

theorem measurableSet_coveragePairBad (n : ℕ) (β m r q : ℝ) :
    MeasurableSet (coveragePairBad n β m r q) := by
  have heq : coveragePairBad n β m r q = ⋃ S : Finset (Config n),
      {J | m ≤ finiteMass (gibbs β J) S} ∩
      {J | finiteOverlapMass (gibbs β J) S q < r*(finiteMass (gibbs β J) S)^2} := by
    ext J
    simp [coveragePairBad]
  rw [heq]
  apply MeasurableSet.iUnion
  intro S
  exact (measurableSet_le measurable_const (continuous_gibbsMass β S).measurable).inter
    (measurableSet_lt (continuous_gibbsOverlapMass β q S).measurable
      (measurable_const.mul ((continuous_gibbsMass β S).measurable.pow_const 2)))

theorem measurable_gibbsEnergyTail {n : ℕ} (β e : ℝ) :
    Measurable (gibbsEnergyTail (N := n) β e) := by
  apply Finset.measurable_sum
  intro x _
  exact Measurable.ite (measurableSet_lt measurable_const (continuous_hamiltonian x).measurable)
    (continuous_gibbs β x).measurable measurable_const

theorem coveragePairBad_probability_le {n : ℕ} (hn : 0 < n)
    {β θ m r q e ε u : ℝ} (hβ : 0 ≤ β) (hm : 0 < m) (hr : 0 ≤ r) (hq : 0 ≤ q)
    (hb : β*Real.sin θ ≠ 0) (hε : ε ≤ m/2) (hu : 0 ≤ u)
    (hsecond : 4*r*Real.exp ((β*Real.sin θ)^2*(n:ℝ)/2) ≤
      Real.exp ((β*Real.sin θ)^2*(n:ℝ)*q^2/2))
    (hgain : u ≤ Real.log (m/2)+β*(Real.cos θ-1)*(n:ℝ)*e+
      freshCoverageGain n (β*Real.sin θ) q) :
    (disorderLaw n).real (coveragePairBad n β m r q) ≤
      (disorderLaw n).real {J | ε < gibbsEnergyTail β e J}+
      2*Real.exp (-u^2/(θ^2*β^2*(n:ℝ))) := by
  let A := coveragePairBad n β m r q ∩ {J | gibbsEnergyTail β e J ≤ ε}
  let E : Set (Disorder n × Disorder n) :=
    {p | u ≤ logPartition β (rotateDisorder θ p).1-logPartition β p.1}
  have hA : MeasurableSet A := (measurableSet_coveragePairBad n β m r q).inter
    (measurableSet_le (measurable_gibbsEnergyTail β e) measurable_const)
  have hE : MeasurableSet E := measurableSet_le measurable_const
    ((((continuous_logPartition β).comp (rotateDisorderCLM n θ).continuous.fst).sub
      ((continuous_logPartition β).comp continuous_fst)).measurable)
  have hsec (J : Disorder n) (hJ : J ∈ A) :
      (1/2:ℝ) ≤ (disorderLaw n).real {G | (J,G) ∈ E} := by
    obtain ⟨S,hS,hraw⟩ := hJ.1
    have htail : gibbsEnergyTail β e J ≤ ε := hJ.2
    let T := energyTrim J e S
    have hST : T ⊆ S := Finset.filter_subset _ _
    have htrim := gibbsMass_energyTrim β e J S
    have hmS : 0 < finiteMass (gibbs β J) S := hm.trans_le hS
    have hhalf : finiteMass (gibbs β J) S/2 ≤ finiteMass (gibbs β J) T := by
      dsimp only [T]
      linarith
    have hmT : 0 < finiteMass (gibbs β J) T := by linarith
    have hratio : finiteMass (gibbs β J) S/finiteMass (gibbs β J) T ≤ 2 := by
      apply (div_le_iff₀ hmT).mpr
      linarith
    have hratio0 : 0 ≤ finiteMass (gibbs β J) S/finiteMass (gibbs β J) T :=
      div_nonneg hmS.le hmT.le
    have hcondS : weightedOverlapMass (conditionalWeights (gibbs β J) S) q ≤ r := by
      rw [weightedOverlapMass_conditional]
      exact (div_le_iff₀ (sq_pos_of_pos hmS)).mpr hraw.le
    have hcondT : weightedOverlapMass (conditionalWeights (gibbs β J) T) q ≤ 4*r := by
      apply (weightedOverlapMass_conditional_mono (gibbs β J)
        (fun x => (gibbs_pos β J x).le) hST hmT q).trans
      have HH := mul_le_mul_of_nonneg_left hcondS
        (sq_nonneg (finiteMass (gibbs β J) S/finiteMass (gibbs β J) T))
      have Hsq : (finiteMass (gibbs β J) S/finiteMass (gibbs β J) T)^2 ≤ 4 := by
        nlinarith
      exact HH.trans (mul_le_mul_of_nonneg_right Hsq hr)
    have hg := weightedPartition_half_gain hn (conditionalWeights (gibbs β J) T)
      (conditionalWeights_nonneg (gibbs β J) (fun x => (gibbs_pos β J x).le) T)
      (conditionalWeights_sum (gibbs β J) T hmT) (β*Real.sin θ) q hb hq
      ((mul_le_mul_of_nonneg_right hcondT (Real.exp_nonneg _)).trans hsecond)
    apply hg.trans
    apply measureReal_mono (μ := disorderLaw n) _ (measure_ne_top _ _)
    intro G hG
    have hmix := logPartition_mix_lower hβ (Real.cos_le_one θ) (Real.sin θ) e J G T hmT
      (fun x hx => (Finset.mem_filter.mp hx).2)
    have hmass : Real.log (m/2) ≤ Real.log (finiteMass (gibbs β J) T) :=
      Real.log_le_log (by positivity) (by linarith)
    change u ≤ logPartition β (mixDisorder (Real.cos θ) (Real.sin θ) (J,G))-
      logPartition β J
    change freshCoverageGain n (β*Real.sin θ) q ≤ _ at hG
    linarith
  have Hint := product_event_lower_of_sections (disorderLaw n) (disorderLaw n)
    hA hE (by norm_num : (0:ℝ) ≤ 1/2) hsec
  have Htail := rotation_logPartition_tail hn β θ u hu
  have Hbad : coveragePairBad n β m r q ⊆ A ∪ {J | ε < gibbsEnergyTail β e J} := by
    intro J hJ
    by_cases h : gibbsEnergyTail β e J ≤ ε
    · exact Or.inl ⟨hJ,h⟩
    · exact Or.inr (lt_of_not_ge h)
  have HB := (measureReal_mono (μ := disorderLaw n) Hbad (measure_ne_top _ _)).trans (measureReal_union_le A {J | ε < gibbsEnergyTail β e J})
  change (1/2)*(disorderLaw n).real A ≤ (disorderPairLaw n).real E at Hint
  change (disorderPairLaw n).real E ≤ _ at Htail
  linarith
end SK.Analytic

end
end

end

end OAI
