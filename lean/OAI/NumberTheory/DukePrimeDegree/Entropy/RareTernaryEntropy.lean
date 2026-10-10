import OAI.NumberTheory.DukePrimeDegree.Entropy.HeightObservationEntropy

namespace OAI

/-! # Entropy of a rare three-valued increment

When a three-valued increment is usually the middle value, its entropy
is bounded by binary entropy plus the exceptional mass times `log 2`.
The bound tends to zero with the exceptional mass.
-/

noncomputable section
open MeasureTheory Set Filter
open scoped Topology BigOperators
namespace DukePrimeDegree
open PrimeDegreePackets

lemma negMulLog_pair_le {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    Real.negMulLog a + Real.negMulLog b ≤
      Real.negMulLog (a+b) + (a+b)*Real.log 2 := by
  have hJ := Real.concaveOn_negMulLog.2 ha hb
    (show (0:ℝ)≤1/2 by norm_num) (show (0:ℝ)≤1/2 by norm_num) (by norm_num)
  simp only [smul_eq_mul] at hJ
  have hm : (1/2:ℝ)*a+(1/2)*b=(a+b)/2 := by ring
  rw [hm] at hJ
  have hhalf : Real.negMulLog (1/2:ℝ)=Real.log 2/2 := by
    rw [one_div,Real.negMulLog,Real.log_inv]
    ring
  have hs : 2*Real.negMulLog ((a+b)/2)=Real.negMulLog (a+b)+(a+b)*Real.log 2 := by
    rw [div_eq_mul_inv,Real.negMulLog_mul]
    have he : (2:ℝ)⁻¹=1/2 := by norm_num
    rw [he,hhalf]
    ring
  linarith

def rareTernaryCost (p : ℝ) : ℝ :=
  Real.negMulLog p + Real.negMulLog (1-p) + p*Real.log 2

lemma continuous_rareTernaryCost : Continuous rareTernaryCost := by
  unfold rareTernaryCost
  fun_prop

@[simp] lemma rareTernaryCost_zero : rareTernaryCost 0=0 := by
  simp [rareTernaryCost]

lemma finiteShannon_ternary_le {p : Fin 3 → ℝ} (hp : ∀ i, 0 ≤ p i)
    (hs : ∑ i, p i=1) :
    finiteShannon p ≤ rareTernaryCost (p 0+p 2) := by
  have hpair := negMulLog_pair_le (hp 0) (hp 2)
  have hmid : p 1=1-(p 0+p 2) := by
    rw [Fin.sum_univ_three] at hs
    linarith
  unfold finiteShannon rareTernaryCost
  rw [Fin.sum_univ_three,←hmid]
  linarith

lemma observationEntropy_ternary_le
    {Y : Type*} [MeasurableSpace Y] (μ : Measure Y) [IsProbabilityMeasure μ]
    (D : Y → Fin 3) (hD : Measurable D) :
    observationEntropy μ D ≤ rareTernaryCost (μ.real {y | D y ≠ 1}) := by
  have hd : Disjoint {y | D y=0} {y | D y=2} := by
    rw [Set.disjoint_left]
    intro y h0 h2
    have h : (0:Fin 3)=2 := h0.symm.trans h2
    norm_num at h
  have he : {y | D y≠1} = {y | D y=0} ∪ {y | D y=2} := by
    ext y
    change D y≠1 ↔ D y=0 ∨ D y=2
    generalize hz : D y=z
    fin_cases z <;> simp
  have hm : μ.real {y | D y≠1} = μ.real {y | D y=0} + μ.real {y | D y=2} := by
    rw [he,measureReal_union hd (hD (measurableSet_singleton 2))]
  rw [hm]
  exact finiteShannon_ternary_le (fun _ => measureReal_nonneg)
    (observation_distribution_sum μ D (fun i => hD (measurableSet_singleton i)))

lemma rareTernaryCost_small {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ p : ℝ, 0 ≤ p → p < δ → rareTernaryCost p < ε := by
  have hlim : Tendsto rareTernaryCost (𝓝 0) (𝓝 0) := by
    simpa only [rareTernaryCost_zero] using continuous_rareTernaryCost.tendsto (0:ℝ)
  have hnear := hlim.eventually (gt_mem_nhds hε)
  obtain ⟨δ,hδ,hball⟩ := Metric.mem_nhds_iff.mp hnear
  refine ⟨δ,hδ,?_⟩
  intro p hp hpδ
  apply hball
  simpa only [Metric.mem_ball,Real.dist_eq,sub_zero,abs_of_nonneg hp] using hpδ

end DukePrimeDegree

end

end OAI
