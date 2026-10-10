import OAI.Geometry.TranslativeCovering.BinnedTail

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal Topology
open Set Filter MeasureTheory
open scoped ENNReal Topology
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal Topology
open Set Filter MeasureTheory
open scoped ENNReal Topology
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open scoped BigOperators Classical
open MeasureTheory ProbabilityTheory Set
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open Set MeasureTheory
open scoped ENNReal Classical

universe u_1 u_2 u_3

namespace PoissonBinned
open Set Finset MeasureTheory PoissonConfig PoissonDiagrams
open scoped BigOperators ENNReal NNReal
variable {Ω : Type u_1} {T : Type u_2} [MeasurableSpace Ω] [StandardBorelSpace Ω]
variable [Fintype T] [Nonempty T] [DecidableEq T] {I : T → Type u_3}
variable [∀ t,Fintype (I t)] [∀ t,Nonempty (I t)]

theorem bound (r : ℝ≥0) (σ : Measure Ω) [IsProbabilityMeasure σ] [NullSingletonClass σ]
    (E : ∀ t,I t → Set Ω) (hE : ∀ t i,MeasurableSet (E t i))
    (hpos : ∀ t i,0 < (((r:ℝ≥0∞) • σ).real (E t i)))
    (bad : T → T → Prop) [DecidableRel bad] {a q f g B : ℝ}
    (ha : 0 < a) (hf : 0 ≤ f) (hg : 0 ≤ g)
    (hbin : ∀ t,a ≤ (∏ i,((r:ℝ≥0∞) • σ).real (E t i)) ∧
      (∏ i,((r:ℝ≥0∞) • σ).real (E t i)) ≤ 2*a)
    (hself : ∀ t,diagram ((r:ℝ≥0∞) • σ) (E t) (E t) ≤
      (∏ i,((r:ℝ≥0∞) • σ).real (E t i))^2*Real.exp B)
    (hcross : ∀ t u,t ≠ u → diagram ((r:ℝ≥0∞) • σ) (E t) (E u) ≤
      if bad t u then g*(∏ i,((r:ℝ≥0∞) • σ).real (E t i))*(∏ j,((r:ℝ≥0∞) • σ).real (E u j)) else 0)
    (hbad : (((univ : Finset (T×T)).filter (fun p => p.1 ≠ p.2 ∧ bad p.1 p.2)).card:ℝ) ≤
      10*f*q^2*(Fintype.card T:ℝ)^2) :
    (PoissonSample.simpleSample r σ).real {x | ∀ t,witnessCount (E t) x = 0} ≤
      Real.exp (-1/(8*(Real.exp B/(Fintype.card T:ℝ)+10*g*q^2*f))) := by
  let μ := (r:ℝ≥0∞) • σ
  let ν : T → ℝ := fun t => ∏ i,μ.real (E t i)
  let D : T → T → ℝ := fun t u => diagram μ (E t) (E u)
  have hν (t : T) : 0 ≤ ν t ∧ ν t ≤ 2*a := ⟨(ha.trans_le (hbin t).1).le,(hbin t).2⟩
  have hsum := BinnedTail.diagram_sum ν D bad ha (Real.exp_pos B).le hg hν hself hcross
  have hbad' := mul_le_mul_of_nonneg_left hbad (by positivity : 0 ≤ 4*a^2*g)
  have hd : ∑ t,∑ u,D t u ≤
      4*(Fintype.card T:ℝ)*a^2*Real.exp B+40*(Fintype.card T:ℝ)^2*a^2*(g*q^2*f) := by
    nlinarith only [hsum,hbad']
  obtain ⟨hΔ,hprob⟩ := PoissonActualBound.lower_tail r σ E hE hpos
  have hn : 0 < (Fintype.card T:ℝ) := by exact_mod_cast Fintype.card_pos
  have hνsum : (Fintype.card T:ℝ)*a ≤ ∑ t,ν t := by
    simpa only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul] using Finset.sum_le_sum (s := univ) (fun t _ => (hbin t).1)
  have hrat := BinnedTail.ratio hn ha (Real.exp_pos B) (by positivity : 0 ≤ g*q^2*f)
    hνsum hΔ hd
  apply hprob.trans
  apply Real.exp_le_exp.mpr
  change -(∑ t,ν t)^2/(2*(∑ t,∑ u,D t u)) ≤ _
  change 1/(8*(Real.exp B/(Fintype.card T:ℝ)+10*(g*q^2*f))) ≤
    (∑ t,ν t)^2/(2*(∑ t,∑ u,D t u)) at hrat
  simpa only [neg_div,neg_mul,mul_assoc] using neg_le_neg hrat

end PoissonBinned

end OAI
