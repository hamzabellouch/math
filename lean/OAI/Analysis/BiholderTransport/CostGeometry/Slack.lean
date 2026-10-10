import Mathlib
import OAI.Analysis.BiholderTransport.CostGeometry.StrictDividedAction
import OAI.Analysis.BiholderTransport.Regularity.FiniteNonnegativeWeightPos

namespace OAI

noncomputable section
open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

namespace WeakMTWTransport
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

lemma WeakMTW.finite_nonnegative_transverse_slack_strict
    (hmtw : WeakMTW (n := n) (M := M))
    {ι : Type*} [Fintype ι] {x : M} (p : ι → TangentSpace 𝓘(ℝ,Model n) x) (w : ι → ℝ)
    (hw : ∀ i, 0 ≤ w i) (hsum : ∑ i, w i = 1)
    (hmin : ∀ i, p i ∈ minimizingVectors x)
    {t s : ℝ} (ht : 0 < t) (hts : t < s) (hs : s < 1)
    (hID : ∀ q ∈ convexHull ℝ (range p), t • q ∈ injectivityDomain x)
    {xi : TangentSpace 𝓘(ℝ,Model n) x} (hxi : xi ≠ 0)
    (hortho : ∀ i, 0 < w i → inner ℝ xi (p i - ∑ j, w j • p j) = 0) :
    (∑ i, w i * (hessianValue x (s • p i) xi / s)) <
      hessianValue x (t • (∑ i, w i • p i)) xi / t := by
  classical
  let S := Finset.univ.filter (fun i => 0 < w i)
  let r := ∑ i, w i • p i
  let C := convexHull ℝ (range p) ∩ {q | inner ℝ xi q = inner ℝ xi r}
  have hhyper : Convex ℝ {q : TangentSpace 𝓘(ℝ,Model n) x | inner ℝ xi q = inner ℝ xi r} := by
    intro u hu v hv a b ha hb hab
    simp only [mem_ofPred_eq,inner_add_right,real_inner_smul_right] at hu hv ⊢
    rw [hu,hv,←add_mul,hab,one_mul]
  have hC : Convex ℝ C := (convex_convexHull ℝ (range p)).inter hhyper
  have hS : ∀ i ∈ S, p i ∈ C := by
    intro i hi
    refine ⟨subset_convexHull ℝ (range p) (mem_range_self i),?_⟩
    exact sub_eq_zero.mp (by simpa only [inner_sub_right] using hortho i (Finset.mem_filter.mp hi).2)
  have hsumS : ∑ i ∈ S, w i = 1 := by
    have H := sum_filter_positive_weights w hw (fun _ => (1:ℝ))
    simpa only [S,smul_eq_mul,mul_one,hsum] using H
  have hc := hmtw.contracted_transverse_concaveOn_set hC (fun q hq => hID q hq.1)
    (fun u hu v hv => by rw [inner_sub_right,hu.2,hv.2,sub_self])
  have hj := hc.le_map_sum (t := S) (w := w) (p := p) (fun i _ => hw i) hsumS hS
  rw [sum_filter_positive_weights w hw p,
    sum_filter_positive_weights w hw (fun q => hessianValue x (t • p q) xi)] at hj
  simp only [smul_eq_mul] at hj
  have hj' := div_le_div_of_nonneg_right hj ht.le
  rw [Finset.sum_div] at hj'
  have hpos : ∃ i, 0 < w i := by
    by_contra hn
    have hz : ∀ i, w i = 0 := fun i => le_antisymm (le_of_not_gt (fun h => hn ⟨i,h⟩)) (hw i)
    simp only [hz,Finset.sum_const_zero] at hsum
    norm_num at hsum
  obtain ⟨j,hjpos⟩ := hpos
  have hlt : (∑ i, w i * (hessianValue x (s • p i) xi / s)) <
      ∑ i, w i * hessianValue x (t • p i) xi / t := by
    apply Finset.sum_lt_sum
    · intro i _
      rw [mul_div_assoc]
      exact mul_le_mul_of_nonneg_left (divided_hessian_strict_decrease (hmin i) ht hts hs hxi).le (hw i)
    · refine ⟨j,Finset.mem_univ j,?_⟩
      rw [mul_div_assoc]
      exact mul_lt_mul_of_pos_left (divided_hessian_strict_decrease (hmin j) ht hts hs hxi) hjpos
  exact hlt.trans_le hj'

end WeakMTWTransport

end

end OAI
