import Mathlib
import OAI.Analysis.BiholderTransport.CostGeometry.Slack
import OAI.Analysis.BiholderTransport.Coordinates.NormalCoordinates3

namespace OAI

noncomputable section
open Set Filter Manifold Bundle
open scoped Topology ContDiff

namespace WeakMTWTransport
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

lemma WeakMTW.finite_scaled_transverse_positive
    (hmtw : WeakMTW (n := n) (M := M))
    {ι : Type*} [Fintype ι] {x : M}
    (p : ι → TangentSpace 𝓘(ℝ,Model n) x) (w : ι → ℝ)
    (hw : ∀ i, 0 ≤ w i) (hsum : ∑ i, w i = 1)
    (hmin : ∀ i, p i ∈ minimizingVectors x)
    {t s : ℝ} (ht : 0 ≤ t) (hts : t < s) (hs : s < 1)
    (hID : ∀ q ∈ convexHull ℝ (range p), t • q ∈ injectivityDomain x)
    {xi : TangentSpace 𝓘(ℝ,Model n) x} (hxi : xi ≠ 0)
    (hle : ∀ i, t * inner ℝ (p i - ∑ j, w j • p j) xi ≤ 0) :
    0 < ∑ i, w i * (hessianValue x (t • ∑ j, w j • p j) xi -
      (t / s) * hessianValue x (s • p i) xi) := by
  rcases eq_or_lt_of_le ht with ht0 | ht0
  · subst t
    simp only [zero_smul,hessianValue_zero,zero_div,zero_mul,sub_zero,←Finset.sum_mul,hsum,one_mul]
    exact sq_pos_of_pos (norm_pos_iff.mpr hxi)
  · let r := ∑ j, w j • p j
    have hneg : ∀ i, inner ℝ (p i-r) xi ≤ 0 := by
      intro i
      exact nonpos_of_mul_nonpos_right (hle i) ht0
    have hmean : ∑ i, w i * inner ℝ (p i-r) xi = 0 := by
      simp only [inner_sub_left,mul_sub,Finset.sum_sub_distrib,←Finset.sum_mul,hsum,one_mul]
      have he : (∑ i, w i * inner ℝ (p i) xi) = inner ℝ r xi := by
        simp only [r,sum_inner,real_inner_smul_left]
      rw [he,sub_self]
    have horth : ∀ i, 0 < w i → inner ℝ xi (p i-r) = 0 := by
      intro i hi
      rw [real_inner_comm]
      exact finite_nonnegative_weight_zero_on_pos w (fun i => inner ℝ (p i-r) xi) hw hneg hmean i hi
    have H := hmtw.finite_nonnegative_transverse_slack_strict p w hw hsum hmin ht0 hts hs hID hxi horth
    have H' := (mul_lt_mul_of_pos_left H ht0)
    have he : t * (hessianValue x (t • r) xi / t) = hessianValue x (t • r) xi := by
      field_simp
    rw [he] at H'
    have heq : (∑ i, w i * (hessianValue x (t • r) xi -
        (t/s)*hessianValue x (s • p i) xi)) =
        hessianValue x (t • r) xi - t * ∑ i, w i * (hessianValue x (s • p i) xi / s) := by
      simp only [mul_sub,Finset.sum_sub_distrib,←Finset.sum_mul,hsum,one_mul]
      rw [Finset.mul_sum]
      congr 1
      apply Finset.sum_congr rfl
      intro i _
      ring
    rw [heq]
    exact sub_pos.mpr H'

end WeakMTWTransport

end

end OAI
