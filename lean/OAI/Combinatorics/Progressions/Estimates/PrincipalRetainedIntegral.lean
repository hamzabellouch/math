import OAI.Combinatorics.Progressions.Estimates.AllocatedEnormousProfiles

namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem principalRetained_bounded_comparison {D α V : Type*}
    [Fintype D] [DecidableEq D] [Fintype α] [DecidableEq α]
    (B : D → Type*) [∀ d, Fintype (B d)] [∀ d, DecidableEq (B d)] (h : D → ℕ)
    (L : PrincipalTupleIndex B h → ℕ) (hL : ∀ j, 0 < L j) (m : ℕ) [NeZero m] (hm : 0 < m)
    (hsize : ∀ j, (Fintype.card α+1)*m ≤ L j) (tv : Finset V)
    (spatial : PrincipalIntegerTuples B h α L → PMF V)
    (site : (PrincipalTupleIndex B h → Option α → ZMod m) → V → ℂ)
    (C : PrincipalIntegerTuples B h α L → V → ℂ)
    (T : (PrincipalTupleIndex B h → Option α → ZMod m) → V → ℂ)
    {δ ε : ℝ} (hδ : 0 ≤ δ) (hε : 0 ≤ ε)
    (hC : ∀ y, (principalTupleWeights (α := α) B h L hL).weight y ≠ 0 → ∀ v ∈ tv, ‖C y v‖ ≤ 1)
    (hspatial : ∀ y, (principalTupleWeights (α := α) B h L hL).weight y ≠ 0 →
      ∀ v ∈ tv, ‖((spatial y v).toReal : ℂ)-site (principalResidueLabel m y) v‖ ≤ δ)
    (hcoeff : ∀ r v, v ∈ tv →
      ‖(principalResidueWeights B h L hL m hm r hsize).complexMean (fun y => C y v)-T r v‖ ≤ ε) :
    let p := principalTupleWeights (α := α) B h L hL
    let q := p.fiberLaw (principalResidueLabel m)
    ‖p.complexMean (fun y => ∑ v ∈ tv, ((spatial y v).toReal : ℂ)*C y v)-
      q.complexMean (fun r => ∑ v ∈ tv, site r v*T r v)‖ ≤
      δ*tv.card+(1+δ*tv.card)*ε := by
  dsimp only
  let p := principalTupleWeights (α := α) B h L hL
  let q := p.fiberLaw (principalResidueLabel m)
  have hsite (r) : (∑ v ∈ tv, ‖site r v‖) ≤ 1+δ*tv.card := by
    obtain ⟨y, hyr, hy⟩ := principalResidue_positive_witness B h L hL m hm hsize r
    apply pmf_proxy_norm_mass (spatial y) tv (site r)
    intro v hv
    simpa only [hyr] using hspatial y hy v hv
  have hfirst : ‖p.complexMean (fun y => ∑ v ∈ tv, ((spatial y v).toReal : ℂ)*C y v)-
      p.complexMean (fun y => ∑ v ∈ tv, site (principalResidueLabel m y) v*C y v)‖ ≤ δ*tv.card := by
    apply (p.norm_complexMean_sub_le _ _ (fun _ => δ*tv.card) ?_).trans_eq (p.mean_const _)
    intro y hy
    rw [← Finset.sum_sub_distrib]
    apply (norm_sum_le _ _).trans
    calc
      _ ≤ ∑ _v ∈ tv, δ := by
        apply Finset.sum_le_sum
        intro v hv
        rw [← sub_mul, norm_mul]
        exact (mul_le_mul (hspatial y hy v hv) (hC y hy v hv) (norm_nonneg _) hδ).trans_eq (mul_one _)
      _ = δ*tv.card := by simp [mul_comm]
  have hmid : p.complexMean (fun y => ∑ v ∈ tv, site (principalResidueLabel m y) v*C y v) =
      q.complexMean (fun r => ∑ v ∈ tv, site r v*
        (principalResidueWeights B h L hL m hm r hsize).complexMean (fun y => C y v)) := by
    rw [principalTuple_complex_disintegrate B h L hL m hm hsize
      (fun r y => ∑ v ∈ tv, site r v*C y v)]
    simp_rw [FiniteProbabilityWeights.complexMean_finset_sum,
      FiniteProbabilityWeights.complexMean_mul_left]
    rfl
  have hsecond : ‖q.complexMean (fun r => ∑ v ∈ tv, site r v*
        (principalResidueWeights B h L hL m hm r hsize).complexMean (fun y => C y v))-
      q.complexMean (fun r => ∑ v ∈ tv, site r v*T r v)‖ ≤ (1+δ*tv.card)*ε := by
    apply (q.norm_complexMean_sub_le _ _ (fun _ => (1+δ*tv.card)*ε) ?_).trans_eq (q.mean_const _)
    intro r _
    rw [← Finset.sum_sub_distrib]
    apply (norm_sum_le _ _).trans
    calc
      _ ≤ ∑ v ∈ tv, ‖site r v‖*ε := by
        apply Finset.sum_le_sum
        intro v hv
        rw [← mul_sub, norm_mul]
        exact mul_le_mul_of_nonneg_left (hcoeff r v hv) (norm_nonneg _)
      _ = (∑ v ∈ tv, ‖site r v‖)*ε := (Finset.sum_mul _ _ _).symm
      _ ≤ (1+δ*tv.card)*ε := mul_le_mul_of_nonneg_right (hsite r) hε
  rw [hmid] at hfirst
  exact (norm_sub_le_norm_sub_add_norm_sub _ _ _).trans (add_le_add hfirst hsecond)

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators

theorem principalRetained_integral_comparison {D α V X Y : Type*}
    [Fintype D] [DecidableEq D] [Fintype α] [DecidableEq α]
    [MeasurableSpace X] [MeasurableSpace Y]
    (B : D → Type*) [∀ d, Fintype (B d)] [∀ d, DecidableEq (B d)] (h : D → ℕ)
    (L : PrincipalTupleIndex B h → ℕ) (hL : ∀ j, 0 < L j) (m : ℕ) [NeZero m] (hm : 0 < m)
    (hsize : ∀ j, (Fintype.card α+1)*m ≤ L j) (tv : Finset V)
    (spatial : PrincipalIntegerTuples B h α L → PMF V)
    (site : (PrincipalTupleIndex B h → Option α → ZMod m) → V → ℂ)
    (μ : Measure X) [IsProbabilityMeasure μ]
    (F : PrincipalIntegerTuples B h α L → X → Y) (hF : ∀ y, Measurable (F y))
    (T : (PrincipalTupleIndex B h → Option α → ZMod m) → V → ℂ)
    {δ ε : ℝ} (hδ : 0 ≤ δ) (hε : 0 ≤ ε)
    (hspatial : ∀ y, (principalTupleWeights (α := α) B h L hL).weight y ≠ 0 →
      ∀ v ∈ tv, ‖((spatial y v).toReal : ℂ)-site (principalResidueLabel m y) v‖ ≤ δ)
    (φ : V → Y → ℂ) (hφ : ∀ v ∈ tv, Measurable (φ v))
    (hb : ∀ v ∈ tv, ∀ z, ‖φ v z‖ ≤ 1)
    (hcoeff : ∀ r v, v ∈ tv →
      ‖(∫ z, (principalResidueWeights B h L hL m hm r hsize).complexMean
        (fun y => φ v (F y z)) ∂μ)-T r v‖ ≤ ε) :
    let p := principalTupleWeights (α := α) B h L hL
    let q := p.fiberLaw (principalResidueLabel m)
    ‖(∫ z, p.complexMean (fun y => ∑ v ∈ tv, ((spatial y v).toReal : ℂ)*φ v (F y z)) ∂μ)-
      q.complexMean (fun r => ∑ v ∈ tv, site r v*T r v)‖ ≤
      δ*tv.card+(1+δ*tv.card)*ε := by
  dsimp only
  let p := principalTupleWeights (α := α) B h L hL
  have hi (y) (v) (hv : v ∈ tv) : Integrable (fun z => φ v (F y z)) μ :=
    (integrable_const (1 : ℝ)).mono' ((hφ v hv).comp (hF y)).aestronglyMeasurable
      (ae_of_all μ (fun z => hb v hv (F y z)))
  have hC (y) (_hy : p.weight y ≠ 0) (v) (hv : v ∈ tv) :
      ‖∫ z, φ v (F y z) ∂μ‖ ≤ 1 := by
    simpa only [probReal_univ, mul_one] using
      norm_integral_le_of_norm_le_const (ae_of_all μ (fun z => hb v hv (F y z)))
  have hc (r) (v) (hv : v ∈ tv) :
      ‖(principalResidueWeights B h L hL m hm r hsize).complexMean
        (fun y => ∫ z, φ v (F y z) ∂μ)-T r v‖ ≤ ε := by
    rw [← (principalResidueWeights B h L hL m hm r hsize).integral_complexMean μ
      (fun z y => φ v (F y z)) (fun y => hi y v hv)]
    exact hcoeff r v hv
  have hsource :
      (∫ z, p.complexMean (fun y => ∑ v ∈ tv, ((spatial y v).toReal : ℂ)*φ v (F y z)) ∂μ) =
        p.complexMean (fun y => ∑ v ∈ tv, ((spatial y v).toReal : ℂ)*(∫ z, φ v (F y z) ∂μ)) := by
    rw [p.integral_complexMean μ _ (fun y =>
      integrable_finsetSum _ (fun v hv => (hi y v hv).const_mul _))]
    congr 1
    funext y
    rw [integral_finsetSum _ (fun v hv => (hi y v hv).const_mul _)]
    simp only [integral_const_mul]
  rw [hsource]
  exact principalRetained_bounded_comparison B h L hL m hm hsize tv spatial site
    (fun y v => ∫ z, φ v (F y z) ∂μ) T hδ hε hC hspatial hc

end Erdos3

end

end OAI
