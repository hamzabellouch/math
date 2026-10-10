import Mathlib
import OAI.Analysis.AffineBernstein.GraphPatchArea

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
namespace AffineBernstein

section GraphBallArea
variable {n : ℕ}

lemma measurableSet_inter_preimage_continuousOn {E F : Type*}
    [MeasurableSpace E] [TopologicalSpace E] [MeasurableSpace F] [TopologicalSpace F]
    [BorelSpace E] [BorelSpace F] {K : Set E} (hK : MeasurableSet K)
    {f : E → F} (hf : ContinuousOn f K) {B : Set F} (hB : MeasurableSet B) :
    MeasurableSet (K ∩ f ⁻¹' B) := by
  have hh := (MeasurableEmbedding.subtype_coe hK).measurableSet_image.mpr
    (hB.preimage hf.domRestrict.measurable)
  convert hh using 1
  ext x
  constructor
  · rintro ⟨hx,hf⟩
    exact ⟨⟨x,hx⟩,hf,rfl⟩
  · rintro ⟨⟨y,hy⟩,hz,rfl⟩
    exact ⟨hy,hz⟩

lemma graph_area_vertical_patch_bound {Ω K : Set (Space n)}
    (hΩ : IsOpen Ω) (hc : Convex ℝ Ω) (hK : MeasurableSet K) (hKΩ : K ⊆ Ω)
    {u : Space n → ℝ} (hu : ContDiffOn ℝ ∞ u Ω)
    (hp : ∀ x ∈ Ω, (hessian u x).PosDef)
    (hm : ∀ x ∈ K, ∀ j, |gradient u x j| ≤ 1)
    {R : ℝ} (hR : 0 ≤ R) (hxR : ∀ x ∈ K, ∀ j, |x j| ≤ R) :
    (∫⁻ x in K, ENNReal.ofReal ((hessian u x).det^(1/((n:ℝ)+2)))) ≤
      (volume (Metric.closedBall (0 : Space n) n))^(1/((n:ℝ)+2)) *
      (volume (Metric.closedBall (0 : Space n) (n*R)))^(1-1/((n:ℝ)+2)) := by
  have hux (x) (hx : x ∈ Ω) := hu.contDiffAt (hΩ.mem_nhds hx)
  apply jacobian_geometric_mean_image_bound hK
    (fun x _ => (hasFDerivAt_id (𝕜 := ℝ) x).hasFDerivWithinAt)
    (fun x hx => ((contDiffAt_gradient (hux x (hKΩ hx))).differentiableAt
      (by simp)).hasFDerivAt.hasFDerivWithinAt)
    (Set.injOn_id K)
    ((gradient_injOn_of_hessian_posDef hΩ hc hu hp).mono hKΩ)
    (by positivity) (by have : (0:ℝ) ≤ n := Nat.cast_nonneg n; rw [div_lt_one (by positivity)]; linarith)
  · intro x hx
    rw [det_fderiv_gradient_eq_hessian (hux x (hKΩ hx)),abs_of_pos (hp x (hKΩ hx)).det_pos]
    simp [ContinuousLinearMap.det]
  · rintro _ ⟨x,hx,rfl⟩
    rw [Metric.mem_closedBall,dist_zero_right]
    exact norm_le_card_of_coord_bound hR (hxR x hx)
  · rintro _ ⟨x,hx,rfl⟩
    rw [Metric.mem_closedBall,dist_zero_right]
    simpa using norm_le_card_of_coord_bound (by norm_num : (0:ℝ)≤1) (hm x hx)

/-- A dimension/radius-only bound for the literal affine area on any measurable
part of a smooth strictly convex graph with |x_i|,|u| ≤ R. This proves the
area-in-a-ball producer without assuming a surface-area or Gauss-map theorem:
two injective coordinate projections supply its Jacobians directly. -/
theorem graph_affine_area_in_box {Ω K : Set (Space n)}
    (hΩ : IsOpen Ω) (hc : Convex ℝ Ω) (hK : MeasurableSet K) (hKΩ : K ⊆ Ω)
    {u : Space n → ℝ} (hu : ContDiffOn ℝ ∞ u Ω)
    (hp : ∀ x ∈ Ω, (hessian u x).PosDef)
    {R : ℝ} (hR : 0 ≤ R) (hxR : ∀ x ∈ K, ∀ j, |x j| ≤ R)
    (huR : ∀ x ∈ K, |u x| ≤ R) :
    (∫⁻ x in K, ENNReal.ofReal ((hessian u x).det^(1/((n:ℝ)+2)))) ≤
      (2*n+1 : ℕ) * ((volume (Metric.closedBall (0 : Space n) n))^(1/((n:ℝ)+2)) *
      (volume (Metric.closedBall (0 : Space n) (n*R)))^(1-1/((n:ℝ)+2))) := by
  classical
  let B0 : Set (Space n) := {p | ∀ j, |p j| ≤ 1}
  let Bp (i : Fin n) : Set (Space n) := {p | 1 ≤ p i ∧ ∀ j, |p j| ≤ |p i|}
  let Bm (i : Fin n) : Set (Space n) := {p | p i ≤ -1 ∧ ∀ j, |p j| ≤ |p i|}
  let K0 := K ∩ gradient u ⁻¹' B0
  let Kp (i : Fin n) := K ∩ gradient u ⁻¹' Bp i
  let Km (i : Fin n) := K ∩ gradient u ⁻¹' Bm i
  let C : ℝ≥0∞ := (volume (Metric.closedBall (0 : Space n) n))^(1/((n:ℝ)+2)) *
    (volume (Metric.closedBall (0 : Space n) (n*R)))^(1-1/((n:ℝ)+2))
  let A := fun x => ENNReal.ofReal ((hessian u x).det^(1/((n:ℝ)+2)))
  have hg : ContinuousOn (gradient u) K := fun x hx =>
    (contDiffAt_gradient (hu.contDiffAt (hΩ.mem_nhds (hKΩ hx)))).continuousAt.continuousWithinAt
  have hmeas0 : MeasurableSet B0 := by
    dsimp [B0]
    rw [Set.ofPred_forall]
    exact MeasurableSet.iInter fun j => measurableSet_le (by fun_prop) measurable_const
  have hmeasp (i : Fin n) : MeasurableSet (Bp i) := by
    change MeasurableSet ({p : Space n | 1 ≤ p i} ∩ {p | ∀ j, |p j| ≤ |p i|})
    apply MeasurableSet.inter (measurableSet_le measurable_const (by fun_prop))
    rw [Set.ofPred_forall]
    exact MeasurableSet.iInter fun j => measurableSet_le (by fun_prop) (by fun_prop)
  have hmeasm (i : Fin n) : MeasurableSet (Bm i) := by
    change MeasurableSet ({p : Space n | p i ≤ -1} ∩ {p | ∀ j, |p j| ≤ |p i|})
    apply MeasurableSet.inter (measurableSet_le (by fun_prop) measurable_const)
    rw [Set.ofPred_forall]
    exact MeasurableSet.iInter fun j => measurableSet_le (by fun_prop) (by fun_prop)
  have hm0 : MeasurableSet K0 := measurableSet_inter_preimage_continuousOn hK hg hmeas0
  have hmp (i : Fin n) : MeasurableSet (Kp i) := measurableSet_inter_preimage_continuousOn hK hg (hmeasp i)
  have hmm (i : Fin n) : MeasurableSet (Km i) := measurableSet_inter_preimage_continuousOn hK hg (hmeasm i)
  have hc0 : (∫⁻ x in K0, A x) ≤ C :=
    graph_area_vertical_patch_bound hΩ hc hm0 (fun _ hx => hKΩ hx.1) hu hp
      (fun _ hx => hx.2) hR (fun _ hx => hxR _ hx.1)
  have hcu := convexOn_of_hessian_posSemidef hΩ hc hu (fun x hx => (hp x hx).posSemidef)
  have hcp (i : Fin n) : (∫⁻ x in Kp i, A x) ≤ C := by
    apply graph_area_dominant_patch_bound hΩ hc (hmp i) (fun _ hx => hKΩ hx.1) hu hp hcu i
    · intro x hx
      have h1 := hx.2.1
      exact ⟨h1.trans (le_abs_self _),hx.2.2⟩
    · exact Or.inl (fun _ hx => lt_of_lt_of_le zero_lt_one hx.2.1)
    · exact hR
    · exact fun _ hx => hxR _ hx.1
    · exact fun _ hx => huR _ hx.1
  have hcm (i : Fin n) : (∫⁻ x in Km i, A x) ≤ C := by
    apply graph_area_dominant_patch_bound hΩ hc (hmm i) (fun _ hx => hKΩ hx.1) hu hp hcu i
    · intro x hx
      have h1 := hx.2.1
      refine ⟨?_,hx.2.2⟩
      have := neg_le_abs (gradient u x i)
      linarith
    · exact Or.inr (fun _ hx => lt_of_le_of_lt hx.2.1 (by norm_num))
    · exact hR
    · exact fun _ hx => hxR _ hx.1
    · exact fun _ hx => huR _ hx.1
  have hcover : K ⊆ K0 ∪ ⋃ i, (Kp i ∪ Km i) := by
    intro x hx
    by_cases hv : ∀ j, |gradient u x j| ≤ 1
    · exact Or.inl ⟨hx,hv⟩
    · obtain ⟨j,hj⟩ := not_forall.mp hv
      obtain ⟨i,_,hi⟩ := Finset.exists_max_image Finset.univ (fun i : Fin n => |gradient u x i|)
        ⟨j,Finset.mem_univ j⟩
      have him : ∀ j, |gradient u x j| ≤ |gradient u x i| := fun j => hi j (Finset.mem_univ j)
      have hia : 1 < |gradient u x i| := (lt_of_not_ge hj).trans_le (him j)
      refine Or.inr (Set.mem_iUnion.mpr ⟨i,?_⟩)
      rcases le_total 0 (gradient u x i) with hsign|hsign
      · left
        refine ⟨hx,?_,him⟩
        rw [abs_of_nonneg hsign] at hia
        exact hia.le
      · right
        refine ⟨hx,?_,him⟩
        rw [abs_of_nonpos hsign] at hia
        linarith
  calc
    (∫⁻ x in K, A x) ≤ ∫⁻ x in K0 ∪ ⋃ i, (Kp i ∪ Km i), A x := lintegral_mono_set hcover
    _ ≤ (∫⁻ x in K0, A x) + ∫⁻ x in ⋃ i, (Kp i ∪ Km i), A x := lintegral_union_le A _ _
    _ ≤ C + ∑' i, ∫⁻ x in Kp i ∪ Km i, A x := add_le_add hc0 (lintegral_iUnion_le _ A)
    _ ≤ C + ∑' _i : Fin n, (C+C) := by
      apply add_le_add le_rfl
      apply ENNReal.tsum_le_tsum
      intro i
      exact (lintegral_union_le A _ _).trans (add_le_add (hcp i) (hcm i))
    _ = _ := by
      rw [tsum_fintype]
      simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
      push_cast
      ring

end GraphBallArea

def graphAreaBoxBound (n : ℕ) (R : ℝ) : ℝ≥0∞ :=
  (2*n+1 : ℕ) * ((volume (Metric.closedBall (0 : Space n) n))^(1/((n:ℝ)+2)) *
    (volume (Metric.closedBall (0 : Space n) (n*R)))^(1-1/((n:ℝ)+2)))

lemma graphAreaBoxBound_ne_top (n : ℕ) (R : ℝ) : graphAreaBoxBound n R ≠ ⊤ := by
  have hd : 0 ≤ 1/((n:ℝ)+2) := by positivity
  have hd1 : 0 ≤ 1-1/((n:ℝ)+2) := by
    have : 1/((n:ℝ)+2) < 1 := by
      rw [div_lt_one (by positivity)]
      have := Nat.cast_nonneg (α := ℝ) n
      linarith
    linarith
  exact ENNReal.mul_ne_top (ENNReal.natCast_ne_top _) (ENNReal.mul_ne_top
    (ENNReal.rpow_ne_top_of_nonneg hd measure_closedBall_lt_top.ne)
    (ENNReal.rpow_ne_top_of_nonneg hd1 measure_closedBall_lt_top.ne))

end AffineBernstein
end

end OAI
