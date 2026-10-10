import Mathlib
import OAI.Probability.SKRatio.Matrices.WeightedSquares
import OAI.Probability.SKRatio.Matrices.RowGeometry
import OAI.Probability.SKRatio.Gaussian.ExponentialProducts
import OAI.Probability.SKRatio.Gaussian.PlantedEntries
import OAI.Probability.SKRatio.Matrices.ConditionalAffineSquares

namespace OAI

section
noncomputable section
open scoped BigOperators NNReal ENNReal Topology
open MeasureTheory ProbabilityTheory Filter Set Real Metric
namespace SKRatio.Planted
open SKRatioClock.Regression MatrixNet
attribute [local instance] Classical.propDecidable

lemma incident_absolute_square_error {n : ℕ} (hn : 0<n) (β : ℝ)
    (z : Disorder n) {C : ℝ}
    (hrow : ∀ i, (∑ e∈incidentEdges i, z e^2)/(n:ℝ) ≤ C) (i : Fin n) :
    ∑ e : incidentEdges i, |affineDisorder β z e^2-β^2/(n:ℝ)| ≤
      2*β^2*C+2*β^4+β^2 := by
  have hnr : (0:ℝ)<n := Nat.cast_pos.mpr hn
  have hc : ((incidentEdges i).card:ℝ) ≤ n := by exact_mod_cast incidentEdges_card_le i
  have hs : ∑ e : incidentEdges i, affineDisorder β z e^2 ≤ 2*β^2*C+2*β^4 := by
    have h := affine_square_row_bound hn β z hrow i
    simp_rw [coupling_sq] at h
    rw [sum_coupling_row] at h
    simpa only [Finset.sum_subtype (incidentEdges i) (fun _ => Iff.rfl)] using h
  calc
    _ ≤ ∑ e : incidentEdges i, (affineDisorder β z e^2+β^2/(n:ℝ)) := by
      apply Finset.sum_le_sum
      intro e _
      exact (abs_sub _ _).trans (by rw [abs_of_nonneg (sq_nonneg _),abs_of_nonneg (by positivity)])
    _ = (∑ e : incidentEdges i, affineDisorder β z e^2)+
        ((incidentEdges i).card:ℝ)*(β^2/(n:ℝ)) := by simp [Finset.sum_add_distrib]
    _ ≤ (2*β^2*C+2*β^4)+β^2 := by
      apply add_le_add hs
      calc
        _ ≤ (n:ℝ)*(β^2/(n:ℝ)) := mul_le_mul_of_nonneg_right hc (by positivity)
        _ = _ := mul_div_cancel₀ _ hnr.ne'

lemma weighted_sum_difference_le {ι : Type*} [Fintype ι]
    (a f g : ι → ℝ) {δ R : ℝ} (hδ : 0≤δ)
    (ha : ∑ i, |a i| ≤ R) (hfg : ∀ i, |f i-g i|≤δ) :
    |(∑ i, a i*f i)-(∑ i, a i*g i)| ≤ δ*R := by
  rw [←Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ i, |a i*f i-a i*g i| := Finset.abs_sum_le_sum_abs _ _
    _ = ∑ i, |a i| * |f i-g i| := by simp only [←mul_sub,abs_mul]
    _ ≤ ∑ i, |a i| * δ := Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_left (hfg i) (abs_nonneg _))
    _ = δ*(∑ i, |a i|) := by rw [←Finset.sum_mul,mul_comm]
    _ ≤ _ := mul_le_mul_of_nonneg_left ha hδ

lemma compact_first_mesh {X : Type*} [PseudoMetricSpace X] [CompactSpace X]
    {δ : ℝ} (hδ : 0<δ) :
    ∃ (s : Finset X) (q : X → s), ∀ x : X, dist x (q x : X) < δ := by
  classical
  obtain ⟨s,_,hs,hcov⟩ := finite_cover_balls_of_compact (X := X) isCompact_univ hδ
  have hnear (x : X) : ∃ y : {z // z∈hs.toFinset}, dist x y<δ := by
    obtain ⟨y,hy,hxy⟩ := Set.mem_iUnion₂.mp (hcov (Set.mem_univ x))
    exact ⟨⟨y,hs.mem_toFinset.mpr hy⟩,hxy⟩
  choose q hq using hnear
  exact ⟨hs.toFinset,q,hq⟩

theorem continuous_weighted_diagonal_rare {X : Type} [PseudoMetricSpace X] [CompactSpace X]
    (G : X × X → ℝ) (hG : Continuous G) (b : ℝ → X) {K : ℝ≥0} (hb : LipschitzWith K b)
    (β : ℝ) (μ : ∀ n, Measure (Fin n → ℝ)) [∀ n, IsProbabilityMeasure (μ n)]
    {u : ℝ} (hu : 0<u) :
    ExponentiallyRare (fun n => (μ n).prod (standardArrayLaw (Edge n)))
      (fun n => {p | ∃ i : Fin n, ∃ a : X,
        u < |∑ e : incidentEdges i, (affineDisorder β p.2 e^2-β^2/(n:ℝ))*
          G (a,b (diagonalField p.1 (affineDisorder β p.2) (otherEnd i e)))|}) := by
  obtain ⟨C,hC,hrows⟩ := gaussian_rows_square_bounded
  let R := 2*β^2*C+2*β^4+β^2
  have hR : 0≤R := by dsimp [R]; positivity
  let v := u/(2*(R+1))
  have hv : 0<v := by dsimp [v]; positivity
  have hvR : v*R ≤ u/2 := by
    dsimp [v]
    rw [div_mul_eq_mul_div]
    apply (div_le_iff₀ (by positivity : 0<2*(R+1))).mpr
    nlinarith only [hu.le]
  obtain ⟨δ,hδ,hcont⟩ := Metric.uniformContinuous_iff.mp
    (CompactSpace.uniformContinuous_of_continuous hG) v hv
  obtain ⟨s,q,hq⟩ := compact_first_mesh (X := X) hδ
  obtain ⟨A,hA⟩ := isCompact_univ.exists_bound_of_continuousOn hG.continuousOn
  have hA0 : 0≤A := (abs_nonneg (G (b 0,b 0))).trans (by
    simpa only [Real.norm_eq_abs] using hA (b 0,b 0) (mem_univ _))
  have hAb (x y : X) : |G (x,y)|≤A := by
    simpa only [Real.norm_eq_abs] using hA (x,y) (mem_univ _)
  obtain ⟨c,hc,ht⟩ := weighted_affine_conditioned_tail β C hA0 (half_pos hu)
  let bad (a : s) (n : ℕ) : Set ((Fin n → ℝ) × Disorder n) :=
    ⋃ i : Fin n, {p | u/2 < |∑ e : incidentEdges i,
      G (a,b (diagonalField p.1 (outsideDisorder β i (fun j => p.2 j)) (otherEnd i e)))*
        ((β/sqrt n*p.2 e+β^2/(n:ℝ))^2-β^2/(n:ℝ))| ∧
      (∑ e : incidentEdges i, p.2 e^2)/(n:ℝ)≤C}
  have hbad (a : s) : ExponentiallyRare
      (fun n => (μ n).prod (standardArrayLaw (Edge n))) (bad a) := by
    apply exponentiallyRare_iUnion_polynomial _ _ hc (by norm_num : (0:ℝ)<3)
      (by norm_num : (0:ℝ)<1) 1
    · exact Eventually.of_forall (fun n => by simp)
    · filter_upwards [ht] with n hn i
      apply hn (μ n) (incidentEdges i)
        (fun ζ y e => G (a,b (diagonalField ζ (outsideDisorder β i y) (otherEnd i e))))
        (incidentEdges_card_le i)
      · intro e
        exact (hG.comp (continuous_const.prodMk (hb.continuous.comp
          (continuous_outside_field β i (otherEnd i e))))).measurable
      · intro ζ y e
        exact hAb _ _
  let d := δ/(2*((K:ℝ)+1))
  have hd : 0<d := by dsimp [d]; positivity
  have hKd : (K:ℝ)*d<δ := by
    dsimp [d]
    have hpos : (0:ℝ)<2*((K:ℝ)+1) := by positivity
    rw [←mul_div_assoc]
    apply (div_lt_iff₀ hpos).mpr
    nlinarith [K.coe_nonneg]
  apply (((hrows.prod_snd μ).union ((affine_max_entry_rare β hd).prod_snd μ)).union
    (ExponentiallyRare.iUnion_finite hbad)).mono
  filter_upwards [eventually_gt_atTop 0] with n hn p hp
  by_contra hfail
  have hr : ∀ i, (∑ e∈incidentEdges i, p.2 e^2)/(n:ℝ)≤C := by
    intro i
    exact le_of_not_gt (fun hi => hfail (Or.inl (Or.inl ⟨i,hi⟩)))
  have he : ∀ e, |affineDisorder β p.2 e|≤d := by
    intro e
    exact le_of_not_gt (fun hh => hfail (Or.inl (Or.inr ⟨e,hh⟩)))
  have hg : ∀ a : s, ∀ i : Fin n,
      |∑ e : incidentEdges i,
        (affineDisorder β p.2 e^2-β^2/(n:ℝ))*
          G (a,b (diagonalField p.1 (outsideDisorder β i (fun j => p.2 j)) (otherEnd i e)))|≤u/2 := by
    intro a i
    apply le_of_not_gt
    intro hh
    apply hfail
    right
    apply mem_iUnion.mpr
    refine ⟨a,mem_iUnion.mpr ⟨i,?_,?_⟩⟩
    · simpa only [affineDisorder,mul_comm] using hh
    · simpa only [Finset.sum_subtype (incidentEdges i) (fun _ => Iff.rfl)] using hr i
  obtain ⟨i,a,hi⟩ := hp
  have hsr : ∑ e : incidentEdges i, |affineDisorder β p.2 e^2-β^2/(n:ℝ)|≤R :=
    incident_absolute_square_error hn β p.2 hr i
  have hf (e : incidentEdges i) :
      |G (a,b (diagonalField p.1 (affineDisorder β p.2) (otherEnd i e)))-
        G (q a,b (diagonalField p.1 (outsideDisorder β i (fun j => p.2 j)) (otherEnd i e)))|≤v := by
    apply le_of_lt
    rw [←Real.dist_eq]
    apply hcont
    rw [Prod.dist_eq,max_lt_iff]
    refine ⟨hq a,?_⟩
    have hdist := hb.dist_le_mul
      (diagonalField p.1 (affineDisorder β p.2) (otherEnd i e))
      (diagonalField p.1 (outsideDisorder β i (fun j => p.2 j)) (otherEnd i e))
    rw [Real.dist_eq,outside_field_error] at hdist
    exact (hdist.trans (mul_le_mul_of_nonneg_left (he e) K.coe_nonneg)).trans_lt hKd
  have herr := weighted_sum_difference_le
    (fun e : incidentEdges i => affineDisorder β p.2 e^2-β^2/(n:ℝ))
    (fun e => G (a,b (diagonalField p.1 (affineDisorder β p.2) (otherEnd i e))))
    (fun e => G (q a,b (diagonalField p.1 (outsideDisorder β i (fun j => p.2 j)) (otherEnd i e))))
    hv.le hsr hf
  have htri := abs_sub_abs_le_abs_sub
    (∑ e : incidentEdges i, (affineDisorder β p.2 e^2-β^2/(n:ℝ))*
      G (a,b (diagonalField p.1 (affineDisorder β p.2) (otherEnd i e))))
    (∑ e : incidentEdges i, (affineDisorder β p.2 e^2-β^2/(n:ℝ))*
      G (q a,b (diagonalField p.1 (outsideDisorder β i (fun j => p.2 j)) (otherEnd i e))))
  have hgood := hg (q a) i
  linarith only [htri,herr,hgood,hvR,hi]

end SKRatio.Planted

end
end

end OAI
