import Mathlib
import OAI.Probability.GaussianInformation.Inverse.Model

namespace OAI
open MeasureTheory Metric
open scoped ENNReal
namespace AllScaleInverseVolume
open Set
open scoped Topology NNReal
noncomputable def diagonalMap {q : ℕ} (c : Fin q → ℝ) : Ambient q →ₗ[ℝ] Ambient q :=
  Matrix.toEuclideanLin (Matrix.diagonal c)

lemma diagonalMap_apply {q : ℕ} (c : Fin q → ℝ) (x : Ambient q) (j : Fin q) :
    diagonalMap c x j = c j*x j := by
  simp [diagonalMap,Matrix.toEuclideanLin,Matrix.toLpLin_apply,Matrix.mulVec_diagonal]

lemma diagonalMap_det {q : ℕ} (c : Fin q → ℝ) : LinearMap.det (diagonalMap c) = ∏ j,c j := by
  rw [diagonalMap,Matrix.toEuclideanLin_eq_toLin_orthonormal,LinearMap.det_toLin,Matrix.det_diagonal]

lemma diagonalMap_contraction {q : ℕ} (c : Fin q → ℝ) (hc : ∀ j,0 ≤ c j ∧ c j ≤ 1) (x : Ambient q) :
    ‖diagonalMap c x‖ ≤ ‖x‖ := by
  have hs : ‖diagonalMap c x‖^2 ≤ ‖x‖^2 := by
    simp only [EuclideanSpace.real_norm_sq_eq]
    apply Finset.sum_le_sum
    intro j _
    change (diagonalMap c x j)^2 ≤ (x j)^2
    rw [diagonalMap_apply,mul_pow]
    have hh : (c j)^2 ≤ 1 := by nlinarith [(hc j).1,(hc j).2]
    exact (mul_le_mul_of_nonneg_right hh (sq_nonneg _)).trans_eq (one_mul _)
  nlinarith [norm_nonneg (diagonalMap c x),norm_nonneg x]

lemma card_ellipsoid_separated {q : ℕ} (c : Fin q → ℝ) (hc : ∀ j,0 < c j ∧ c j ≤ 1)
    (s : Finset (Ambient q)) (hs : ∀ x ∈ s,‖diagonalMap c x‖ ≤ 2)
    (hsep : ∀ x ∈ s,∀ y ∈ s,x ≠ y → 1 ≤ ‖x-y‖) :
    (s.card:ℝ) ≤ 5^q * (∏ j,c j)⁻¹ := by
  let A := ⋃ x ∈ s,ball x (1/2)
  have hp : 0 < ∏ j,c j := Finset.prod_pos (fun j _ => (hc j).1)
  have hd : LinearMap.det (diagonalMap c) ≠ 0 := by rw [diagonalMap_det]; exact ne_of_gt hp
  have hdisj : (s:Set (Ambient q)).PairwiseDisjoint (fun x => ball x (1/2)) := by
    intro x hx y hy hxy
    apply ball_disjoint_ball
    rw [dist_eq_norm]
    convert hsep x hx y hy hxy using 1
    norm_num
  have hsub : A ⊆ diagonalMap c ⁻¹' ball 0 (5/2) := by
    intro y hy
    obtain ⟨x,hx,hy⟩ := mem_iUnion₂.mp hy
    have he : ‖diagonalMap c (y-x)‖ < 1/2 :=
      (diagonalMap_contraction c (fun j => ⟨(hc j).1.le,(hc j).2⟩) (y-x)).trans_lt hy
    change ‖diagonalMap c y-0‖ < 5/2
    rw [sub_zero]
    have hi := norm_add_le (diagonalMap c (y-x)) (diagonalMap c x)
    rw [← map_add,sub_add_cancel] at hi
    linarith [hs x hx]
  have hb : (s.card:ℝ≥0∞)*ENNReal.ofReal ((1/2:ℝ)^q)*volume (ball (0:Ambient q) 1) ≤
      ENNReal.ofReal ((∏ j,c j)⁻¹)*ENNReal.ofReal ((5/2:ℝ)^q)*volume (ball (0:Ambient q) 1) := by
    calc
      _ = volume A := by
        rw [measure_biUnion_finset hdisj (fun _ _ => measurableSet_ball)]
        simp only [volume.addHaar_ball_of_pos _ (by norm_num : (0:ℝ)<1/2),finrank_euclideanSpace,
          Fintype.card_fin,Finset.sum_const,nsmul_eq_mul,mul_assoc]
      _ ≤ volume (diagonalMap c ⁻¹' ball 0 (5/2)) := measure_mono hsub
      _ = _ := by
        rw [Measure.addHaar_preimage_linearMap volume hd,diagonalMap_det,abs_of_pos (inv_pos.mpr hp),
          volume.addHaar_ball_of_pos _ (by norm_num : (0:ℝ)<5/2)]
        simp [mul_assoc]
  have hb' := (ENNReal.mul_le_mul_iff_left (measure_ball_pos volume (0:Ambient q) zero_lt_one).ne'
    measure_ball_lt_top.ne).mp hb
  rw [← ENNReal.ofReal_mul (le_of_lt (inv_pos.mpr hp))] at hb'
  have hr : (s.card:ℝ)*(1/2:ℝ)^q ≤ (∏ j,c j)⁻¹*(5/2:ℝ)^q := by
    simpa [ENNReal.toReal_mul,ENNReal.toReal_ofReal (by positivity : 0 ≤ (1/2:ℝ)^q)] using
      ENNReal.toReal_le_of_le_ofReal (by positivity) hb'
  have he : (5/2:ℝ)^q = 5^q*(1/2:ℝ)^q := by rw [← mul_pow]; congr 1; norm_num
  rw [he,← mul_assoc,mul_comm (∏ j,c j)⁻¹] at hr
  exact (mul_le_mul_iff_left₀ (pow_pos (by norm_num : (0:ℝ)<1/2) q)).mp hr

lemma exists_ellipsoid_cover {q : ℕ} (c : Fin q → ℝ) (hc : ∀ j,0 < c j ∧ c j ≤ 1) :
    ∃ s : Finset (Ambient q),
      (∀ x ∈ s,‖diagonalMap c x‖ ≤ 2) ∧
      (∀ x : Ambient q,‖diagonalMap c x‖ ≤ 2 → ∃ y ∈ s,dist x y ≤ 1) ∧
      (s.card:ℝ) ≤ 5^q*(∏ j,c j)⁻¹ := by
  classical
  let A := diagonalMap c ⁻¹' closedBall 0 2
  have hd : LinearMap.det (diagonalMap c) ≠ 0 := by
    rw [diagonalMap_det]
    exact ne_of_gt (Finset.prod_pos (fun j _ => (hc j).1))
  let e : Ambient q ≃ₗ[ℝ] Ambient q :=
    LinearMap.equivOfIsUnitDet (f := diagonalMap c) (isUnit_iff_ne_zero.mpr hd)
  have he : DFunLike.coe e = DFunLike.coe (diagonalMap c) := by
    funext x
    exact LinearMap.equivOfIsUnitDet_apply (f := diagonalMap c) (isUnit_iff_ne_zero.mpr hd) x
  have hA : IsCompact A := by
    change IsCompact (diagonalMap c ⁻¹' closedBall 0 2)
    rw [← he]
    exact e.toContinuousLinearEquiv.toHomeomorph.isCompact_preimage.mpr (isCompact_closedBall _ _)
  let ε : ℝ≥0 := 1
  obtain ⟨N,_,hNfin,hNcov⟩ := Metric.exists_finite_isCover_of_isCompact
    (s := A) (ε := ε/2) (by norm_num [ε]) hA
  have hp : Metric.packingNumber ε A < ⊤ := by
    calc
      _ = Metric.packingNumber (2*(ε/2)) A := by congr 1; ring
      _ ≤ Metric.externalCoveringNumber (ε/2) A := Metric.packingNumber_two_mul_le_externalCoveringNumber _ _
      _ ≤ N.encard := hNcov.externalCoveringNumber_le_encard
      _ < ⊤ := hNfin.encard_lt_top
  let S := Metric.maximalSeparatedSet ε A
  have hSfin : S.Finite := Set.encard_lt_top_iff.mp (by
    change (Metric.maximalSeparatedSet ε A).encard < ⊤
    rw [Metric.encard_maximalSeparatedSet hp.ne]
    exact hp)
  have hs : ∀ x ∈ hSfin.toFinset,‖diagonalMap c x‖ ≤ 2 := by
    intro x hx
    have hm : x ∈ S := by simpa using hx
    simpa [A] using Metric.maximalSeparatedSet_subset hm
  refine ⟨hSfin.toFinset,hs,?_,card_ellipsoid_separated c hc _ hs ?_⟩
  · intro x hx
    have hm : x ∈ A := by simpa [A] using hx
    obtain ⟨y,hy,hxy⟩ := mem_iUnion₂.mp (Metric.isCover_iff_subset_iUnion_closedBall.mp
      (Metric.isCover_maximalSeparatedSet hp.ne) hm)
    exact ⟨y,by simpa using hy,by simpa [ε] using hxy⟩
  · intro x hx y hy hxy
    have hs := Metric.isSeparated_maximalSeparatedSet (ε := ε) (A := A)
      (by simpa using hx) (by simpa using hy) hxy
    have ht := ENNReal.toReal_mono (edist_ne_top x y) hs.le
    simpa [ε,edist_dist,dist_eq_norm] using ht

lemma weighted_group_bound {q : ℕ} (g : Fin q → ℕ) (x : Ambient q)
    (hx : ∀ h : ℕ,∑ j ∈ Finset.univ.filter (fun j => g j = h),(x j)^2 ≤ (4:ℝ)^h) :
    ‖diagonalMap (fun j => (1/4:ℝ)^(g j)) x‖ ≤ 2 := by
  classical
  let T := Finset.univ.image g
  have hsum : ∑ j : Fin q,((1/4:ℝ)^(g j)*(x j))^2 ≤ 4/3 := by
    calc
      _ = ∑ h ∈ T,∑ j ∈ Finset.univ.filter (fun j => g j = h),
          ((1/4:ℝ)^(g j)*(x j))^2 :=
        (Finset.sum_fiberwise_of_maps_to (fun j _ => Finset.mem_image.mpr ⟨j,Finset.mem_univ _,rfl⟩) _).symm
      _ ≤ ∑ h ∈ T,(1/4:ℝ)^h := by
        apply Finset.sum_le_sum
        intro h hh
        calc
          _ = ((1/4:ℝ)^h)^2 * ∑ j ∈ Finset.univ.filter (fun j => g j = h),(x j)^2 := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro j hj
            rw [(Finset.mem_filter.mp hj).2,mul_pow]
          _ ≤ ((1/4:ℝ)^h)^2 * (4:ℝ)^h := mul_le_mul_of_nonneg_left (hx h) (sq_nonneg _)
          _ = (1/4:ℝ)^h := by
            rw [sq,mul_assoc,← mul_pow]
            norm_num
      _ ≤ ∑' h : ℕ,(1/4:ℝ)^h :=
        (summable_geometric_of_lt_one (by norm_num : (0:ℝ) ≤ 1/4) (by norm_num)).sum_le_tsum
          T (fun _ _ => by positivity)
      _ = 4/3 := by rw [tsum_geometric_of_norm_lt_one (by norm_num : ‖(1/4:ℝ)‖<1)]; norm_num
  have hn : ‖diagonalMap (fun j => (1/4:ℝ)^(g j)) x‖^2 ≤ 4/3 := by
    simpa only [EuclideanSpace.real_norm_sq_eq,diagonalMap_apply] using hsum
  nlinarith [norm_nonneg (diagonalMap (fun j => (1/4:ℝ)^(g j)) x)]

end AllScaleInverseVolume

end OAI
