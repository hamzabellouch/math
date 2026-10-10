import Mathlib
import OAI.Analysis.VlasovMaxwell.Population.SelectedReceiverWeightBoundFinite

namespace OAI

noncomputable section

open MeasureTheory Set
open Filter Set
open scoped Topology
open scoped Topology Pointwise
open Set MeasureTheory Metric ODE
open scoped Topology NNReal
open scoped ContDiff
open Set MeasureTheory Metric
open Set MeasureTheory Metric Filter ODE
open Set MeasureTheory Filter Metric ODE
open Set MeasureTheory Filter Metric
open scoped Topology NNReal ContDiff
open Set MeasureTheory Filter
open scoped Topology ContDiff RealInnerProductSpace NNReal
open Set Filter MeasureTheory Metric
open scoped Topology ContDiff NNReal RealInnerProductSpace
open scoped Topology ContDiff NNReal ENNReal
open Set MeasureTheory
open scoped ENNReal
open Set Filter MeasureTheory
open scoped Topology ContDiff RealInnerProductSpace
open scoped Topology ContDiff ENNReal
open scoped Topology ContDiff NNReal
open scoped Topology ContDiff
open Set
open Set Filter Metric MeasureTheory
open scoped ENNReal Topology ContDiff

namespace RVM

def relativeAngleCoordinate (v w : Vec) : ℝ :=
  Real.sqrt ((1-dot (velocity w) (velocity v))/2)

lemma relative_deficit_pos (v w : Vec) : 0<1-dot (velocity w) (velocity v) := by
  have hd := dot_le_norm (velocity w) (velocity v)
  have hm := mul_le_mul_of_nonneg_right (norm_velocity_lt_one w).le (norm_nonneg (velocity v))
  rw [one_mul] at hm
  linarith [norm_velocity_lt_one v]

lemma relativeAngleCoordinate_pos (v w : Vec) : 0<relativeAngleCoordinate v w := by
  exact Real.sqrt_pos.mpr (div_pos (relative_deficit_pos v w) (by norm_num))

lemma relativeAngleCoordinate_le_one (v w : Vec) : relativeAngleCoordinate v w≤1 := by
  apply (Real.sqrt_le_iff).mpr
  constructor
  · norm_num
  · linarith [(velocity_deficit_mem_unit2 v w).2]

lemma relativeAngleCoordinate_lower (v w : Vec) : 1/2≤q v*relativeAngleCoordinate v w := by
  have hq := q_pos v
  have hv := norm_velocity_lt_one v
  have hdot : dot (velocity w) (velocity v)≤‖velocity v‖ := by
    calc
      _ ≤ ‖velocity w‖*‖velocity v‖ := dot_le_norm _ _
      _ ≤ 1*‖velocity v‖ := mul_le_mul_of_nonneg_right (norm_velocity_lt_one w).le (norm_nonneg _)
      _ = _ := one_mul _
  have hs := velocity_self v
  rw [dot_self] at hs
  have hinv : (q v)^2*((q v)⁻¹)^2=1 := by field_simp
  have hd : ((q v)⁻¹)^2≤2*(1-dot (velocity w) (velocity v)) := by
    nlinarith [sq_nonneg (1-‖velocity v‖)]
  have hdq := mul_le_mul_of_nonneg_left hd (sq_nonneg (q v))
  rw [hinv] at hdq
  have hroot := Real.sq_sqrt (div_nonneg (relative_deficit_pos v w).le (by norm_num : (0:ℝ)≤2))
  have hp : 0≤q v*relativeAngleCoordinate v w := mul_nonneg hq.le (relativeAngleCoordinate_pos _ _).le
  have hsq : 1≤4*(q v*relativeAngleCoordinate v w)^2 := by
    dsimp [relativeAngleCoordinate]
    nlinarith [sq_nonneg (q v)]
  nlinarith

lemma relative_angle_index_lt {j N : ℕ} {v w : Vec}
    (h : DyadicBand j (relativeAngleCoordinate v w)) (hP : 1024*q v≤(2:ℝ)^N) : j<N := by
  by_contra hc
  have hn : N≤j := Nat.le_of_not_gt hc
  have hpow : (2:ℝ)^N≤(2:ℝ)^j := pow_le_pow_right₀ (by norm_num) hn
  have hm := mul_le_mul_of_nonneg_right (hP.trans hpow) (relativeAngleCoordinate_pos v w).le
  have hl := relativeAngleCoordinate_lower v w
  nlinarith [h.2]

def relativePhysicalFactor (T r : ℝ) (n v w : Vec) (k : Fin 4→ℕ) (j : ℕ) : ℝ :=
  dyadicMultiFactor k (physicalCutoffCoordinates T r n v w)*
    dyadicFactor j (relativeAngleCoordinate v w)

lemma relativePhysicalFactor_nonneg (T r : ℝ) (n v w : Vec) (k : Fin 4→ℕ) (j : ℕ) :
    0≤relativePhysicalFactor T r n v w k j :=
  mul_nonneg (dyadicMultiFactor_nonneg _ _) (dyadicFactor_nonneg _ _)

lemma relativePhysicalFactor_partition (T r : ℝ) (n v w : Vec) (k : Fin 4→ℕ) :
    (∑'j : ℕ,relativePhysicalFactor T r n v w k j)=
      dyadicMultiFactor k (physicalCutoffCoordinates T r n v w) := by
  unfold relativePhysicalFactor
  rw [tsum_mul_left,tsum_dyadicFactor (relativeAngleCoordinate_pos v w)
    (relativeAngleCoordinate_le_one v w),mul_one]

def relativeRepresentativeClosedBin (T w : ℝ) (k : Fin 4→ℕ) (j : ℕ) : ClosedConeBin :=
  {representativeClosedBin T w k with
    emin := cappedRepresentative j^2/2
    emax := 8*cappedRepresentative j^2}

lemma relativePhysicalFactor_positive_closedBin {T w t σ : ℝ} {V : ℝ→Vec}
    {J : Set ℝ} (ht : t∈J) (hσ : σ∈Icc 0 t) (hband : q (V t)∈Icc (w/8) (8*w))
    {k : Fin 4→ℕ} {j : ℕ} {n : Sphere} {v : Vec}
    (hk : 0<relativePhysicalFactor T (t-σ) n.1 v (V t) k j) :
    (t,σ,n)∈physicalBinBase V (relativeRepresentativeClosedBin T w k j) J ∧
      v∈coneBinMomentumSet (relativeRepresentativeClosedBin T w k j) n.1 (velocity (V t)) := by
  have h1 : 0<dyadicMultiFactor k (physicalCutoffCoordinates T (t-σ) n.1 v (V t)) :=
    pos_of_mul_pos_left hk (dyadicFactor_nonneg _ _)
  have h2 : 0<dyadicFactor j (relativeAngleCoordinate v (V t)) :=
    pos_of_mul_pos_right hk (dyadicMultiFactor_nonneg _ _)
  have hmem := physicalCutoff_positive_closedBin ht hσ hband h1
  have hrelative := dyadicBand_angular_range (relative_deficit_pos v (V t)).le
    (dyadicFactor_tsupport (subset_tsupport _ (ne_of_gt h2)))
  exact ⟨hmem.1,hmem.2.1,hmem.2.2.1,hrelative⟩

lemma relativePhysicalFactor_positive_indices {T r : ℝ} {v w n : Vec}
    {k : Fin 4→ℕ} {j N : ℕ} (hn : ‖n‖=1) (hP : 1024*q v≤(2:ℝ)^N)
    (hk : 0<relativePhysicalFactor T r n v w k j) : k 0<N ∧ k 1<N ∧ j<N := by
  have h1 : 0<dyadicMultiFactor k (physicalCutoffCoordinates T r n v w) :=
    pos_of_mul_pos_left hk (dyadicFactor_nonneg _ _)
  have h2 : 0<dyadicFactor j (relativeAngleCoordinate v w) :=
    pos_of_mul_pos_right hk (dyadicMultiFactor_nonneg _ _)
  have hbase := physicalCutoff_positive_source_indices hn hP h1
  exact ⟨hbase.1,hbase.2,relative_angle_index_lt
    (dyadicFactor_tsupport (subset_tsupport _ (ne_of_gt h2))) hP⟩

lemma exists_relative_dyadic_positive (v w : Vec) :
    ∃j : ℕ,0<dyadicFactor j (relativeAngleCoordinate v w) := by
  by_contra hn
  push Not at hn
  have hz (j : ℕ) : dyadicFactor j (relativeAngleCoordinate v w)=0 :=
    le_antisymm (hn j) (dyadicFactor_nonneg _ _)
  have hh := tsum_dyadicFactor (relativeAngleCoordinate_pos v w) (relativeAngleCoordinate_le_one v w)
  simp_rw [hz] at hh
  norm_num at hh

def relativeBinRefinement (B : ClosedConeBin) (j : ℕ) : ClosedConeBin :=
  {B with emin := cappedRepresentative j^2/2,emax := 8*cappedRepresentative j^2}

lemma relativeBinRefinement_base (V : ℝ→Vec) (B : ClosedConeBin) (J : Set ℝ) (j : ℕ) :
    physicalBinBase V (relativeBinRefinement B j) J=physicalBinBase V B J := rfl

lemma relativeBinRefinement_measure (V : ℝ→Vec) (B : ClosedConeBin) (J : Set ℝ) (j : ℕ) :
    physicalBinMeasure V (relativeBinRefinement B j) J=physicalBinMeasure V B J := rfl

lemma coneBinMomentumSet_relative_cover (B : ClosedConeBin) (n w : Vec) {N : ℕ}
    (hN : 1024*B.qmax≤(2:ℝ)^N) {v : Vec}
    (hv : v∈coneBinMomentumSet B n (velocity w)) :
    ∃j∈Finset.range N,v∈coneBinMomentumSet (relativeBinRefinement B j) n (velocity w) := by
  obtain ⟨j,hj⟩ := exists_relative_dyadic_positive v w
  have hband := dyadicFactor_tsupport (subset_tsupport _ (ne_of_gt hj))
  have hq : 1024*q v≤(2:ℝ)^N := (mul_le_mul_of_nonneg_left hv.1.2 (by norm_num)).trans hN
  refine ⟨j,Finset.mem_range.mpr (relative_angle_index_lt hband hq),hv.1,hv.2.1,?_⟩
  exact dyadicBand_angular_range (relative_deficit_pos v w).le hband

lemma lintegral_coneBin_relative_cover (B : ClosedConeBin) (n w : Vec) {N : ℕ}
    (hN : 1024*B.qmax≤(2:ℝ)^N) {g : Vec→ℝ≥0∞} (hg : Measurable g) :
    (∫⁻v in coneBinMomentumSet B n (velocity w),g v)≤
      ∑j∈Finset.range N,∫⁻v in coneBinMomentumSet (relativeBinRefinement B j) n (velocity w),g v := by
  classical
  rw [←lintegral_indicator (measurableSet_coneBinMomentumSet B n (velocity w))]
  have hpoint (v : Vec) : (coneBinMomentumSet B n (velocity w)).indicator g v ≤
      ∑j∈Finset.range N,(coneBinMomentumSet (relativeBinRefinement B j) n (velocity w)).indicator g v := by
    by_cases hv : v∈coneBinMomentumSet B n (velocity w)
    · obtain ⟨j,hj,hv'⟩ := coneBinMomentumSet_relative_cover B n w hN hv
      rw [indicator_of_mem hv]
      calc
        _ = (coneBinMomentumSet (relativeBinRefinement B j) n (velocity w)).indicator g v :=
          (indicator_of_mem hv' g).symm
        _ ≤ _ := Finset.single_le_sum (f:=fun k : ℕ=>
          (coneBinMomentumSet (relativeBinRefinement B k) n (velocity w)).indicator g v) (fun _ _=>bot_le) hj
    · rw [indicator_of_notMem hv]
      exact bot_le
  calc
    _ ≤ ∫⁻v : Vec,∑j∈Finset.range N,
        (coneBinMomentumSet (relativeBinRefinement B j) n (velocity w)).indicator g v :=
      lintegral_mono hpoint
    _ = ∑j∈Finset.range N,∫⁻v : Vec,
        (coneBinMomentumSet (relativeBinRefinement B j) n (velocity w)).indicator g v := by
      exact lintegral_finsetSum _ (fun j _=>
        (hg.indicator (measurableSet_coneBinMomentumSet _ _ _)))
    _ = _ := by
      apply Finset.sum_congr rfl
      intro j _
      exact lintegral_indicator (measurableSet_coneBinMomentumSet _ _ _) _

end RVM

end

end OAI
