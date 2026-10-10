import OAI.NumberTheory.Jacobsthal.Estimates.ReferenceSourceDecomposition

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

open _root_.Set _root_.Finset
namespace ErdosContinuousAnomaly
attribute [local instance] Classical.propDecidable
open NumberTheoryLean.FinitePathGeometry NumberTheoryLean.PrimeHistories
open NumberTheoryLean.PrimeBinMembership NumberTheoryLean.ActualPrimeHigh
open NumberTheoryLean.BoundaryAnomaly NumberTheoryLean.UniformBoundaryCorrection
open NumberTheoryLean.UniformExponentialOccupation NumberTheoryLean.ActualBoundaryDomain
open ErdosPrimeInputs.PrimePrefixMass

noncomputable def continuousBoundaryCorrection (w ell : ℝ) (start : Node) : ℝ :=
  ∑ ps ∈ uncappedPrefixes w ell start,prefixWeight ps*((-1:ℝ)^ps.length*
    continuousAnomaly (terminal w start ps).side (terminal w start ps).gap)

theorem boundaryCorrection_difference (w ell : ℝ) (start : Node) :
    boundaryCorrection w ell start-continuousBoundaryCorrection w ell start =
      ∑ ps ∈ uncappedPrefixes w ell start,prefixWeight ps*((-1:ℝ)^ps.length*
        (anomaly w (terminal w start ps).side (terminal w start ps).gap-
          continuousAnomaly (terminal w start ps).side (terminal w start ps).gap)) := by
  simp only [boundaryCorrection,continuousBoundaryCorrection,mul_sub,Finset.sum_sub_distrib]

theorem actual_anomaly_replacement (ell d eps : ℝ) (hell : 2 ≤ ell)
    (hd : 0 < d) (heps : 0 < eps) :
    ∃ B₀ w₀ : ℝ,0 < B₀ ∧ 1 < w₀ ∧ ∀ B w : ℝ,B₀ ≤ B → w₀ ≤ w →
      Real.log B ≤ d*Real.log w → ∀ start : Node,
        start.side=.even → 199/100 ≤ start.ratio → start.ratio ≤ 23/10 →
        Consistent start → start.cutoff=B →
        B^2*|boundaryCorrection w ell start-continuousBoundaryCorrection w ell start| ≤ eps := by
  obtain ⟨c,hc,hweighted⟩ := weighted_anomaly_convergence
  obtain ⟨C,BO,wO,hC,hBO,hwO,hoccupation⟩ :=
    uniform_signed_exponential_rewards ell c d (by linarith) hc hd
  obtain ⟨wA,hwA,hA⟩ := hweighted (eps/C) (div_pos heps hC)
  refine ⟨max BO 4,max wO wA,hBO.trans_le (le_max_left _ _),hwO.trans_le (le_max_left _ _),?_⟩
  intro B w hB hw hcomp start hi h199 h23 hcons hcut
  have hBO' : BO ≤ B := (le_max_left _ _).trans hB
  have hB4 : 4 ≤ B := (le_max_right _ _).trans hB
  have hwO' : wO ≤ w := (le_max_left _ _).trans hw
  have hwA' : wA ≤ w := (le_max_right _ _).trans hw
  rw [boundaryCorrection_difference]
  have hs := hoccupation B w hBO' hwO' hcomp start hi h199 h23 hcons hcut
    (eps/C) (div_pos heps hC).le
    (fun ps => (-1:ℝ)^ps.length*
      (anomaly w (terminal w start ps).side (terminal w start ps).gap-
        continuousAnomaly (terminal w start ps).side (terminal w start ps).gap))
  have hp : ∀ ps ∈ uncappedPrefixes w ell start,
      |(-1:ℝ)^ps.length*(anomaly w (terminal w start ps).side (terminal w start ps).gap-
        continuousAnomaly (terminal w start ps).side (terminal w start ps).gap)| ≤
          (eps/C)*positiveGapEnvelope c (terminal w start ps).gap := by
    intro ps hps
    have hallowed : uncappedAllowed w ell start ps := (Finset.mem_filter.mp hps).2
    have hdom := source_boundary_domain hB4 hell start hi h199 h23 hcons hcut hallowed
    have hr := boundary_gap_ge_two hdom
    rw [abs_mul,abs_pow,abs_neg,abs_one,one_pow,one_mul,positiveGapEnvelope,ite_eq_left hr]
    exact hA w hwA' _ hr _
  have hcanc : (eps/C)*C=eps := div_mul_cancel₀ eps (ne_of_gt hC)
  simpa only [hcanc] using hs hp

end ErdosContinuousAnomaly

end

section

namespace ErdosContinuousAnomaly
open NumberTheoryLean.FinitePathGeometry NumberTheoryLean.PrimeHistories
open NumberTheoryLean.ActualPrimeHigh
open ErdosPrimeInputs.PrimePrefixMass

noncomputable def sideSign : Side → ℝ | .even => 1 | .odd => -1

theorem terminal_side_sign (w : ℝ) (z : Node) (ps : List ℕ) :
    sideSign (terminal w z ps).side=sideSign z.side*(-1:ℝ)^ps.length := by
  induction ps generalizing z with
  | nil => simp only [terminal_nil,List.length_nil,pow_zero,mul_one]
  | cons p ps ih =>
    rw [terminal_cons,ih,List.length_cons,pow_succ]
    have he : sideSign (step w z p).side = -sideSign z.side := by
      cases h : z.side <;> simp [step,h,Side.flip,sideSign]
    rw [he]
    ring

theorem source_parity_sign (w : ℝ) (z : Node) (hz : z.side=.even) (ps : List ℕ) :
    (-1:ℝ)^ps.length=sideSign (terminal w z ps).side := by
  rw [terminal_side_sign,hz,sideSign,one_mul]

noncomputable def signedAnomaly (i : Side) (r : ℝ) : ℝ := sideSign i*continuousAnomaly i r

theorem continuousBoundaryCorrection_eq_state_reward (w ell : ℝ) (start : Node)
    (hi : start.side=.even) :
    continuousBoundaryCorrection w ell start=
      ∑ ps ∈ uncappedPrefixes w ell start,prefixWeight ps*
        signedAnomaly (terminal w start ps).side (terminal w start ps).gap := by
  unfold continuousBoundaryCorrection signedAnomaly
  apply Finset.sum_congr rfl
  intro ps _
  rw [source_parity_sign w start hi ps]

end ErdosContinuousAnomaly

end

section

open _root_.Set
namespace ErdosCorrectionOccupation
open ErdosContinuousAnomaly
open NumberTheoryLean.FinitePathGeometry NumberTheoryLean.PositiveGapMajorant

noncomputable def extendedSignedAnomaly (i : Side) (r : ℝ) : ℝ :=
  sideSign i*continuousAnomaly i (max 2 r)

theorem extendedSignedAnomaly_continuous (i : Side) : Continuous (extendedSignedAnomaly i) := by
  have h := (continuousAnomaly_continuousOn i).comp_continuous
    (continuous_const.max continuous_id) (fun r => le_max_left 2 r)
  exact continuous_const.mul h

theorem extendedSignedAnomaly_eq (i : Side) {r : ℝ} (hr : 2 ≤ r) :
    extendedSignedAnomaly i r=signedAnomaly i r := by
  simp only [extendedSignedAnomaly,signedAnomaly,max_eq_right hr]

noncomputable def compactCutoff (K : ℝ) : C(ℝ×ℝ,ℝ) :=
  Classical.choose (exists_positive_gap_majorant K)

theorem compactCutoff_spec (K : ℝ) :
    HasCompactSupport (compactCutoff K) ∧ (∀ x,0 ≤ compactCutoff K x ∧ compactCutoff K x ≤ 1) ∧
    (∀ r s,2 ≤ r → r ≤ K → 0 ≤ s → s ≤ K → compactCutoff K (r,s)=1) ∧
    ∀ r s,r < 1 ∨ K+1 < r → compactCutoff K (r,s)=0 :=
  Classical.choose_spec (exists_positive_gap_majorant K)

noncomputable def compactAnomalyTest (K : ℝ) (i : Side) (x : ℝ×ℝ) : ℝ :=
  compactCutoff K x*extendedSignedAnomaly i x.1

theorem compactAnomalyTest_continuous (K : ℝ) (i : Side) : Continuous (compactAnomalyTest K i) :=
  (compactCutoff K).continuous.mul ((extendedSignedAnomaly_continuous i).comp continuous_fst)

theorem compactAnomalyTest_compact (K : ℝ) (i : Side) : HasCompactSupport (compactAnomalyTest K i) := by
  exact (compactCutoff_spec K).1.mul_right

theorem compactAnomalyTest_support (K : ℝ) (i : Side) (r s : ℝ)
    (hr : r < 1 ∨ K+1 < r) : compactAnomalyTest K i (r,s)=0 := by
  unfold compactAnomalyTest
  rw [(compactCutoff_spec K).2.2.2 r s hr,zero_mul]

theorem compactAnomalyTest_eq (K : ℝ) (i : Side) {r s : ℝ}
    (hr : 2 ≤ r) (hrK : r ≤ K) (hs : 0 ≤ s) (hsr : s ≤ r) :
    compactAnomalyTest K i (r,s)=signedAnomaly i r := by
  unfold compactAnomalyTest
  rw [(compactCutoff_spec K).2.2.1 r s hr hrK hs (hsr.trans hrK),one_mul,extendedSignedAnomaly_eq i hr]

theorem compactAnomalyTest_error (K : ℝ) (i : Side) {r s : ℝ}
    (hr : 2 ≤ r) (hs : 0 ≤ s) (hsr : s ≤ r) :
    |signedAnomaly i r-compactAnomalyTest K i (r,s)| ≤
      if K < r then |continuousAnomaly i r| else 0 := by
  by_cases hrK : r ≤ K
  · rw [compactAnomalyTest_eq K i hr hrK hs hsr,sub_self,abs_zero,ite_eq_right (not_lt_of_ge hrK)]
  · rw [ite_eq_left (lt_of_not_ge hrK)]
    have hb := (compactCutoff_spec K).2.1 (r,s)
    have he : signedAnomaly i r-compactAnomalyTest K i (r,s)=
        (1-compactCutoff K (r,s))*(sideSign i*continuousAnomaly i r) := by
      simp only [compactAnomalyTest,extendedSignedAnomaly_eq i hr,signedAnomaly]
      ring
    rw [he,abs_mul,abs_of_nonneg (by linarith : 0 ≤ 1-compactCutoff K (r,s)),abs_mul]
    have hsign : |sideSign i|=1 := by cases i <;> norm_num [sideSign]
    rw [hsign,one_mul]
    exact mul_le_of_le_one_left (abs_nonneg _) (by linarith)

end ErdosCorrectionOccupation

end

end Erdos970

end OAI
