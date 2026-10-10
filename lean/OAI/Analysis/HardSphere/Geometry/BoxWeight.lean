import Mathlib
import OAI.Analysis.HardSphere.Geometry.LargeParentMarked
import OAI.Analysis.HardSphere.Geometry.TorusNear

namespace OAI

noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology BigOperators
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical ENNReal
namespace HardSphere.BathSlice
open HardSphere.Lattice

def boxWeight (m : ℕ) : ℝ≥0∞ := ENNReal.ofReal ((2*((m:ℝ)+1))^3)

lemma volume_largeBoxUnion_le {K : ℕ} [NeZero K] (L : Length) (B : Finset (DiscreteTorus K)) :
    (volume : Measure (Torus L)) (largeBoxUnion L B) ≤ animalCost (torusRangeGraph K 1) B boxWeight := by
  classical
  unfold largeBoxUnion animalCost
  apply (measure_iUnion_le _).trans
  apply ENNReal.tsum_le_tsum
  intro m
  apply (measure_iUnion_le _).trans
  rw [tsum_fintype]
  apply Finset.sum_le_sum
  intro v _
  apply (measure_biUnion_finset_le _ _).trans
  apply Finset.sum_le_sum
  intro A _
  by_cases hA : A⊆B
  · simp only [hA,Set.iUnion_true,ite_true]
    simpa only [boxWeight,Nat.cast_add,Nat.cast_one,add_assoc,one_add_one_eq_two] using
      volume_rootBox_le L (siteRep v) (by positivity : (0:ℝ)≤(m:ℝ)+2)
  · simp only [hA,Set.iUnion_of_empty,measure_empty,ite_false,le_refl]

attribute [local irreducible] torusDistance

lemma pairCloseLabels_measurable {m : ℕ} (L : Length) (s : ℝ) (v : Torus L) :
    Measurable (fun Y : Configuration m L ↦ ((pairCloseLabels L s v Y).card:ℝ)) := by
  classical
  simp only [pairCloseLabels,Finset.card_filter,Nat.cast_sum,Nat.cast_ite,Nat.cast_one,Nat.cast_zero]
  apply Finset.measurable_sum
  intro i _
  have hd : Continuous (fun Y : Configuration m L ↦ torusDistance L (Y i) v) :=
    (continuous_torusDistance L).comp
      ((continuous_apply i).prodMk (continuous_const : Continuous (fun _ : Configuration m L ↦ v)))
  have hp : MeasurableSet {Y : Configuration m L | ∃ j, j≠i ∧ torusDistance L (Y i) (Y j)≤ s} := by
    simp only [Set.ofPred_exists]
    apply MeasurableSet.iUnion
    intro j
    have hc : Continuous (fun Y : Configuration m L ↦ torusDistance L (Y i) (Y j)) :=
      (continuous_torusDistance L).comp ((show Continuous (fun Y : Configuration m L ↦ Y i) from continuous_apply i).prodMk
        (show Continuous (fun Y : Configuration m L ↦ Y j) from continuous_apply j))
    by_cases hji : j≠i
    · convert measurableSet_le hc.measurable (show Measurable (fun _ : Configuration m L ↦ s) from measurable_const) using 1
      ext Y
      exact and_iff_right hji
    · convert (MeasurableSet.empty : MeasurableSet (∅ : Set (Configuration m L))) using 1
      ext Y
      exact iff_false_intro (fun h ↦ hji h.1)
  exact Measurable.ite ((measurableSet_le hd.measurable measurable_const).inter hp)
    measurable_const measurable_const

lemma measurable_closeSet {n K : ℕ} [NeZero K] (L : Length) (s T : ℝ) :
    Measurable (closeSet (n := n) (K := K) L s T) := by
  classical
  apply measurable_finset_iff.mpr
  intro v
  simp only [closeSet,Finset.mem_filter,Finset.mem_univ,true_and]
  apply measurableSet_setOfPred.mp
  exact measurableSet_le measurable_const (pairCloseLabels_measurable L s (siteCenter L v))

lemma volume_torus (L : Length) : (volume : Measure (Torus L)) Set.univ = ENNReal.ofReal (L.val^3) := by
  rw [volume_pi,Measure.pi_univ]
  simp only [AddCircle.measure_univ,Finset.prod_const,Finset.card_univ,Fintype.card_fin,
    ENNReal.ofReal_pow L.property.le]

lemma microperiod_length {K : ℕ} {L : Length} {r : ℝ} (hr : 0 < r)
    (hLK : L.val=(K:ℝ)) : L.val = microMesh r * ((microPeriod r*K : ℕ):ℝ) := by
  have hq : (microPeriod r : ℝ) ≠ 0 := by exact_mod_cast (microPeriod_pos hr).ne'
  rw [hLK,microMesh,Nat.cast_mul]
  field_simp

theorem omitted_volume_le {n K M : ℕ} [NeZero K] {L : Length} {r s T : ℝ}
    (hr : 0 < r) (hrsmall : r ≤ 1/4096) (hL : 10 < L.val) (hLK : L.val=(K:ℝ))
    (hMK : M ≤ K) (hrs : 6*r ≤ s) (hT : T ≤ 1/(1372*r))
    (Y : Configuration n L) (hY : Y ∈ allowed n L r) :
    (volume : Measure (Torus L)) (omitted (microMesh r) r Y) ≤
      ENNReal.ofReal (1029*r^2*n) +
      animalCost (torusRangeGraph K 1) (closeSet L s T Y) boxWeight +
      (if LargeBadComponent (torusRangeGraph K 1) (closeSet L s T Y) M then
        ENNReal.ofReal (L.val^3) else 0) := by
  classical
  have hmesh := microMesh_bounds hr (by linarith : r ≤ 1)
  have hmark : LargeParentMarked (microPeriod r) (microMesh r) r Y (closeSet (K := K) L s T Y) := by
    simpa only [mul_one,Function.Embedding.refl_apply] using actual_large_parent_marked (K := K) (D := 1) (θ := T)
      hr hrsmall hL hLK hrs (by simpa using hT) (Function.Embedding.refl _) Y
  by_cases he : LargeBadComponent (torusRangeGraph K 1) (closeSet L s T Y) M
  · simp only [he,ite_true]
    calc
      _ ≤ (volume : Measure (Torus L)) Set.univ := measure_mono (Set.subset_univ _)
      _ = ENNReal.ofReal (L.val^3) := volume_torus L
      _ ≤ _ := le_add_self
  · simp only [he,ite_false,add_zero]
    have hK : 2 < K := by rw [hLK] at hL; exact_mod_cast (show (2:ℝ)<K by linarith)
    have hsub := omitted_subset_small_and_boxes (microPeriod_pos hr) hK hLK hMK Y hY
      (closeSet L s T Y) hmark he
    apply (measure_mono hsub).trans
    apply (measure_union_le _ _).trans
    apply add_le_add
    · apply (volume_smallFills_le hmesh.1 (hmesh.2.1.trans (by linarith))
        (microperiod_length hr hLK) hmesh.2.2 Y).trans
      apply ENNReal.ofReal_le_ofReal
      have hsq : (microMesh r)^2 ≤ r^2 := sq_le_sq₀ hmesh.1.le hr.le |>.mpr hmesh.2.1
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hsq (by norm_num)) (Nat.cast_nonneg n)
    · exact volume_largeBoxUnion_le L _

theorem omitted_mean_marginal {m n : ℕ} (L : Length) (h r : ℝ)
    (e : Fin m ↪ Fin n) (μ : Measure (Configuration n L)) :
    (∫⁻ Y, (volume : Measure (Torus L)) (omitted h r Y)
        ∂(μ.map (fun X i ↦ X (e i)))) =
      ∫⁻ X, (volume : Measure (Torus L)) (omitted h r (fun i ↦ X (e i))) ∂μ := by
  exact lintegral_map (measurable_omitted_volume L h r)
    (Measurable.of_eval (fun i ↦ measurable_pi_apply (e i)))

end HardSphere.BathSlice

namespace HardSphere.BathSlice
open HardSphere.Lattice

lemma boxWeight_le (m : ℕ) : boxWeight (m+1) ≤ 64*(8:ℝ≥0∞)^m := by
  have hnat : m+2 ≤ 2^(m+1) := by have := (Nat.lt_two_pow_self (n := m+1)); omega
  have hbound : 8*(m+2)^3 ≤ 64*8^m := by
    calc
      _ ≤ 8*(2^(m+1))^3 := by gcongr
      _ = 64*8^m := by rw [←pow_mul,Nat.mul_comm (m+1) 3,pow_mul]; norm_num; rw [pow_succ]; ring
  have heq : boxWeight (m+1) = ((8*(m+2)^3:ℕ):ℝ≥0∞) := by
    unfold boxWeight
    norm_cast
    ring
  rw [heq]
  exact_mod_cast hbound

lemma box_series_le {q : ℝ≥0∞} (hq : 8*q ≤ (2:ℝ≥0∞)⁻¹) :
    (∑' m : ℕ, boxWeight (m+1)*q^(m+1)) ≤ 128*q := by
  calc
    _ ≤ ∑' m : ℕ, (64*q)*((2:ℝ≥0∞)⁻¹)^m := by
      apply ENNReal.tsum_le_tsum
      intro m
      calc
        _ ≤ (64*8^m)*q^(m+1) := mul_le_mul' (boxWeight_le m) le_rfl
        _ = (64*q)*(8*q)^m := by rw [mul_pow,pow_succ]; ring
        _ ≤ _ := mul_le_mul' le_rfl (pow_le_pow_left' hq m)
    _ = (64*q)*2 := by rw [ENNReal.tsum_mul_left,ENNReal.tsum_geometric_two]
    _ = _ := by ring

theorem omitted_mean_le {n K M : ℕ} [NeZero K] {L : Length} {r s T : ℝ}
    (hr : 0 < r) (hrsmall : r ≤ 1/4096) (hL : 10 < L.val) (hLK : L.val=(K:ℝ))
    (hMK : M ≤ K) (hM : 1 ≤ M) (hrs : 6*r ≤ s) (hT : T ≤ 1/(1372*r))
    (μ : Measure (Configuration n L)) [IsProbabilityMeasure μ]
    (hallowed : ∀ᵐ Y ∂μ, Y ∈ allowed n L r) (p : ℝ≥0∞)
    (hbad : ∀ A : Finset (DiscreteTorus K), μ {Y | A ⊆ closeSet L s T Y} ≤ p^A.card)
    (hp : 8*((2^27:ℕ):ℝ≥0∞)*p ≤ (2:ℝ≥0∞)⁻¹) :
    (∫⁻ Y, (volume : Measure (Torus L)) (omitted (microMesh r) r Y) ∂μ) ≤
      ENNReal.ofReal (1029*r^2*n) +
      (K:ℝ≥0∞)^3*(128*(((2^27:ℕ):ℝ≥0∞)*p)) +
      ENNReal.ofReal (L.val^3)*(K:ℝ≥0∞)^3*(((2^27:ℕ):ℝ≥0∞)*p)^M := by
  classical
  let B := closeSet (n := n) (K := K) L s T
  let E := {Y : Configuration n L | LargeBadComponent (torusRangeGraph K 1) (B Y) M}
  have hB : Measurable B := measurable_closeSet L s T
  have hE : MeasurableSet E := by
    exact (Set.to_countable {C : Finset (DiscreteTorus K) |
      LargeBadComponent (torusRangeGraph K 1) C M}).measurableSet.preimage hB
  have hdegree (v : DiscreteTorus K) : (torusRangeGraph K 1).degree v ≤ 27 := by
    simpa using torusRange_degree 1 v
  have hcard : Fintype.card (DiscreteTorus K) = K^3 := by
    simp only [DiscreteTorus,Fintype.card_fun,ZMod.card,Fintype.card_fin]
  have hcost := animalCost_mean_le (torusRangeGraph K 1) 27 hdegree μ B hB p hbad boxWeight
  rw [hcard,Nat.cast_pow] at hcost
  have hprob := largeBadComponent_measure (torusRangeGraph K 1) 27 hdegree μ B p hbad M hM
  rw [hcard,Nat.cast_pow] at hprob
  have hi : (fun Y ↦ if Y∈E then ENNReal.ofReal (L.val^3) else 0) =
      E.indicator (fun _ ↦ ENNReal.ofReal (L.val^3)) := by
    ext Y
    simp only [Set.indicator_apply]
  calc
    _ ≤ ∫⁻ Y, ENNReal.ofReal (1029*r^2*n) + animalCost (torusRangeGraph K 1) (B Y) boxWeight +
        (if Y∈E then ENNReal.ofReal (L.val^3) else 0) ∂μ := by
      apply lintegral_mono_ae
      filter_upwards [hallowed] with Y hY
      exact omitted_volume_le hr hrsmall hL hLK hMK hrs hT Y hY
    _ = ENNReal.ofReal (1029*r^2*n) + (∫⁻ Y, animalCost (torusRangeGraph K 1) (B Y) boxWeight ∂μ) +
        ENNReal.ofReal (L.val^3)*μ E := by
      have hm : Measurable (fun Y ↦ ENNReal.ofReal (1029*r^2*n) +
          animalCost (torusRangeGraph K 1) (B Y) boxWeight) :=
        measurable_const.add (measurable_animalCost _ B hB _)
      rw [lintegral_add_left hm,
        lintegral_add_left measurable_const,hi,lintegral_indicator_const hE,lintegral_const]
      simp only [measure_univ,mul_one]
    _ ≤ _ := by
      apply add_le_add
      · apply add_le_add_right
        exact hcost.trans (mul_le_mul' le_rfl (box_series_le (by simpa only [mul_assoc] using hp)))
      · exact (mul_le_mul' le_rfl hprob).trans_eq (by ring)

end HardSphere.BathSlice

end

end OAI
