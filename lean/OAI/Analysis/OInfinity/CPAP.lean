import OAI.Analysis.OInfinity.FockRangeProjection
import OAI.Analysis.Nuclearity.CPMultiplicativeDefect
import OAI.Analysis.WeakInfiniteness.CentralOInfinityCopies

namespace OAI

/-! # Completely positive finite-dimensional approximation of O∞ -/

noncomputable section
open scoped CStarAlgebra ComplexOrder
open Filter Topology

namespace WeakPureInfiniteness

local instance : PartialOrder OInfinity := CStarAlgebra.spectralOrder _
local instance : StarOrderedRing OInfinity := CStarAlgebra.spectralOrderedRing _
local instance : Module ℝ OInfinity := Module.complexToReal _
local instance : NormedSpace ℝ OInfinity := NormedSpace.restrictScalars ℝ ℂ _
local instance : IsBoundedSMul ℝ OInfinity := NormedSpace.toIsBoundedSMul
local instance : ContinuousSMul ℝ OInfinity := IsBoundedSMul.continuousSMul

def oInfinityApproximationSequence (n : ℕ) : OInfinity →L[ℂ] OInfinity :=
  oInfinityFockApproximation n (n + 1)

lemma oInfinityApproximationSequence_one (n : ℕ) :
    oInfinityApproximationSequence n 1 = 1 := oInfinityFockApproximation_one _ _

lemma oInfinityApproximationSequence_cp (n : ℕ) :
    CompletelyPositive (oInfinityApproximationSequence n) := oInfinityFockApproximation_cp _ _

lemma oInfinityApproximationSequence_norm_le (n : ℕ) :
    ‖oInfinityApproximationSequence n‖ ≤ 1 := oInfinityFockApproximation_norm_le _ _

lemma oInfinityApproximationSequence_generator_tendsto (p : ℕ) :
    Tendsto (fun n => oInfinityApproximationSequence n (oInfinityIsometry p))
      atTop (𝓝 (oInfinityIsometry p)) := by
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  apply squeeze_zero' (Filter.Eventually.of_forall (fun _ => norm_nonneg _))
  · filter_upwards [eventually_gt_atTop p] with n hn
    simpa only [oInfinityApproximationSequence, Nat.cast_add, Nat.cast_one, add_assoc,
      one_add_one_eq_two] using
      oInfinityFockApproximation_generator_norm_le (m := n + 1) (⟨p, hn⟩ : Fin n)
  · exact tendsto_inv_atTop_zero.comp
      (tendsto_atTop_add_const_right atTop (2 : ℝ) tendsto_natCast_atTop_atTop)

lemma oInfinityApproximationSequence_rangeProjection_tendsto (p : ℕ) :
    Tendsto (fun n => oInfinityApproximationSequence n
      (oInfinityIsometry p * star (oInfinityIsometry p))) atTop
      (𝓝 (oInfinityIsometry p * star (oInfinityIsometry p))) := by
  have hc : Tendsto (fun n : ℕ => ((n : ℝ) + 1) / ((n : ℝ) + 2)) atTop (𝓝 1) := by
    have ht : Tendsto (fun n : ℕ => ((n : ℝ) + 2)⁻¹) atTop (𝓝 0) :=
      tendsto_inv_atTop_zero.comp
        (tendsto_atTop_add_const_right atTop (2 : ℝ) tendsto_natCast_atTop_atTop)
    have he (n : ℕ) : ((n : ℝ) + 1) / ((n : ℝ) + 2) = 1 - ((n : ℝ) + 2)⁻¹ := by
      field_simp [show (n : ℝ) + 2 ≠ 0 by positivity]
      ring
    simpa only [he, sub_zero] using tendsto_const_nhds.sub ht
  have ht : Tendsto (fun n : ℕ => (((n : ℝ) + 1) / ((n : ℝ) + 2)) •
      (oInfinityIsometry p * star (oInfinityIsometry p))) atTop
      (𝓝 (oInfinityIsometry p * star (oInfinityIsometry p))) := by
    simpa only [one_smul] using hc.smul_const (oInfinityIsometry p * star (oInfinityIsometry p))
  apply ht.congr'
  filter_upwards [eventually_gt_atTop p] with n hn
  exact (oInfinityFockApproximation_rangeProjection_succ (r := n) (⟨p, hn⟩ : Fin n)).symm

lemma oInfinityApproximationSequence_word_tendsto (w : List (ℕ × Bool)) :
    Tendsto (fun n => oInfinityApproximationSequence n (cuntzWord oInfinityIsometry w))
      atTop (𝓝 (cuntzWord oInfinityIsometry w)) := by
  induction w with
  | nil => simpa only [cuntzWord, oInfinityApproximationSequence_one] using tendsto_const_nhds
  | cons z w ih =>
    rcases z with ⟨p, b⟩
    cases b with
    | false =>
      change Tendsto (fun n => oInfinityApproximationSequence n
        (star (oInfinityIsometry p) * cuntzWord oInfinityIsometry w)) atTop
          (𝓝 (star (oInfinityIsometry p) * cuntzWord oInfinityIsometry w))
      apply completelyPositive_mul_tendsto oInfinityApproximationSequence_cp
        oInfinityApproximationSequence_one _ _ ih
      · simpa only [completelyPositive_map_star (oInfinityApproximationSequence_cp _)] using
          (oInfinityApproximationSequence_generator_tendsto p).star
      · have hrel : star (oInfinityIsometry p) * star (star (oInfinityIsometry p)) = 1 := by
          simpa only [star_star, ite_true] using oInfinityIsometry_relations p p
        simpa only [hrel, oInfinityApproximationSequence_one] using tendsto_const_nhds
    | true =>
      change Tendsto (fun n => oInfinityApproximationSequence n
        (oInfinityIsometry p * cuntzWord oInfinityIsometry w)) atTop
          (𝓝 (oInfinityIsometry p * cuntzWord oInfinityIsometry w))
      exact completelyPositive_mul_tendsto oInfinityApproximationSequence_cp
        oInfinityApproximationSequence_one (oInfinityApproximationSequence_generator_tendsto p)
        (oInfinityApproximationSequence_rangeProjection_tendsto p) ih

lemma oInfinityApproximationSequence_polynomial_tendsto
    (c : List (ℕ × Bool) →₀ ℂ) :
    Tendsto (fun n => oInfinityApproximationSequence n (cuntzPolynomial oInfinityIsometry c))
      atTop (𝓝 (cuntzPolynomial oInfinityIsometry c)) := by
  simp only [cuntzPolynomial, Finsupp.sum, map_sum, map_smul]
  exact tendsto_finsetSum _ (fun w _ =>
    (oInfinityApproximationSequence_word_tendsto w).const_smul (c w))

lemma oInfinityApproximationSequence_tendsto (a : OInfinity) :
    Tendsto (fun n => oInfinityApproximationSequence n a) atTop (𝓝 a) := by
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  obtain ⟨c, hc⟩ := Metric.denseRange_iff.mp oInfinityPolynomial_denseRange a (ε / 3) (by positivity)
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp (oInfinityApproximationSequence_polynomial_tendsto c)
    (ε / 3) (by positivity)
  refine ⟨N, fun n hn => ?_⟩
  have hcontract : dist (oInfinityApproximationSequence n a)
      (oInfinityApproximationSequence n (cuntzPolynomial oInfinityIsometry c)) ≤
      dist a (cuntzPolynomial oInfinityIsometry c) := by
    rw [dist_eq_norm, ← map_sub, dist_eq_norm]
    exact (ContinuousLinearMap.le_opNorm _ _).trans
      (by simpa only [one_mul] using (mul_le_mul_of_nonneg_right
        (oInfinityApproximationSequence_norm_le n) (norm_nonneg _)))
  have ht := dist_triangle4 (oInfinityApproximationSequence n a)
    (oInfinityApproximationSequence n (cuntzPolynomial oInfinityIsometry c))
    (cuntzPolynomial oInfinityIsometry c) a
  have hm := hN n hn
  have hc' : dist (cuntzPolynomial oInfinityIsometry c) a < ε / 3 := by
    simpa only [dist_comm] using hc
  linarith

abbrev oInfinityApproximationDimension (n : ℕ) :=
  Fintype.card (FiniteFockIndex n (n + 1))

def oInfinityApproximationReindex (n : ℕ) :
    CStarMatrix (FiniteFockIndex n (n + 1)) (FiniteFockIndex n (n + 1)) ℂ ≃⋆ₐ[ℂ]
      CStarMatrix (Fin (oInfinityApproximationDimension n))
        (Fin (oInfinityApproximationDimension n)) ℂ :=
  CStarMatrix.reindexₐ ℂ ℂ (Fintype.equivFin _)

def oInfinityCPAPCompression (n : ℕ) : OInfinity →L[ℂ]
    CStarMatrix (Fin (oInfinityApproximationDimension n))
      (Fin (oInfinityApproximationDimension n)) ℂ :=
  (starHomContinuousLinear
    (oInfinityApproximationReindex n).toStarAlgHom.toNonUnitalStarAlgHom).comp
      (oInfinityFockCompression n (n + 1))

def oInfinityCPAPReturn (n : ℕ) :
    CStarMatrix (Fin (oInfinityApproximationDimension n))
      (Fin (oInfinityApproximationDimension n)) ℂ →L[ℂ] OInfinity :=
  (oInfinityFockReturn n (n + 1)).comp
    (starHomContinuousLinear
      (oInfinityApproximationReindex n).symm.toStarAlgHom.toNonUnitalStarAlgHom)

lemma oInfinityCPAPCompression_cp (n : ℕ) : CompletelyPositive (oInfinityCPAPCompression n) := by
  intro k X hX
  exact map_nonneg (CStarMatrix.mapₙₐ
    (oInfinityApproximationReindex n).toStarAlgHom.toNonUnitalStarAlgHom)
      (oInfinityFockCompression_cp n (n + 1) k X hX)

lemma oInfinityCPAPReturn_cp (n : ℕ) : CompletelyPositive (oInfinityCPAPReturn n) := by
  intro k X hX
  exact oInfinityFockReturn_cp n (n + 1) k _
    (map_nonneg (CStarMatrix.mapₙₐ
      (oInfinityApproximationReindex n).symm.toStarAlgHom.toNonUnitalStarAlgHom) hX)

lemma oInfinityCPAPCompression_one (n : ℕ) : oInfinityCPAPCompression n 1 = 1 := by
  change oInfinityApproximationReindex n (oInfinityFockCompression n (n + 1) 1) = 1
  rw [oInfinityFockCompression_one, map_one]

lemma oInfinityCPAPReturn_one (n : ℕ) : oInfinityCPAPReturn n 1 = 1 := by
  change oInfinityFockReturn n (n + 1) ((oInfinityApproximationReindex n).symm 1) = 1
  rw [map_one, oInfinityFockReturn_one]

lemma oInfinityCPAP_comp (n : ℕ) (a : OInfinity) :
    oInfinityCPAPReturn n (oInfinityCPAPCompression n a) =
      oInfinityApproximationSequence n a := by
  change oInfinityFockReturn n (n + 1)
    ((oInfinityApproximationReindex n).symm
      (oInfinityApproximationReindex n (oInfinityFockCompression n (n + 1) a))) = _
  rw [StarAlgEquiv.symm_apply_apply]
  rfl

theorem oInfinity_nuclear : Nuclear OInfinity := by
  intro F ε hε
  have he : ∀ᶠ n : ℕ in atTop, ∀ a ∈ F,
      ‖oInfinityApproximationSequence n a - a‖ < ε := by
    apply (Filter.eventually_all_finset F).mpr
    intro a _
    exact (tendsto_iff_norm_sub_tendsto_zero.mp (oInfinityApproximationSequence_tendsto a))
      (eventually_lt_nhds hε)
  obtain ⟨n, hn⟩ := he.exists
  have hdim : 1 ≤ oInfinityApproximationDimension n := by
    apply Nat.succ_le_of_lt
    apply Fintype.card_pos_iff.mpr
    exact ⟨⟨0, Fin.elim0⟩⟩
  refine ⟨oInfinityApproximationDimension n, hdim,
    oInfinityCPAPCompression n, oInfinityCPAPReturn n,
    oInfinityCPAPCompression_cp n, oInfinityCPAPReturn_cp n,
    completelyPositive_norm_le_of_unital (oInfinityCPAPCompression_cp n)
      (oInfinityCPAPCompression_one n),
    completelyPositive_norm_le_of_unital (oInfinityCPAPReturn_cp n)
      (oInfinityCPAPReturn_one n), ?_⟩
  intro a ha
  rw [oInfinityCPAP_comp]
  exact hn a ha

end WeakPureInfiniteness

end

end OAI
