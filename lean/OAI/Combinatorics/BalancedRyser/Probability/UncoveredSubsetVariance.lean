import OAI.Combinatorics.BalancedRyser.Probability.FiniteUniformVariance
import OAI.Combinatorics.BalancedRyser.Probability.ProductSubsetVariance
import OAI.Combinatorics.BalancedRyser.Probability.UncoveredExchange

namespace OAI

open scoped BigOperators
open MeasureTheory ProbabilityTheory

namespace Balanced.UncoveredSampling

open WithoutReplacement UncoveredExchange

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

noncomputable def planeFraction (S T : Finset (Line F)) : ℝ :=
  ((uncoveredBy (S ∪ T)).card : ℝ) / (Fintype.card F : ℝ)^2

noncomputable def targetFraction (L : Line F) (S T : Finset (Line F)) : ℝ :=
  ((linePoints L ∩ uncoveredBy (S ∪ T)).card : ℝ) / (Fintype.card F : ℝ)

theorem planeFraction_exchange_left (S T : Finset (Line F))
    {a : Line F} (ha : a ∈ S) (b : Line F) :
    |planeFraction S T - planeFraction (insert b (S.erase a)) T| ≤
      2 / (Fintype.card F : ℝ) := by
  simpa only [planeFraction, ← Finset.insert_union, Finset.insert_erase ha] using
    normalized_plane_exchange_bound (S.erase a ∪ T) a b

theorem planeFraction_exchange_right (S T : Finset (Line F))
    {a : Line F} (ha : a ∈ T) (b : Line F) :
    |planeFraction S T - planeFraction S (insert b (T.erase a))| ≤
      2 / (Fintype.card F : ℝ) := by
  simpa only [planeFraction, ← Finset.union_insert, Finset.insert_erase ha] using
    normalized_plane_exchange_bound (S ∪ T.erase a) a b

theorem targetFraction_exchange_left (L : Line F) (S T : Finset (Line F))
    {a : Line F} (ha : a ∈ S) (b : Line F) (hLa : L ≠ a) (hLb : L ≠ b) :
    |targetFraction L S T - targetFraction L (insert b (S.erase a)) T| ≤
      2 / (Fintype.card F : ℝ) := by
  simpa only [targetFraction, ← Finset.insert_union, Finset.insert_erase ha] using
    normalized_target_exchange_bound (S.erase a ∪ T) L a b hLa hLb

theorem targetFraction_exchange_right (L : Line F) (S T : Finset (Line F))
    {a : Line F} (ha : a ∈ T) (b : Line F) (hLa : L ≠ a) (hLb : L ≠ b) :
    |targetFraction L S T - targetFraction L S (insert b (T.erase a))| ≤
      2 / (Fintype.card F : ℝ) := by
  simpa only [targetFraction, ← Finset.union_insert, Finset.insert_erase ha] using
    normalized_target_exchange_bound (S ∪ T.erase a) L a b hLa hLb

theorem planeFraction_variance_le (U V : Finset (Line F)) (m n : ℕ)
    (hm : m ≤ U.card) (hn : n ≤ V.card) :
    finiteVariance (U.powersetCard m ×ˢ V.powersetCard n)
      (fun p => planeFraction p.1 p.2) ≤
        4 * ((m : ℝ) + n) / (Fintype.card F : ℝ)^2 := by
  have hc : 0 ≤ 2 / (Fintype.card F : ℝ) := by positivity
  have h := finiteVariance_powersetCard_product_le U V m n planeFraction
    hc hc hm hn
    (fun S _ _ T _ _ a ha b _ _ => planeFraction_exchange_left S T ha b)
    (fun S _ _ T _ _ a ha b _ _ => planeFraction_exchange_right S T ha b)
  refine h.trans_eq ?_
  ring

theorem targetFraction_variance_le (L : Line F) (U V : Finset (Line F))
    (hLU : L ∉ U) (hLV : L ∉ V) (m n : ℕ)
    (hm : m ≤ U.card) (hn : n ≤ V.card) :
    finiteVariance (U.powersetCard m ×ˢ V.powersetCard n)
      (fun p => targetFraction L p.1 p.2) ≤
        4 * ((m : ℝ) + n) / (Fintype.card F : ℝ)^2 := by
  have hc : 0 ≤ 2 / (Fintype.card F : ℝ) := by positivity
  have h := finiteVariance_powersetCard_product_le U V m n (targetFraction L)
    hc hc hm hn
    (fun S hSU _ T _ _ a ha b hb _ =>
      targetFraction_exchange_left L S T ha b
        (fun heq => hLU (heq ▸ hSU ha)) (fun heq => hLU (heq ▸ hb)))
    (fun S _ _ T hTV _ a ha b hb _ =>
      targetFraction_exchange_right L S T ha b
        (fun heq => hLV (heq ▸ hTV ha)) (fun heq => hLV (heq ▸ hb)))
  refine h.trans_eq ?_
  ring

omit [DecidableEq F] in

theorem scaled_exposure_bound (m n : ℕ) {C : ℝ}
    (hsize : (m : ℝ) + n ≤ C * (Fintype.card F : ℝ)) :
    4 * ((m : ℝ) + n) / (Fintype.card F : ℝ)^2 ≤
      4 * C / (Fintype.card F : ℝ) := by
  have hq : (0 : ℝ) < Fintype.card F := by positivity
  calc
    _ ≤ 4 * (C * (Fintype.card F : ℝ)) / (Fintype.card F : ℝ)^2 := by
      apply div_le_div_of_nonneg_right _ (sq_nonneg _)
      linarith
    _ = _ := by field_simp

theorem planeFraction_variance_le_scaled (U V : Finset (Line F)) (m n : ℕ)
    (hm : m ≤ U.card) (hn : n ≤ V.card) {C : ℝ}
    (hsize : (m : ℝ) + n ≤ C * (Fintype.card F : ℝ)) :
    finiteVariance (U.powersetCard m ×ˢ V.powersetCard n)
      (fun p => planeFraction p.1 p.2) ≤ 4 * C / (Fintype.card F : ℝ) :=
  (planeFraction_variance_le U V m n hm hn).trans (scaled_exposure_bound m n hsize)

theorem targetFraction_variance_le_scaled (L : Line F) (U V : Finset (Line F))
    (hLU : L ∉ U) (hLV : L ∉ V) (m n : ℕ)
    (hm : m ≤ U.card) (hn : n ≤ V.card) {C : ℝ}
    (hsize : (m : ℝ) + n ≤ C * (Fintype.card F : ℝ)) :
    finiteVariance (U.powersetCard m ×ˢ V.powersetCard n)
      (fun p => targetFraction L p.1 p.2) ≤ 4 * C / (Fintype.card F : ℝ) :=
  (targetFraction_variance_le L U V hLU hLV m n hm hn).trans
    (scaled_exposure_bound m n hsize)

abbrev SamplePair (F : Type*) := Finset (Line F) × Finset (Line F)

noncomputable def sampleLaw (U V : Finset (Line F)) (m n : ℕ)
    (hm : m ≤ U.card) (hn : n ≤ V.card) : PMF (SamplePair F) :=
  PMF.uniformOfFinset (U.powersetCard m ×ˢ V.powersetCard n)
    ((Finset.powersetCard_nonempty.mpr hm).product
      (Finset.powersetCard_nonempty.mpr hn))

omit [Field F] [Fintype F] [DecidableEq F] in

theorem sampleLaw_apply_product (U V : Finset (Line F)) (m n : ℕ)
    (hm : m ≤ U.card) (hn : n ≤ V.card) (S T : Finset (Line F)) :
    sampleLaw U V m n hm hn (S, T) =
      PMF.uniformOfFinset (U.powersetCard m) (Finset.powersetCard_nonempty.mpr hm) S *
      PMF.uniformOfFinset (V.powersetCard n) (Finset.powersetCard_nonempty.mpr hn) T :=
  uniformOfFinset_product_apply _ _ _ _ S T

section MeasureTransport

variable [MeasurableSpace (SamplePair F)] [MeasurableSingletonClass (SamplePair F)]

omit [Field F] [DecidableEq F] in

theorem variance_sampleLaw (U V : Finset (Line F)) (m n : ℕ)
    (hm : m ≤ U.card) (hn : n ≤ V.card) (f : SamplePair F → ℝ) :
    variance f (sampleLaw U V m n hm hn).toMeasure =
      finiteVariance (U.powersetCard m ×ˢ V.powersetCard n) f :=
  variance_uniformOfFinset _ _ f

theorem planeFraction_measure_variance_le (U V : Finset (Line F)) (m n : ℕ)
    (hm : m ≤ U.card) (hn : n ≤ V.card) :
    variance (fun p : SamplePair F => planeFraction p.1 p.2)
      (sampleLaw U V m n hm hn).toMeasure ≤
        4 * ((m : ℝ) + n) / (Fintype.card F : ℝ)^2 := by
  rw [variance_sampleLaw]
  exact planeFraction_variance_le U V m n hm hn

theorem targetFraction_measure_variance_le (L : Line F) (U V : Finset (Line F))
    (hLU : L ∉ U) (hLV : L ∉ V) (m n : ℕ)
    (hm : m ≤ U.card) (hn : n ≤ V.card) :
    variance (fun p : SamplePair F => targetFraction L p.1 p.2)
      (sampleLaw U V m n hm hn).toMeasure ≤
        4 * ((m : ℝ) + n) / (Fintype.card F : ℝ)^2 := by
  rw [variance_sampleLaw]
  exact targetFraction_variance_le L U V hLU hLV m n hm hn

theorem planeFraction_measure_variance_le_scaled (U V : Finset (Line F)) (m n : ℕ)
    (hm : m ≤ U.card) (hn : n ≤ V.card) {C : ℝ}
    (hsize : (m : ℝ) + n ≤ C * (Fintype.card F : ℝ)) :
    variance (fun p : SamplePair F => planeFraction p.1 p.2)
      (sampleLaw U V m n hm hn).toMeasure ≤ 4 * C / (Fintype.card F : ℝ) := by
  rw [variance_sampleLaw]
  exact planeFraction_variance_le_scaled U V m n hm hn hsize

theorem targetFraction_measure_variance_le_scaled (L : Line F)
    (U V : Finset (Line F)) (hLU : L ∉ U) (hLV : L ∉ V) (m n : ℕ)
    (hm : m ≤ U.card) (hn : n ≤ V.card) {C : ℝ}
    (hsize : (m : ℝ) + n ≤ C * (Fintype.card F : ℝ)) :
    variance (fun p : SamplePair F => targetFraction L p.1 p.2)
      (sampleLaw U V m n hm hn).toMeasure ≤ 4 * C / (Fintype.card F : ℝ) := by
  rw [variance_sampleLaw]
  exact targetFraction_variance_le_scaled L U V hLU hLV m n hm hn hsize

end MeasureTransport

end Balanced.UncoveredSampling

end OAI
