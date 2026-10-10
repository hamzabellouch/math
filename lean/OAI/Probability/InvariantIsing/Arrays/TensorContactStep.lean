import OAI.Probability.InvariantIsing.Fields.FieldCapEstimate
import OAI.Probability.IsingPerceptron.TimeIncrement

namespace OAI

/-! The contact increment coordinates represent the same fixed-partition
fields and pairings as the one-site variational functional. -/

noncomputable section
open MeasureTheory IsingPerceptron Set
open scoped BigOperators

namespace InvariantIsing

def contactFieldStep {n : ℕ} (cut : Fin (n + 2) → ℝ) (hc : StrictMono cut)
    (hfirst : cut 0 = 0) (hlast : cut (Fin.last (n + 1)) = 1)
    (a : Fin (n + 1) → ℝ) (ha : ∀ i, 0 ≤ a i) : FieldStep where
  depth := n
  cut := cut
  ordered_cut := hc
  first := hfirst
  last := hlast
  height i := finiteFieldPath a i
  nonneg i := finiteFieldPath_nonneg ha i
  ordered_height _i _j hij := monotone_finiteFieldPath ha hij

lemma fieldPairing_of_step_trial (p : OverlapPath) (h : FieldStep)
    (v : Fin (h.depth + 1) → ℝ)
    (hv : ∀ i s, s ∈ Ioo (h.cut i.castSucc) (h.cut i.succ) → p s = v i) :
    fieldPairing p h = ∑ i, (h.cut i.succ - h.cut i.castSucc) * v i * h.height i := by
  unfold fieldPairing
  calc
    _ = ∫ s, finiteStepFunction h.cut (fun i => v i * h.height i) s ∂pathMeasure := by
      apply integral_congr_ae
      refine ae_of_all _ fun s => ?_
      simp only [fieldFunction, finiteStepFunction, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      split_ifs with hi
      · rw [hv i s hi]
      · simp
    _ = ∑ i, (h.cut i.succ - h.cut i.castSucc) * (v i * h.height i) :=
      integral_finiteStepFunction h.cut h.ordered_cut h.first h.last _
    _ = _ := by simp only [mul_assoc]

lemma fieldPairing_contactFieldStep {n : ℕ} (p : OverlapPath)
    (cut : Fin (n + 2) → ℝ) (hc : StrictMono cut)
    (hfirst : cut 0 = 0) (hlast : cut (Fin.last (n + 1)) = 1)
    (a : Fin (n + 1) → ℝ) (ha : ∀ i, 0 ≤ a i) (v : Fin (n + 1) → ℝ)
    (hv : ∀ i s, s ∈ Ioo (cut i.castSucc) (cut i.succ) → p s = v i) :
    fieldPairing p (contactFieldStep cut hc hfirst hlast a ha) =
      ∑ i, ((cut i.succ - cut i.castSucc) * v i) * finiteFieldPath a i :=
  fieldPairing_of_step_trial p (contactFieldStep cut hc hfirst hlast a ha) v hv


lemma heightSequence_contactFieldStep {n : ℕ} (cut : Fin (n + 2) → ℝ) (hc : StrictMono cut)
    (hfirst : cut 0 = 0) (hlast : cut (Fin.last (n + 1)) = 1)
    (a : Fin (n + 1) → ℝ) (ha : ∀ i, 0 ≤ a i) :
    heightSequence (contactFieldStep cut hc hfirst hlast a ha) = finiteFieldPath a := by
  funext i
  change finiteFieldPath a (min i n) = finiteFieldPath a i
  unfold finiteFieldPath
  apply Finset.sum_congr rfl
  intro j _
  have he : j.val ≤ min i n ↔ j.val ≤ i := by omega
  simp only [he]

lemma fieldPartitionConstant_contactFieldStep {n : ℕ}
    (cut : Fin (n + 2) → ℝ) (hc : StrictMono cut)
    (hfirst : cut 0 = 0) (hlast : cut (Fin.last (n + 1)) = 1)
    (a : Fin (n + 1) → ℝ) (ha : ∀ i, 0 ≤ a i) :
    fieldPartitionConstant (contactFieldStep cut hc hfirst hlast a ha) =
      ∑ i : Fin n, Real.log 2 / cut i.succ.castSucc := rfl

end InvariantIsing

end

end OAI
