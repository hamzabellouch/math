import OAI.LinearAlgebra.MatrixMultiplication.FieldConstruction.NativeLaws

namespace OAI

/-! Tensor extraction over arbitrary fields and its asymptotic rate. -/

noncomputable section

namespace MatrixMultiplication.AllFieldPairMarginals

open MatrixMultiplication.Foundation AllFieldParameters AllFieldHistory AllFieldNativeCapacity
open scoped BigOperators
attribute [local instance] Classical.propDecidable Classical.decEq

theorem statistic_weight_mass {A : Type*} [Fintype A]
    (q : A → ℝ) (weight : A → Fin 17) (own : ℕ)
    (hq : ∀ a, 0 ≤ q a) (htotal : ∑ a, q a = 1)
    (hweight : ∀ a, 0 < q a → (weight a).val = own) (k : Fin 17) :
    (∑ a, if weight a = k then q a else 0) = if own = k.val then 1 else 0 := by
  have hterm (a : A) : (if weight a = k then q a else 0) =
      if own = k.val then q a else 0 := by
    by_cases ha : q a = 0
    · simp only [ha, ite_self]
    · have hw := hweight a (lt_of_le_of_ne (hq a) (Ne.symm ha))
      have he : weight a = k ↔ own = k.val := by rw [Fin.ext_iff, hw]
      simp only [he]
  simp_rw [hterm]
  split_ifs <;> simp_all

theorem pairLaw_leftWeight_mass {A : Type*} [Fintype A]
    (support : List Shape) (s : Shape) (p : Shape → ℝ) (q : Shape → A → ℝ)
    (side : Fin 3) (weight : A → Fin 17)
    (hq : ∀ u ∈ support, ∀ a, 0 ≤ q u a)
    (hleft : ∀ u ∈ support, ∑ a, q u a = 1)
    (hright : ∀ u ∈ support, ∑ a, q (complement s u) a = 1)
    (hweight : ∀ u ∈ support, ∀ a, 0 < q u a → (weight a).val = u side)
    (k : Fin 17) :
    (∑ ij : A × A, if weight ij.1 = k then pairLaw support s p q ij else 0) =
      marginal support p side k := by
  unfold pairLaw marginal
  induction support with
  | nil => simp
  | cons u us ih =>
      have hu : u ∈ u :: us := by simp
      have hw := statistic_weight_mass (q u) weight (u side)
        (hq u hu) (hleft u hu) (hweight u hu) k
      have hr := hright u hu
      have head : (∑ ij : A × A, if weight ij.1 = k then
          p u * q u ij.1 * q (complement s u) ij.2 else 0) =
            if u side = k.val then p u else 0 := by
        rw [Fintype.sum_prod_type]
        calc
          _ = ∑ a, if weight a = k then p u * q u a else 0 := by
            apply Finset.sum_congr rfl
            intro a _
            by_cases ha : weight a = k
            · simp only [ha, ite_true, ← Finset.mul_sum, hr, mul_one]
            · simp [ha]
          _ = p u * (∑ a, if weight a = k then q u a else 0) := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro a _
            split_ifs <;> simp
          _ = _ := by rw [hw]; split_ifs <;> simp
      have tail := ih (fun v hv => hq v (by simp [hv]))
        (fun v hv => hleft v (by simp [hv]))
        (fun v hv => hright v (by simp [hv]))
        (fun v hv => hweight v (by simp [hv]))
      simpa only [List.map_cons, List.sum_cons, ite_add_zero, Finset.sum_add_distrib,
        head] using congrArg (fun r : ℝ => (if u side = k.val then p u else 0) + r) tail

def statisticWeightCode (a : Fin 6) : Fin 17 :=
  ⟨statisticWeight a, by have := statisticWeight_le_four a; omega⟩

def halfWeightCode (a : PairSlot) : Fin 17 :=
  ⟨statisticWeight a.1 + statisticWeight a.2, by
    have := statisticWeight_le_four a.1
    have := statisticWeight_le_four a.2
    omega⟩

@[simp] theorem statisticWeightCode_val (a : Fin 6) :
    (statisticWeightCode a).val = statisticWeight a := rfl

@[simp] theorem halfWeightCode_val (a : PairSlot) :
    (halfWeightCode a).val = statisticWeight a.1 + statisticWeight a.2 := rfl

theorem littleLaw_positive_weight (t : Shape) (ht : t ∈ positiveSecond)
    (u : Shape) (hu : u ∈ below t) (side : Fin 3) (a : Fin 6)
    (ha : 0 < (littleLaw t u side a : ℝ)) : (statisticWeightCode a).val = u side := by
  change statisticWeight a = u side
  by_contra hne
  have hz := littleLaw_outside_support t u side
    (child_statistic_weight_bounded t ht u hu side) a hne
  have hz' : (littleLaw t u side a : ℝ) = 0 := by exact_mod_cast hz
  linarith

theorem halfLaw_positive_weight (u : Shape) (hu : u ∈ shapes 8)
    (side : Fin 3) (a : PairSlot) (ha : 0 < (halfLaw u side a : ℝ)) :
    (halfWeightCode a).val = u side := by
  change statisticWeight a.1 + statisticWeight a.2 = u side
  by_contra hne
  have hz := halfLaw_outside_support u hu side a hne
  have hz' : (halfLaw u side a : ℝ) = 0 := by exact_mod_cast hz
  linarith

theorem stageBPairLaw_leftWeight_mass (t : Shape) (ht : t ∈ positiveSecond)
    (side : Fin 3) (k : Fin 17) :
    ((stageBPairLaw t ht side).map (fun ij => statisticWeightCode ij.1)).mass k =
      (stageBMarginalLaw t ht side).mass k := by
  rw [FiniteLaw.map_mass]
  change (∑ ij : Fin 6 × Fin 6, if statisticWeightCode ij.1 = k then
    pairLaw (below t) t (fun u => (stageBLaw t u : ℝ))
      (fun u a => (littleLaw t u side a : ℝ)) ij else 0) = _
  rw [pairLaw_leftWeight_mass (below t) t (fun u => (stageBLaw t u : ℝ))
    (fun u a => (littleLaw t u side a : ℝ)) side statisticWeightCode
    (fun u _ a => Rat.cast_nonneg.mpr (littleLaw_nonnegative t u side a))
    (fun u _ => (littleFiniteLaw t u side).total)
    (fun u _ => (littleFiniteLaw t (complement t u) side).total)
    (fun u hu a => littleLaw_positive_weight t ht u hu side a)]
  exact (indexedMarginalLaw_mass _ _ _ _ _ _ k).symm

theorem stageAPairLaw_leftWeight_mass (g : Shape) (hg : g ∈ positiveInitial)
    (side : Fin 3) (k : Fin 17) :
    ((stageAPairLaw g hg side).map (fun ij => halfWeightCode ij.1)).mass k =
      (stageAMarginalLaw g hg side).mass k := by
  rw [FiniteLaw.map_mass]
  change (∑ ij : PairSlot × PairSlot, if halfWeightCode ij.1 = k then
    pairLaw (below g) g (fun u => (stageALaw g u : ℝ))
      (fun u a => (halfLaw u side a : ℝ)) ij else 0) = _
  rw [pairLaw_leftWeight_mass (below g) g (fun u => (stageALaw g u : ℝ))
    (fun u a => (halfLaw u side a : ℝ)) side halfWeightCode
    (fun u _ a => Rat.cast_nonneg.mpr (halfLaw_nonnegative u side a))
    (fun u hu => (halfFiniteLaw u (stageA_children_size g hg u hu) side).total)
    (fun u hu => (halfFiniteLaw (complement g u)
      (stageA_children_size g hg _ (stageA_support_complement g hg u hu).1) side).total)
    (fun u hu a => halfLaw_positive_weight u (stageA_children_size g hg u hu) side a)]
  exact (indexedMarginalLaw_mass _ _ _ _ _ _ k).symm

private theorem law_ext {A : Type*} [Fintype A] (p q : FiniteLaw A)
    (h : ∀ a, p.mass a = q.mass a) : p = q := by
  cases p with
  | mk p hp htotal =>
      cases q with
      | mk q hq hqtotal =>
          have heq : p = q := funext h
          subst q
          rfl

theorem stageBPairLaw_leftWeight_marginal (t : Shape) (ht : t ∈ positiveSecond)
    (side : Fin 3) :
    (stageBPairLaw t ht side).map (fun ij => statisticWeightCode ij.1) =
      stageBMarginalLaw t ht side :=
  law_ext _ _ (stageBPairLaw_leftWeight_mass t ht side)

theorem stageAPairLaw_leftWeight_marginal (g : Shape) (hg : g ∈ positiveInitial)
    (side : Fin 3) :
    (stageAPairLaw g hg side).map (fun ij => halfWeightCode ij.1) =
      stageAMarginalLaw g hg side :=
  law_ext _ _ (stageAPairLaw_leftWeight_mass g hg side)

end MatrixMultiplication.AllFieldPairMarginals

end

end OAI
