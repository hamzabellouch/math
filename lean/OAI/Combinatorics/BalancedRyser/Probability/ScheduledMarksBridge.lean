import OAI.Combinatorics.BalancedRyser.Probability.ScheduledCountingExposure
import OAI.Combinatorics.BalancedRyser.Profiles.ProfileScheduledMarks

namespace OAI

namespace Balanced.ScheduledMarksBridge

noncomputable section
attribute [local instance] Classical.propDecidable
open scoped BigOperators
open ExposureInterleaving ConditionalOrderVariance ProfileScheduledMarks
open UncoveredSampling

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

def rankMark {n m : ℕ} (d : Fin n → Line F) (c : Fin m → Line F)
    (η ε : ℝ) (s : Step n m) : Prop :=
  η < parameter (Real.sqrt 2) s ∧
    CoverCountingExposure.Marked
      (uncoveredBy ((previousD (Real.sqrt 2) s).image d ∪
        (previousC (Real.sqrt 2) s).image c)) ε (Sum.elim d c s)

def rankCount {n m : ℕ} (d : Fin n → Line F) (c : Fin m → Line F)
    (η ε : ℝ) : ℕ :=
  (Finset.univ.filter (rankMark d c η ε)).card

theorem marked_iff_fraction (S T : Finset (Line F)) (l : Line F) (ε : ℝ) :
    CoverCountingExposure.Marked (uncoveredBy (S ∪ T)) ε l ↔
      ε < |targetFraction l S T - planeFraction S T| := by
  have hset : (uncoveredBy (S ∪ T)).filter (fun p => OnLine p l) =
      linePoints l ∩ uncoveredBy (S ∪ T) := by
    ext p
    simp [linePoints, and_comm]
  simp only [CoverCountingExposure.Marked, affineIntersectionCount, hset,
    targetFraction, planeFraction]

def orderedArray (D : Finset (Line F)) (p : Equiv.Perm D) : Fin D.card → Line F :=
  fun i => (p ((label D).symm i)).val

omit [Field F] [Fintype F] in

theorem population_prefix (D : Finset (Line F)) (p : Equiv.Perm D)
    (s : Finset (Fin D.card)) :
    populationLines D ((s.map (label D).symm.toEmbedding).map p.toEmbedding) =
      s.image (orderedArray D p) := by
  simp only [populationLines, Finset.map_eq_image, Finset.image_image]
  rfl

theorem rankMark_inl (D C : Finset (Line F)) (η ε : ℝ)
    (p : OrderPair D C) (i : Fin D.card) :
    rankMark (orderedArray D p.1) (orderedArray C p.2) η ε (Sum.inl i) ↔
      ProfileMarkedOrders.firstMark D C (ID D C) (JD D C) (zD D) η ε
        ((label D).symm i) p := by
  simp only [ProfileMarkedOrders.firstMark, ID, JD, prefixD, prefixC, stepD,
    zD, Equiv.apply_symm_apply, population_prefix]
  exact and_congr Iff.rfl (marked_iff_fraction _ _ _ _)

theorem rankMark_inr (D C : Finset (Line F)) (η ε : ℝ)
    (p : OrderPair D C) (i : Fin C.card) :
    rankMark (orderedArray D p.1) (orderedArray C p.2) η ε (Sum.inr i) ↔
      ProfileMarkedOrders.firstMark C D (IC D C) (JC D C) (zC C) η ε
        ((label C).symm i) p.swap := by
  simp only [ProfileMarkedOrders.firstMark, IC, JC, prefixD, prefixC, stepC,
    zC, Equiv.apply_symm_apply, Prod.fst_swap, Prod.snd_swap, population_prefix]
  unfold rankMark
  simp only [parameter, Sum.elim_inr]
  rw [Finset.union_comm]
  exact and_congr Iff.rfl (marked_iff_fraction _ _ _ _)

theorem rankCount_eq_sourceMarkCount (D C : Finset (Line F)) (η ε : ℝ)
    (p : OrderPair D C) :
    rankCount (orderedArray D p.1) (orderedArray C p.2) η ε =
      sourceMarkCount D C η ε p := by
  simp only [rankCount, sourceMarkCount, ProfileMarkedOrders.markCount,
    ProfileMarkedOrders.firstMarkCount, Finset.card_eq_sum_ones, Finset.sum_filter]
  rw [Fintype.sum_sum_type]
  congr 1
  · apply Fintype.sum_equiv (label D).symm
    intro i
    simp only [rankMark_inl]
  · apply Fintype.sum_equiv (label C).symm
    intro i
    simp only [rankMark_inr]

theorem rankCount_cast {n n' m m' : ℕ} (hn : n = n') (hm : m = m')
    (d : Fin n' → Line F) (c : Fin m' → Line F) (η ε : ℝ) :
    rankCount (fun i => d (Fin.cast hn i)) (fun i => c (Fin.cast hm i)) η ε =
      rankCount d c η ε := by
  subst n'
  subst m'
  rfl

def populationOrder (D : Finset (Line F)) {n : ℕ} (h : n = D.card) : Fin n ≃ D :=
  (finCongr h).trans (label D).symm

theorem arrayMarkCount_eq_sourceMarkCount {k m : ℕ} (D C : Finset (Line F))
    (hD : k * (Fintype.card F + 1) = D.card) (hC : m = C.card)
    (η ε : ℝ) (p : OrderPair D C) :
    ScheduledCountingExposure.arrayMarkCount
      (fun i => (p.1 (populationOrder D hD i)).val)
      (fun i => (p.2 (populationOrder C hC i)).val)
      (Real.sqrt 2) η ε = sourceMarkCount D C η ε p := by
  change rankCount
    (fun i => orderedArray D p.1 (Fin.cast hD i))
    (fun i => orderedArray C p.2 (Fin.cast hC i)) η ε = _
  rw [rankCount_cast]
  exact rankCount_eq_sourceMarkCount D C η ε p

end
end Balanced.ScheduledMarksBridge

end OAI
