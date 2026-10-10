import OAI.Analysis.CircleDomains.Topology.AffineIntervalImages
import OAI.Analysis.CircleDomains.Selection.AffineTagRestriction
import OAI.Analysis.CircleDomains.Modulus.TimeIncidenceReparametrization
import OAI.Analysis.CircleDomains.Selection.PreterminalTolls

namespace OAI

/-! Exact dust tolls of an affine path restriction. The preterminal cost
corresponds to a half-open old interval, so cut points are never charged twice. -/

open Set Function
open scoped ENNReal Classical

noncomputable section

namespace CircleDomainRigidity

variable {X : Type*} [MetricSpace X]

theorem preterminalToll_eq_timeToll (γ : C(PathTime, X)) (m : X → ℝ≥0∞) :
    preterminalToll γ m = timeToll γ (Iio (⊤ : PathTime)) m := by
  rw [timeToll_eq_indicator]
  unfold preterminalToll
  apply tsum_congr
  intro t
  by_cases ht : t = ⊤ <;> simp [ht, lt_top_iff_ne_top]

theorem boundaryToll_eq_timeToll (γ : C(PathTime, X)) (m : X → ℝ≥0∞) :
    boundaryToll γ m = timeToll γ univ m := by
  rw [timeToll_eq_indicator]
  simp only [mem_univ, ite_true]
  rfl

theorem affine_image_preterminal {a b : PathTime} (hab : a < b) :
    affinePathTime a b '' Iio (⊤ : PathTime) = Ico a b := by
  have he : Iio (⊤ : PathTime) = Ico ⊥ ⊤ := by
    ext t
    simp only [mem_Iio, mem_Ico, bot_le, true_and]
  rw [he, (affinePathTime a b).continuous.image_Ico_of_strictMono
    (affinePathTime_strictMono hab), affinePathTime_zero, affinePathTime_one]

theorem preterminalToll_affine (γ : C(PathTime, X)) (m : X → ℝ≥0∞)
    {a b : PathTime} (hab : a < b) :
    preterminalToll (affineRestrictedPath a b γ) m = timeToll γ (Ico a b) m := by
  rw [preterminalToll_eq_timeToll, ← affine_image_preterminal hab,
    timeToll_image γ _ (affinePathTime_strictMono hab).injective]
  rfl

theorem boundaryToll_affine (γ : C(PathTime, X)) (m : X → ℝ≥0∞)
    {a b : PathTime} (hab : a < b) :
    boundaryToll (affineRestrictedPath a b γ) m = timeToll γ (Icc a b) m := by
  rw [boundaryToll_eq_timeToll, ← range_affinePathTime hab, ← image_univ,
    timeToll_image γ _ (affinePathTime_strictMono hab).injective]
  rfl

theorem interiorToll_affine (γ : C(PathTime, X)) (m : X → ℝ≥0∞)
    {a b : PathTime} (hab : a < b) :
    timeToll (affineRestrictedPath a b γ) (Ioo (⊥ : PathTime) ⊤) m =
      timeToll γ (Ioo a b) m := by
  have he := (affinePathTime a b).continuous.image_Ioo_of_strictMono
    (affinePathTime_strictMono hab) (a := ⊥) (b := ⊤)
  rw [affinePathTime_zero, affinePathTime_one] at he
  rw [← he, timeToll_image γ _ (affinePathTime_strictMono hab).injective]
  rfl

theorem sum_restricted_preterminalToll_le {ι : Type*} (γ : C(PathTime, X))
    (m : X → ℝ≥0∞) (a b : ι → PathTime) (hab : ∀ i, a i < b i)
    (hdis : Pairwise (Disjoint on (fun i => Ico (a i) (b i)))) :
    (∑' i, preterminalToll (affineRestrictedPath (a i) (b i) γ) m) ≤ preterminalToll γ m := by
  simp_rw [preterminalToll_affine γ m (hab _)]
  rw [← timeToll_iUnion γ m _ hdis, preterminalToll_eq_timeToll]
  apply timeToll_mono
  intro t ht
  obtain ⟨i, hi⟩ := mem_iUnion.mp ht
  exact lt_of_lt_of_le hi.2 le_top

end CircleDomainRigidity

end

end OAI
