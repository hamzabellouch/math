import OAI.Analysis.IrrationalRotation.Model.BlockedProductCoupling
import OAI.Analysis.IrrationalRotation.Analysis.ConcreteTagEvent

namespace OAI

open MeasureTheory Set
open scoped ENNReal

namespace Invariant233.BlockedProductCoupling

open OneCoordinateCoupling

variable {m : ℕ → ℕ} {κ : ℕ → ℝ}
  {a b : (s : ℕ) → Fin (m s) → ℝ}
  (hm : ∀ s, 100 ≤ m s) (hκ0 : ∀ s, 0 ≤ κ s) (hκ : ∀ s, κ s ≤ 1 / 100)
  (ha : ∀ s i, 1 / (m s : ℝ) ≤ a s i) (ha' : ∀ s i, a s i ≤ 1 / 4)
  (hb : ∀ s i, 1 / (m s : ℝ) ≤ b s i) (hb' : ∀ s i, b s i ≤ 1 / 4)

include hm hκ0 hκ ha ha' hb hb'

theorem coordinate_isProbabilityMeasure (j s : ℕ) (i : Fin (m s)) :
    IsProbabilityMeasure (labelledLaw (κ s) (m s) (a s i) (b s i)
      (if s = j then 1 else 0)) := by
  apply labelledLaw_isProbabilityMeasure (hκ0 s) (hκ s)
    (by exact_mod_cast hm s) (ha s i) (ha' s i) (hb s i) (hb' s i)
  all_goals split_ifs <;> norm_num

theorem blockLaw_isProbabilityMeasure (j s : ℕ) :
    IsProbabilityMeasure (blockLaw m κ a b j s) := by
  have := coordinate_isProbabilityMeasure hm hκ0 hκ ha ha' hb hb' j s
  unfold blockLaw
  infer_instance

theorem law_isProbabilityMeasure (j : ℕ) :
    IsProbabilityMeasure (law m κ a b j) := by
  have := blockLaw_isProbabilityMeasure hm hκ0 hκ ha ha' hb hb' j
  unfold law
  infer_instance

theorem law_map_block (j s : ℕ) :
    (law m κ a b j).map (fun z => z s) = blockLaw m κ a b j s := by
  have := blockLaw_isProbabilityMeasure hm hκ0 hκ ha ha' hb hb' j
  exact Measure.infinitePi_map_eval _ s

theorem law_map_coordinate (j s : ℕ) (i : Fin (m s)) :
    (law m κ a b j).map (fun z => z s i) =
      labelledLaw (κ s) (m s) (a s i) (b s i) (if s = j then 1 else 0) := by
  have := coordinate_isProbabilityMeasure hm hκ0 hκ ha ha' hb hb' j s
  change (law m κ a b j).map ((fun z => z i) ∘ (fun z => z s)) = _
  rw [← Measure.map_map (measurable_pi_apply i) (measurable_pi_apply s),
    law_map_block hm hκ0 hκ ha ha' hb hb']
  exact (measurePreserving_eval _ i).map_eq

theorem currentEvent_mass (j : ℕ) :
    Real.exp (-82) ≤ (law m κ a b j).real (currentEvent m j) := by
  let E : Set (Fin (m j) → Coordinate) :=
    {z | (∃ i, (z i).1 = some (4 : Fin 5)) ∧
      ∀ i, (z i).2.1 < 1 - 2 / (m j : ℝ) ∧ 2 / (m j : ℝ) < (z i).2.2}
  have hE : MeasurableSet E := by
    change MeasurableSet ({z : Fin (m j) → Coordinate | ∃ i, (z i).1 = some (4 : Fin 5)} ∩
      {z | ∀ i, (z i).2.1 < 1 - 2 / (m j : ℝ) ∧ 2 / (m j : ℝ) < (z i).2.2})
    rw [Set.ofPred_exists, Set.ofPred_forall]
    apply MeasurableSet.inter
    ·
      apply MeasurableSet.iUnion
      intro i
      exact (measurable_fst.comp (measurable_pi_apply i)) (measurableSet_singleton _)
    ·
      apply MeasurableSet.iInter
      intro i
      have hx : Measurable (fun z : Fin (m j) → Coordinate => (z i).2.1) := by fun_prop
      have hy : Measurable (fun z : Fin (m j) → Coordinate => (z i).2.2) := by fun_prop
      exact (measurableSet_lt hx measurable_const).inter
        (measurableSet_lt measurable_const hy)
  have heq : (law m κ a b j).real (currentEvent m j) =
      (blockLaw m κ a b j j).real E := by
    rw [← law_map_block hm hκ0 hκ ha ha' hb hb' j j,
      map_measureReal_apply (measurable_pi_apply j) hE]
    rfl
  rw [heq]
  simpa only [blockLaw, ite_true, E] using
    concrete_product_currentBlock_mass (m j) (hm j) (κ j) (hκ0 j) (hκ j)
      (a j) (b j) (ha j) (ha' j) (hb j) (hb' j)

theorem law_map_uncurry (j : ℕ) :
    (law m κ a b j).map (fun z (p : Σ s, Fin (m s)) => z p.1 p.2) =
      Measure.infinitePi (fun p : Σ s, Fin (m s) =>
        labelledLaw (κ p.1) (m p.1) (a p.1 p.2) (b p.1 p.2)
          (if p.1 = j then 1 else 0)) := by
  have := coordinate_isProbabilityMeasure hm hκ0 hκ ha ha' hb hb' j
  unfold law blockLaw
  have h := Measure.infinitePi_map_piCurry_symm
    (fun s i => labelledLaw (κ s) (m s) (a s i) (b s i)
      (if s = j then 1 else 0))
  simp only [Measure.infinitePi_eq_pi] at h
  convert h using 1
  congr 1

theorem law_left_marginal_le_ten (j s : ℕ) (i : Fin (m s)) :
    (law m κ a b j).map (fun z => (z s i).2.1) ≤
      (10 : ℝ≥0∞) • volume.restrict (Ico (0 : ℝ) 1) := by
  change (law m κ a b j).map ((Prod.fst ∘ Prod.snd) ∘
    (fun z => z s i)) ≤ _
  rw [← Measure.map_map (measurable_fst.comp measurable_snd)
      ((measurable_pi_apply i).comp (measurable_pi_apply s)),
    law_map_coordinate hm hκ0 hκ ha ha' hb hb']
  change (labelledLaw (κ s) (m s) (a s i) (b s i) _).map
    (fun z => z.2.1) ≤ _
  rw [labelledLaw_left_map, ← baseLaw_eq_restrict]
  apply pairLaw_fst_le_ten (hκ0 s) (hκ s) (by exact_mod_cast hm s)
    (ha s i) (ha' s i) (hb s i) (hb' s i)
  all_goals split_ifs <;> norm_num

theorem law_right_marginal_le_ten (j s : ℕ) (i : Fin (m s)) :
    (law m κ a b j).map (fun z => (z s i).2.2) ≤
      (10 : ℝ≥0∞) • volume.restrict (Ico (0 : ℝ) 1) := by
  change (law m κ a b j).map ((Prod.snd ∘ Prod.snd) ∘
    (fun z => z s i)) ≤ _
  rw [← Measure.map_map (measurable_snd.comp measurable_snd)
      ((measurable_pi_apply i).comp (measurable_pi_apply s)),
    law_map_coordinate hm hκ0 hκ ha ha' hb hb']
  change (labelledLaw (κ s) (m s) (a s i) (b s i) _).map
    (fun z => z.2.2) ≤ _
  rw [labelledLaw_right_map, ← baseLaw_eq_restrict]
  apply pairLaw_snd_le_ten (hκ0 s) (hκ s) (by exact_mod_cast hm s)
    (ha s i) (ha' s i) (hb s i) (hb' s i)
  all_goals split_ifs <;> norm_num

theorem futureBad_mass_le {K : ℕ → ℝ} (hK : ∀ s, 0 < K s)
    (j : ℕ) (hsum : Summable (fun n : ℕ => 1 / K (j + 1 + n))) :
    (law m κ a b j).real (futureBad m K j) ≤
      40 * K j * ∑' n : ℕ, 1 / K (j + 1 + n) := by
  have := law_isProbabilityMeasure hm hκ0 hκ ha ha' hb hb' j
  have h := InvariantRotation.EndpointIntervalBounds.blocked_future_endpoint_loss_le
    (law m κ a b j) (fun n => m (j + 1 + n)) (fun n => by have := hm (j + 1 + n); omega)
    (K := fun n => K (j + 1 + n)) (fun n => hK _) hsum
    (X := fun n i z => (z (j + 1 + n) i).2.1)
    (Y := fun n i z => (z (j + 1 + n) i).2.2)
    (by intros; fun_prop) (by intros; fun_prop)
    (C := 10) (a := 2) (W := K j) (by norm_num) (by norm_num) (hK j).le
    (fun n i => by simpa using law_left_marginal_le_ten hm hκ0 hκ ha ha' hb hb' j _ i)
    (fun n i => by simpa using law_right_marginal_le_ten hm hκ0 hκ ha ha' hb hb' j _ i)
  norm_num only [show (2 : ℝ) * 10 * 2 = 40 by norm_num] at h
  exact h

end Invariant233.BlockedProductCoupling

end OAI
