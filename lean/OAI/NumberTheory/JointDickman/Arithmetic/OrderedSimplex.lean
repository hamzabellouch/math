import OAI.NumberTheory.JointDickman.Arithmetic.OrderedPrimeBoundary
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Order.Fin.Tuple

namespace OAI

/-! # Removing the least coordinate from an ordered simplex -/
namespace JointDickman
open Finset MeasureTheory
open scoped ENNReal

noncomputable def orderedTupleRegion (n : ℕ) (u : ℝ) : Set (Fin n → ℝ) :=
  {t | StrictMono t} ∩ {t | ∑ i, t i ≤ u}

theorem orderedTupleRegion_measurable (n : ℕ) (u : ℝ) :
    MeasurableSet (orderedTupleRegion n u) :=
  (strictMono_isOpen n).measurableSet.inter
    (measurableSet_le (Finset.measurable_sum _ (fun i _ => measurable_pi_apply i)) measurable_const)

theorem orderedTupleRegion_cons (n : ℕ) (s u : ℝ) (t : Fin n → ℝ) :
    Fin.cons s t ∈ orderedTupleRegion (n+1) u ↔
      t ∈ orderedTupleRegion n (u-s) ∩ Set.pi Set.univ (fun _ => Set.Ioi s) := by
  simp only [orderedTupleRegion, Set.mem_inter_iff, Set.mem_ofPred_eq,
    Fin.strictMono_cons, Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ,
    Set.mem_pi, Set.mem_univ, forall_const, Set.mem_Ioi]
  constructor
  · rintro ⟨⟨hmin, hmono⟩, hsum⟩
    exact ⟨⟨hmono, by linarith⟩, hmin⟩
  · rintro ⟨⟨hmono, hsum⟩, hmin⟩
    exact ⟨⟨hmin, hmono⟩, by linarith⟩

noncomputable def orderedSimplexMass (μ : Measure ℝ) (n : ℕ) (u : ℝ) : ℝ :=
  (Measure.pi (fun _ : Fin n => μ)).real (orderedTupleRegion n u)

theorem orderedSimplexMass_succ (μ : Measure ℝ) [IsFiniteMeasure μ]
    (n : ℕ) (u : ℝ) :
    orderedSimplexMass μ (n+1) u =
      ∫ s, orderedSimplexMass (μ.restrict (Set.Ioi s)) n (u-s) ∂μ := by
  let E : Set (ℝ × (Fin n → ℝ)) :=
    (fun z => Fin.cons z.1 z.2) ⁻¹' orderedTupleRegion (n+1) u
  have hcons : Measurable (fun z : ℝ × (Fin n → ℝ) =>
      (Fin.cons z.1 z.2 : Fin (n+1) → ℝ)) := by
    apply Measurable.of_eval
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · exact measurable_fst
    · exact (measurable_pi_apply j).comp measurable_snd
  have hE : MeasurableSet E := (orderedTupleRegion_measurable _ _).preimage hcons
  have he : (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n+1) => ℝ) 0) ⁻¹' E =
      orderedTupleRegion (n+1) u := by
    ext t
    change (Fin.cons (t 0) (fun i : Fin n => t i.succ) : Fin (n+1) → ℝ) ∈ orderedTupleRegion (n+1) u ↔ t ∈ orderedTupleRegion (n+1) u
    have ht : (Fin.cons (t 0) (fun i : Fin n => t i.succ) : Fin (n+1) → ℝ) = t := by
      funext i
      refine Fin.cases ?_ (fun j => ?_) i <;> rfl
    rw [ht]
  unfold orderedSimplexMass
  rw [measureReal_def, ← he,
    (measurePreserving_piFinSuccAbove (fun _ : Fin (n+1) => μ) 0).measure_preimage hE.nullMeasurableSet,
    Measure.prod_apply hE]
  rw [← integral_toReal (measurable_measure_prodMk_left hE).aemeasurable]
  · apply integral_congr_ae
    filter_upwards [] with s
    change ((Measure.pi (fun _ : Fin n => μ)) ((fun t => (s,t)) ⁻¹' E)).toReal = _
    have hs : (fun t => (s,t)) ⁻¹' E =
        orderedTupleRegion n (u-s) ∩ Set.pi Set.univ (fun _ => Set.Ioi s) := by
      ext t
      exact orderedTupleRegion_cons n s u t
    rw [hs, ← Measure.restrict_apply (orderedTupleRegion_measurable _ _), Measure.restrict_pi_pi]
    rfl
  · filter_upwards [] with s
    exact measure_lt_top _ _

end JointDickman

end OAI
