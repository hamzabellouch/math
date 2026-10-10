import Mathlib
import OAI.Geometry.IntegralFillings.Currents.IntegralPush
import OAI.Geometry.IntegralFillings.Optimality.Calibration

namespace OAI

section

open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal

namespace SharpIntegralFillings.Optimality
open CurrentOperations

lemma integral_boundary {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
    {k : ℕ} {T : Functional X (k+1)} (hT : IsIntegral (k+1) T) :
    IsIntegral k (boundarySucc T) := by
  cases k with
  | zero => exact ⟨hT.2.2.1,hT.2.2.2⟩
  | succ k =>
    refine ⟨hT.2.2.1,hT.2.2.2,?_,?_⟩
    · rw [Foundations.boundarySucc_boundarySucc hT.1]
      exact isMetricCurrent_zero _
    · rw [Foundations.boundarySucc_boundarySucc hT.1]
      exact integerRectifiable_zero _

lemma boundary_isCycle {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
    {k : ℕ} {T : Functional X (k+1)} (hT : IsMetricCurrent T) :
    IsCycle (boundarySucc T) := by
  cases k with
  | zero => rfl
  | succ k => exact Foundations.boundarySucc_boundarySucc hT

lemma push_compactlySupported {X Y : Type*} [MetricSpace X] [MeasurableSpace X]
    [BorelSpace X] [CompactSpace X] [MetricSpace Y] [MeasurableSpace Y] [BorelSpace Y]
    {k : ℕ} {T : Functional X k} (hT : IsMetricCurrent T) {f : X → Y} {L : ℝ≥0}
    (hf : LipschitzWith L f) : CompactlySupported (pushCurrent f T) := by
  refine ⟨range f, isCompact_range hf.continuous, ?_⟩
  intro b π had hb
  rw [pushCurrent_apply f T had]
  have he : b ∘ f = fun _ => 0 := funext fun x => hb (f x) ⟨x,rfl⟩
  rw [he]
  have h0 := hT.linearFirst (fun _ => 0) (fun _ => 0) (fun i => π i ∘ f) 0 0
    (BoundedLip.const 0) (BoundedLip.const 0) (admissible_comp had hf).2
  simpa only [zero_mul,add_zero] using h0

noncomputable def clippedCoord {d : ℕ} (i : Fin d) (x : Euc d) : ℝ :=
  max (-1) (min 1 (ambientCoord i x))

lemma clippedCoord_lipschitz {d : ℕ} (i : Fin d) : LipschitzWith 1 (clippedCoord i) :=
  ((ambientCoord_lipschitz i).const_min 1).const_max (-1)

lemma clippedCoord_abs_le {d : ℕ} (i : Fin d) (x : Euc d) : |clippedCoord i x| ≤ 1 := by
  rw [abs_le]
  exact ⟨le_max_left _ _,max_le (by norm_num) (min_le_left _ _)⟩

lemma clippedCoord_boundedLip {d : ℕ} (i : Fin d) : BoundedLip (clippedCoord i) :=
  ⟨⟨1,clippedCoord_lipschitz i⟩,1,clippedCoord_abs_le i⟩

lemma clippedCoord_on_unitBall {d : ℕ} (i : Fin d) (x : UnitBall d) :
    clippedCoord i x.val = unitCoord i x := by
  have hx := abs_le.mp (unitCoord_bound i x)
  change max (-1) (min 1 (unitCoord i x)) = unitCoord i x
  rw [min_eq_right hx.2,max_eq_right hx.1]

noncomputable def ambientBall (d : ℕ) (t : ℝ) : Functional (Euc d) d :=
  pushCurrent (fun x : UnitBall d => x.val) (innerBallCurrent d t)

lemma inclusion_lipschitz (d : ℕ) : LipschitzWith 1 (fun x : UnitBall d => x.val) :=
  LipschitzWith.subtype_val _

lemma ambientBall_integral {d : ℕ} {t : ℝ}
    (hT : IsIntegral d (innerBallCurrent d t)) : IsIntegral d (ambientBall d t) :=
  integral_push_of_bilipschitz hT (inclusion_lipschitz d) isometry_subtype_coe.antilipschitzWith

lemma ambientBall_metric (d : ℕ) (t : ℝ) : IsMetricCurrent (ambientBall d t) :=
  pushCurrent_isMetricCurrent (innerBallCurrent_metric d t) (inclusion_lipschitz d)

lemma ambientBall_boundary_mass_le (n : ℕ) (t : ℝ)
    (hT : IsMetricCurrent (boundarySucc (innerBallCurrent (n+1) t))) :
    mass (boundarySucc (ambientBall (n+1) t)) ≤
      mass (boundarySucc (innerBallCurrent (n+1) t)) := by
  rw [ambientBall, pushCurrent_boundarySucc _ (inclusion_lipschitz (n+1))]
  simpa only [NNReal.coe_one,one_pow,one_mul] using
    mass_pushCurrent_le hT (inclusion_lipschitz (n+1))

lemma ambientBall_boundary_compact (n : ℕ) (t : ℝ)
    (hT : IsMetricCurrent (boundarySucc (innerBallCurrent (n+1) t))) :
    CompactlySupported (boundarySucc (ambientBall (n+1) t)) := by
  rw [ambientBall, pushCurrent_boundarySucc _ (inclusion_lipschitz (n+1))]
  exact push_compactlySupported hT (inclusion_lipschitz (n+1))

lemma ambientBall_boundary_coords (n : ℕ) {t : ℝ} (ht : -1 < t) :
    boundarySucc (ambientBall (n+1) t) (clippedCoord 0) (fun i => ambientCoord i.succ) =
      (volume (Metric.ball (0 : Euc (n+1)) (-t))).toReal := by
  have had : Admissible (clippedCoord (0 : Fin (n+1))) (fun i => ambientCoord i.succ) :=
    ⟨clippedCoord_boundedLip 0,fun i => ⟨1,ambientCoord_lipschitz i.succ⟩⟩
  rw [boundarySucc,ite_eq_left had,ambientBall,
    pushCurrent_apply _ _ (Foundations.admissible_vecCons (BoundedLip.const 1) had.1.1 had.2)]
  have he : (fun i => Matrix.vecCons (clippedCoord (0 : Fin (n+1)))
        (fun j => ambientCoord j.succ) i ∘ (fun x : UnitBall (n+1) => x.val)) = unitCoord := by
    funext i x
    induction i using Fin.cases with
    | zero => exact clippedCoord_on_unitBall 0 x
    | succ i => rfl
  rw [he]
  exact innerBallCurrent_coords (n+1) ht

lemma allFillings_mass_ge_ball (n : ℕ) {t : ℝ} (ht : -1 < t)
    {S : Functional (Euc (n+1)) (n+1)} (hS : IsMetricCurrent S)
    (hb : boundarySucc S = boundarySucc (ambientBall (n+1) t)) :
    (volume (Metric.ball (0 : Euc (n+1)) (-t))).toReal ≤ mass S := by
  have he := congrArg (fun U : Functional (Euc (n+1)) n =>
    U (clippedCoord 0) (fun i => ambientCoord i.succ)) hb
  rw [ambientBall_boundary_coords n ht] at he
  have had : Admissible (clippedCoord (0 : Fin (n+1))) (fun i => ambientCoord i.succ) :=
    ⟨clippedCoord_boundedLip 0,fun i => ⟨1,ambientCoord_lipschitz i.succ⟩⟩
  rw [boundarySucc,ite_eq_left had] at he
  rw [← he]
  apply (le_abs_self _).trans
  apply abs_apply_le_mass hS (BoundedLip.const 1) (fun _ => by norm_num)
  intro i
  induction i using Fin.cases with
  | zero => exact clippedCoord_lipschitz 0
  | succ i => exact ambientCoord_lipschitz i.succ

lemma ambientBall_boundary_mass_pos (n : ℕ) {t : ℝ} (ht : t ∈ Ioo (-1:ℝ) 0)
    (hT : IsMetricCurrent (boundarySucc (ambientBall (n+1) t))) :
    0 < mass (boundarySucc (ambientBall (n+1) t)) := by
  have htest := abs_apply_le_mass hT (clippedCoord_boundedLip (0 : Fin (n+1)))
    (clippedCoord_abs_le 0) (fun i => ambientCoord_lipschitz i.succ)
  rw [ambientBall_boundary_coords n ht.1,abs_of_nonneg ENNReal.toReal_nonneg,
    ball_volume_scaling (n+1) (neg_pos.mpr ht.2)] at htest
  exact (mul_pos (omega_pos (n+1)) (pow_pos (neg_pos.mpr ht.2) _)).trans_le htest

end SharpIntegralFillings.Optimality

end

end OAI
