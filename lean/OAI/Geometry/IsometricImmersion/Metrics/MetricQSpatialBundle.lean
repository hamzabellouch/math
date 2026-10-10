import OAI.Geometry.IsometricImmersion.Metrics.UniversalMetricQ

namespace OAI

noncomputable section
open Set Filter Function
open scoped ContDiff Topology BigOperators Matrix Matrix.Norms.Elementwise

namespace SmoothLocal.HighEquation
open SmoothLocal.Geometry SmoothLocal.Weighted SmoothLocal.ODE SmoothLocal.Hyperbolic

def HorizontalMetricTwoJetBound (g : MetricField) (p : Coord) (N : ℕ) (G : ℝ) : Prop :=
  (∀ i j n, n ≤ N → |horizontalJet (fun x => g x i j) n p| ≤ G) ∧
  (∀ d i j n, n ≤ N → |horizontalJet (coordPartial d (fun x => g x i j)) n p| ≤ G) ∧
  (∀ d e i j n, n ≤ N →
    |horizontalJet (coordPartial d (coordPartial e (fun x => g x i j))) n p| ≤ G)

def qFixedTimeBaseDomain (U : Set Coord) (theta : ℝ) : Set QSpatialState :=
  {v | coordinatePoint (v 0) theta ∈ U}

def metricQSpatialBundle (g : MetricField) (theta : ℝ) : QSpatialState → MetricPInput :=
  metricPBundle g ∘ qFixedTimeState theta

theorem statePoint_qFixedTimeState (theta : ℝ) (v : QSpatialState) :
    statePoint (qFixedTimeState theta v) = coordinatePoint (v 0) theta := by
  ext i
  fin_cases i <;> simp [statePoint, qFixedTimeState, qSpatialCLM, qSpatialLinear,
    coordinatePoint]

theorem qFixedTimeBaseDomain_isOpen {U : Set Coord} (hU : IsOpen U) (theta : ℝ) :
    IsOpen (qFixedTimeBaseDomain U theta) :=
  hU.preimage (by unfold coordinatePoint; fun_prop)

theorem metricQSpatialBundle_contDiffOn {g : MetricField} {U : Set Coord}
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) (theta : ℝ) :
    ContDiffOn ℝ ∞ (metricQSpatialBundle g theta) (qFixedTimeBaseDomain U theta) := by
  apply (metricPBundle_contDiffOn hg hU).comp (qFixedTimeState_contDiff theta).contDiffOn
  intro v hv
  change statePoint (qFixedTimeState theta v) ∈ U
  simpa only [statePoint_qFixedTimeState, qFixedTimeBaseDomain, Set.mem_ofPred_eq] using hv

theorem norm_iteratedFDeriv_fixedTime_coordinate
    {f : Coord → ℝ} {U : Set Coord} (hf : ContDiffOn ℝ ∞ f U) (hU : IsOpen U)
    {theta : ℝ} {v : QSpatialState} (hp : coordinatePoint (v 0) theta ∈ U) (n : ℕ) :
    ‖iteratedFDeriv ℝ n (fun w : QSpatialState => f (coordinatePoint (w 0) theta)) v‖ ≤
      |horizontalJet f n (coordinatePoint (v 0) theta)| := by
  let I : Set ℝ := {x | coordinatePoint x theta ∈ U}
  let L : QSpatialState →L[ℝ] ℝ := ContinuousLinearMap.proj 0
  have hI : IsOpen I := hU.preimage (horizontalPoint_contDiff theta).continuous
  have hs : ContDiffOn ℝ ∞ (fun x : ℝ => f (coordinatePoint x theta)) I :=
    hf.comp (horizontalPoint_contDiff theta).contDiffOn (fun x hx => hx)
  have hL : ‖L‖ ≤ 1 := by
    apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    intro w
    simpa only [one_mul, L, ContinuousLinearMap.proj_apply] using norm_le_pi_norm w 0
  have h := norm_iteratedFDeriv_comp_contraction L hs hI hL hp n
  rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv] at h
  change ‖iteratedFDeriv ℝ n (fun w : QSpatialState => f (coordinatePoint (w 0) theta)) v‖ ≤
    ‖iteratedDeriv n (fun x => f (coordinatePoint x theta)) (v 0)‖ at h
  rw [horizontalJet_slice hU hf theta n (v 0) hp, Real.norm_eq_abs] at h
  exact h

theorem qSpatialCLM_norm_le : ‖qSpatialCLM‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro v
  rw [one_mul]
  apply (pi_norm_le_iff_of_nonneg (norm_nonneg v)).mpr
  intro i
  fin_cases i
  · exact norm_le_pi_norm v 0
  · simp [qSpatialCLM, qSpatialLinear]
  · exact norm_le_pi_norm v 1
  · exact norm_le_pi_norm v 2
  · exact norm_le_pi_norm v 3
  · exact norm_le_pi_norm v 4

theorem qFixedTimeState_positive_jet_bound (theta : ℝ) (v : QSpatialState)
    {n : ℕ} (hn : 1 ≤ n) : ‖iteratedFDeriv ℝ n (qFixedTimeState theta) v‖ ≤ 1 := by
  cases n with
  | zero => omega
  | succ n =>
      rw [← norm_iteratedFDeriv_fderiv]
      have he : fderiv ℝ (qFixedTimeState theta) = (fun _ : QSpatialState => qSpatialCLM) := by
        funext w
        exact (qSpatialCLM.hasFDerivAt.add_const (Pi.single 1 theta)).fderiv
      rw [he]
      cases n with
      | zero => simpa only [norm_iteratedFDeriv_zero] using qSpatialCLM_norm_le
      | succ _ => simp only [iteratedFDeriv_succ_const]; norm_num

theorem metricQSpatialBundle_norm_bound
    {g : MetricField} {theta G W : ℝ} {v : QSpatialState} {N : ℕ}
    (hG : 0 ≤ G) (hgB : HorizontalMetricTwoJetBound g (coordinatePoint (v 0) theta) N G)
    (hwB : ‖qFixedTimeState theta v‖ ≤ W) :
    ‖metricQSpatialBundle g theta v‖ ≤ max G W := by
  have h0 : ‖g (coordinatePoint (v 0) theta)‖ ≤ G :=
    (pi_norm_le_iff_of_nonneg hG).mpr (fun i =>
      (pi_norm_le_iff_of_nonneg hG).mpr (fun j => hgB.1 i j 0 (by omega)))
  have h1 : ‖(fun d i j => coordPartial d (fun p => g p i j) (coordinatePoint (v 0) theta))‖ ≤ G :=
    (pi_norm_le_iff_of_nonneg hG).mpr (fun d =>
      (pi_norm_le_iff_of_nonneg hG).mpr (fun i =>
        (pi_norm_le_iff_of_nonneg hG).mpr (fun j => hgB.2.1 d i j 0 (by omega))))
  have h2 : ‖(fun d e i j => coordPartial d (coordPartial e (fun p => g p i j))
      (coordinatePoint (v 0) theta))‖ ≤ G :=
    (pi_norm_le_iff_of_nonneg hG).mpr (fun d =>
      (pi_norm_le_iff_of_nonneg hG).mpr (fun e =>
        (pi_norm_le_iff_of_nonneg hG).mpr (fun i =>
          (pi_norm_le_iff_of_nonneg hG).mpr (fun j => hgB.2.2 d e i j 0 (by omega)))))
  unfold metricQSpatialBundle metricPBundle
  simp only [Function.comp_apply, statePoint_qFixedTimeState, Prod.norm_def]
  exact max_le (h0.trans (le_max_left _ _))
    (max_le (h1.trans (le_max_left _ _))
      (max_le (h2.trans (le_max_left _ _)) (hwB.trans (le_max_right _ _))))

theorem metricQSpatialBundle_positive_jet_bound
    {g : MetricField} {U : Set Coord} {theta G : ℝ} {v : QSpatialState} {N : ℕ}
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) (hp : coordinatePoint (v 0) theta ∈ U)
    (hG : 0 ≤ G) (hgB : HorizontalMetricTwoJetBound g (coordinatePoint (v 0) theta) N G)
    {n : ℕ} (hn : 1 ≤ n) (hnN : n ≤ N) :
    ‖iteratedFDeriv ℝ n (metricQSpatialBundle g theta) v‖ ≤ max 1 G := by
  have hB := (metricQSpatialBundle_contDiffOn hg hU theta).contDiffAt
    ((qFixedTimeBaseDomain_isOpen hU theta).mem_nhds hp)
  have h0 := hB.fst
  have h1 := hB.snd.fst
  have h2 := hB.snd.snd.fst
  have hId := hB.snd.snd.snd
  change ContDiffAt ℝ ∞ (fun w : QSpatialState => (metricQSpatialBundle g theta w).1) v at h0
  change ContDiffAt ℝ ∞ (fun w : QSpatialState => (metricQSpatialBundle g theta w).2.1) v at h1
  change ContDiffAt ℝ ∞ (fun w : QSpatialState => (metricQSpatialBundle g theta w).2.2.1) v at h2
  have he0 : (fun w : QSpatialState => (metricQSpatialBundle g theta w).1) =
      (fun w => g (coordinatePoint (w 0) theta)) := by
    funext w
    exact congrArg g (statePoint_qFixedTimeState theta w)
  have he1 : (fun w : QSpatialState => (metricQSpatialBundle g theta w).2.1) =
      (fun w d i j => coordPartial d (fun p => g p i j) (coordinatePoint (w 0) theta)) := by
    funext w d i j
    exact congrArg (coordPartial d (fun p => g p i j)) (statePoint_qFixedTimeState theta w)
  have he2 : (fun w : QSpatialState => (metricQSpatialBundle g theta w).2.2.1) =
      (fun w d e i j => coordPartial d (coordPartial e (fun p => g p i j)) (coordinatePoint (w 0) theta)) := by
    funext w d e i j
    exact congrArg (coordPartial d (coordPartial e (fun p => g p i j))) (statePoint_qFixedTimeState theta w)
  rw [he0] at h0
  rw [he1] at h1
  rw [he2] at h2
  have hb0 : ‖iteratedFDeriv ℝ n (fun w : QSpatialState => g (coordinatePoint (w 0) theta)) v‖ ≤ G := by
    apply norm_iteratedFDeriv_pi_le h0 n hG
    intro i
    apply norm_iteratedFDeriv_pi_le ((contDiffAt_pi.mp h0) i) n hG
    intro j
    exact (norm_iteratedFDeriv_fixedTime_coordinate (hg.1 i j) hU hp n).trans (hgB.1 i j n hnN)
  have hb1 : ‖iteratedFDeriv ℝ n
      (fun w : QSpatialState => fun d i j => coordPartial d (fun p => g p i j) (coordinatePoint (w 0) theta)) v‖ ≤ G := by
    apply norm_iteratedFDeriv_pi_le (F := Matrix (Fin 2) (Fin 2) ℝ) h1 n hG
    intro d
    have h1d := (contDiffAt_pi (F' := fun _ : Fin 2 => Matrix (Fin 2) (Fin 2) ℝ)).mp h1 d
    apply norm_iteratedFDeriv_pi_le h1d n hG
    intro i
    apply norm_iteratedFDeriv_pi_le ((contDiffAt_pi.mp h1d) i) n hG
    intro j
    exact (norm_iteratedFDeriv_fixedTime_coordinate (partial_contDiffOn (hg.1 i j) hU d) hU hp n).trans
      (hgB.2.1 d i j n hnN)
  have hb2 : ‖iteratedFDeriv ℝ n
      (fun w : QSpatialState => fun d e i j => coordPartial d (coordPartial e (fun p => g p i j))
        (coordinatePoint (w 0) theta)) v‖ ≤ G := by
    apply norm_iteratedFDeriv_pi_le (F := Fin 2 → Matrix (Fin 2) (Fin 2) ℝ) h2 n hG
    intro d
    have h2d := (contDiffAt_pi (F' := fun _ : Fin 2 => Fin 2 → Matrix (Fin 2) (Fin 2) ℝ)).mp h2 d
    apply norm_iteratedFDeriv_pi_le (F := Matrix (Fin 2) (Fin 2) ℝ) h2d n hG
    intro e
    have h2de := (contDiffAt_pi (F' := fun _ : Fin 2 => Matrix (Fin 2) (Fin 2) ℝ)).mp h2d e
    apply norm_iteratedFDeriv_pi_le h2de n hG
    intro i
    apply norm_iteratedFDeriv_pi_le ((contDiffAt_pi.mp h2de) i) n hG
    intro j
    exact (norm_iteratedFDeriv_fixedTime_coordinate
      (partial_contDiffOn (partial_contDiffOn (hg.1 i j) hU e) hU d) hU hp n).trans
        (hgB.2.2 d e i j n hnN)
  have hb0' : ‖iteratedFDeriv ℝ n (fun w => (metricQSpatialBundle g theta w).1) v‖ ≤ G := by
    rw [he0]
    exact hb0
  have hb1' : ‖iteratedFDeriv ℝ n (fun w => (metricQSpatialBundle g theta w).2.1) v‖ ≤ G := by
    rw [he1]
    exact hb1
  have hb2' : ‖iteratedFDeriv ℝ n (fun w => (metricQSpatialBundle g theta w).2.2.1) v‖ ≤ G := by
    rw [he2]
    exact hb2
  exact norm_iteratedFDeriv_prod_le hB.fst hB.snd n (hb0'.trans (le_max_right _ _))
    (norm_iteratedFDeriv_prod_le hB.snd.fst hB.snd.snd n (hb1'.trans (le_max_right _ _))
      (norm_iteratedFDeriv_prod_le hB.snd.snd.fst hId n (hb2'.trans (le_max_right _ _))
        ((qFixedTimeState_positive_jet_bound theta v hn).trans (le_max_left _ _))))

end SmoothLocal.HighEquation

end

end OAI
