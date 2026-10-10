import OAI.Combinatorics.BalancedRyser.Selection.SelectionHistoryInvariant

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped MeasureTheory ProbabilityTheory BigOperators

namespace Balanced.Selection.Process

attribute [local instance] Classical.propDecidable
variable {I V : Type*} [Fintype I] [Fintype V]

theorem integrable_stateObservable (p : Parameters) (q : ℕ) (G : Input I V)
    (t : ℕ) (f : Option (State I V) → ℝ) :
    Integrable (fun ω => f (ω t).1) (snapshotPathLaw p q G) := by
  have hi : Integrable (fun s : Snapshot I V => f s.1)
      ((snapshotPathLaw p q G).map (fun ω => ω t)) := .of_finite
  exact hi.comp_measurable (measurable_pi_apply t)

theorem sum_snapshotWeight_stateObservable (p : Parameters) (q t : ℕ)
    (G : Input I V) (before : Snapshot I V) (f : Option (State I V) → ℝ) :
    (∑ out, snapshotWeight p q t G before out * f out.1) =
      ∑ out, transitionWeight p q t G before.1 out * f out := by
  simp only [Snapshot, Fintype.sum_prod_type]
  simp_rw [← Finset.sum_mul, sum_snapshotWeight_state]

theorem integral_stateObservable_eq_historyWeight (p : Parameters) (q : ℕ)
    (G : Input I V) (t : ℕ) (f : Option (State I V) → ℝ) :
    (∫ ω, f (ω t).1 ∂snapshotPathLaw p q G) =
      ∑ out, historyWeight p q G t out * f out := by
  induction t generalizing f with
  | zero =>
    have hi := FiniteHistory.ae_initial_state
      (fun t => snapshotPMF p q t G) (initialSnapshot (I := I) (V := V))
    have heq : (fun ω => f (ω 0).1) =ᵐ[snapshotPathLaw p q G]
        fun _ => f (some initialState) := by
      filter_upwards [hi] with ω hω
      simp only [hω, initialSnapshot]
    rw [integral_congr_ae heq]
    simp [historyWeight]
  | succ t ih =>
    have hce := condExp_snapshot_step p q G t (fun _ out => f out.1)
    have hce' : (snapshotPathLaw p q G)[
        (fun ω => f (ω (t + 1)).1) | snapshotFiltration t]
        =ᵐ[snapshotPathLaw p q G]
        fun ω => ∑ out, transitionWeight p q t G (ω t).1 out * f out := by
      change (snapshotPathLaw p q G)[
        (fun ω => f (ω (t + 1)).1) | snapshotFiltration t] =ᵐ[snapshotPathLaw p q G] _ at hce
      simpa only [sum_snapshotWeight_stateObservable] using hce
    calc
      (∫ ω, f (ω (t + 1)).1 ∂snapshotPathLaw p q G) =
          ∫ ω, ((snapshotPathLaw p q G)[
            (fun ω => f (ω (t + 1)).1) | snapshotFiltration t]) ω
              ∂snapshotPathLaw p q G :=
        (integral_condExp (snapshotFiltration.le t)).symm
      _ = ∫ ω, (∑ out, transitionWeight p q t G (ω t).1 out * f out)
          ∂snapshotPathLaw p q G := integral_congr_ae hce'
      _ = ∑ out, ∫ ω, transitionWeight p q t G (ω t).1 out * f out
          ∂snapshotPathLaw p q G :=
        integral_finsetSum _ (fun out _ =>
          integrable_stateObservable p q G t (fun s => transitionWeight p q t G s out * f out))
      _ = ∑ out, ∑ before, historyWeight p q G t before *
          (transitionWeight p q t G before out * f out) := by
        apply Finset.sum_congr rfl
        intro out _
        exact ih (fun before => transitionWeight p q t G before out * f out)
      _ = ∑ out, historyWeight p q G (t + 1) out * f out := by
        simp only [historyWeight, Finset.sum_mul, mul_assoc]

theorem state_event_real_eq_historyWeight (p : Parameters) (q : ℕ)
    (G : Input I V) (t : ℕ) (A : Set (Option (State I V))) :
    (snapshotPathLaw p q G).real {ω | (ω t).1 ∈ A} =
      ∑ out, if out ∈ A then historyWeight p q G t out else 0 := by
  have hm : MeasurableSet {ω : FiniteHistory.Path (Snapshot I V) | (ω t).1 ∈ A} :=
    (show MeasurableSet {s : Snapshot I V | s.1 ∈ A} from .of_discrete).preimage
      (measurable_pi_apply t)
  rw [← integral_indicator_one hm]
  have h := integral_stateObservable_eq_historyWeight p q G t
    (fun out => if out ∈ A then 1 else 0)
  simpa only [Set.indicator_apply, Set.mem_ofPred_eq, Pi.one_apply, mul_ite,
    mul_one, mul_zero] using h

theorem map_state_snapshotPathLaw
    [MeasurableSpace (Option (State I V))]
    [MeasurableSingletonClass (Option (State I V))]
    (p : Parameters) (q : ℕ) (G : Input I V) (t : ℕ) :
    (snapshotPathLaw p q G).map (fun ω => (ω t).1) =
      (historyPMF p q G t).toMeasure := by
  apply Measure.ext_of_singleton
  intro out
  have hm : Measurable (fun ω : FiniteHistory.Path (Snapshot I V) => (ω t).1) :=
    (measurable_of_countable (fun s : Snapshot I V => s.1)).comp (measurable_pi_apply t)
  apply (ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _) (measure_ne_top _ _)).1
  rw [Measure.map_apply hm (measurableSet_singleton out),
    PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton out), historyPMF_apply_real]
  change (snapshotPathLaw p q G).real {ω | (ω t).1 ∈ ({out} : Set (Option (State I V)))} = _
  rw [state_event_real_eq_historyWeight]
  simp

end Balanced.Selection.Process

end

end OAI
