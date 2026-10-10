import OAI.Combinatorics.BalancedRyser.Selection.SelectionAuxiliaryTracks

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter Preorder
open scoped BigOperators

namespace Balanced.Selection.Process
attribute [local instance] Classical.propDecidable
variable {I V : Type*} [Fintype I] [Fintype V]

theorem measurable_snapshot_prefix_response (t : ℕ)
    (f : FiniteHistory.Prefix (Snapshot I V) t → ℝ) :
    Measurable[snapshotFiltration t] (fun ω => f (frestrictLe t ω)) := by
  have hr : Measurable[snapshotFiltration (I := I) (V := V) t] (frestrictLe t) := by
    rw [measurable_iff_comap_le]
    change MeasurableSpace.comap (frestrictLe t) MeasurableSpace.pi ≤
      Filtration.piLE (X := fun _ : ℕ => Snapshot I V) t
    rw [Filtration.piLE_eq_comap_frestrictLe]
  exact (measurable_of_countable f).comp hr

theorem stronglyMeasurable_retained_increment (t : ℕ)
    (f : Option (State I V) → Option (Noise I V) → ℝ) :
    StronglyMeasurable[snapshotFiltration (t + 1)]
      (fun ω : FiniteHistory.Path (Snapshot I V) => f (ω t).1 (ω (t + 1)).2) := by
  exact (measurable_snapshot_prefix_response (t + 1)
    (fun h => f (h ⟨t, Finset.mem_Iic.mpr (Nat.le_succ t)⟩).1
      (h ⟨t + 1, Finset.mem_Iic.mpr le_rfl⟩).2)).stronglyMeasurable

theorem stronglyMeasurable_domainTrack (p : Parameters) (q : ℕ) (G : Input I V)
    (i : I) (t : ℕ) :
    StronglyMeasurable[snapshotFiltration t] (domainTrack p q G i t) := by
  induction t with
  | zero =>
      have heq : domainTrack p q G i 0 = fun _ => ((domain G initialState i).card : ℝ) :=
        funext (domainTrack_zero p q G i)
      rw [heq]
      exact stronglyMeasurable_const
  | succ t ih =>
      have hsum := (ih.mono (snapshotFiltration.mono (Nat.le_succ t))).add
        (stronglyMeasurable_retained_increment t (domainTrackIncrement p q t G i))
      convert hsum using 1
      funext ω
      have h := domainTrack_succ_sub p q t G i ω
      change domainTrack p q G i (t + 1) ω =
        domainTrack p q G i t ω + domainTrackIncrement p q t G i (ω t).1 (ω (t + 1)).2
      linarith

theorem stronglyMeasurable_degreeTrack (p : Parameters) (q : ℕ) (G : Input I V)
    (v : V) (t : ℕ) :
    StronglyMeasurable[snapshotFiltration t] (degreeTrack p q G v t) := by
  induction t with
  | zero =>
      have heq : degreeTrack p q G v 0 = fun _ => (degree G initialState v : ℝ) :=
        funext (degreeTrack_zero p q G v)
      rw [heq]
      exact stronglyMeasurable_const
  | succ t ih =>
      have hsum := (ih.mono (snapshotFiltration.mono (Nat.le_succ t))).add
        (stronglyMeasurable_retained_increment t (degreeTrackIncrement p q t G v))
      convert hsum using 1
      funext ω
      have h := degreeTrack_succ_sub p q t G v ω
      change degreeTrack p q G v (t + 1) ω =
        degreeTrack p q G v t ω + degreeTrackIncrement p q t G v (ω t).1 (ω (t + 1)).2
      linarith

theorem condExp_current_retained_response (p : Parameters) (q t : ℕ) (G : Input I V)
    (f : Option (State I V) → Option (Noise I V) → ℝ) :
    (snapshotPathLaw p q G)[fun ω => f (ω t).1 (ω (t + 1)).2 | snapshotFiltration t]
      =ᵐ[snapshotPathLaw p q G]
        fun ω => ∑ draw, drawStepWeight p q t G (ω t).1 draw * f (ω t).1 draw := by
  exact condExp_retained_draw p q G t
    (fun h draw => f (h ⟨t, Finset.mem_Iic.mpr le_rfl⟩).1 draw)

theorem condExp_domainTrack_increment (p : Parameters) (q t : ℕ) (G : Input I V)
    (i : I) :
    (snapshotPathLaw p q G)[fun ω =>
      domainTrack p q G i (t + 1) ω - domainTrack p q G i t ω | snapshotFiltration t]
      =ᵐ[snapshotPathLaw p q G]
        fun ω => ∑ draw, drawStepWeight p q t G (ω t).1 draw *
          domainTrackIncrement p q t G i (ω t).1 draw := by
  simp_rw [domainTrack_succ_sub]
  exact condExp_current_retained_response p q t G (domainTrackIncrement p q t G i)

theorem condExp_degreeTrack_increment (p : Parameters) (q t : ℕ) (G : Input I V)
    (v : V) :
    (snapshotPathLaw p q G)[fun ω =>
      degreeTrack p q G v (t + 1) ω - degreeTrack p q G v t ω | snapshotFiltration t]
      =ᵐ[snapshotPathLaw p q G]
        fun ω => ∑ draw, drawStepWeight p q t G (ω t).1 draw *
          degreeTrackIncrement p q t G v (ω t).1 draw := by
  simp_rw [degreeTrack_succ_sub]
  exact condExp_current_retained_response p q t G (degreeTrackIncrement p q t G v)

end Balanced.Selection.Process

end

end OAI
