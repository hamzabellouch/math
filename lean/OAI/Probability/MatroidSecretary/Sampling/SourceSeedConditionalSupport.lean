import OAI.Probability.MatroidSecretary.Sampling.SourceSeedSupport
import OAI.Probability.MatroidSecretary.Secretary.Coupling

namespace OAI

/-!
Strict support for the actual finite conditional reconstruction. Every advertised
branch/mask fiber has positive source mass, so the zero-fiber fallback is never
used for these concrete kernels. The conditional law is supported exactly on its
fiber, not on the whole source space; this does not remove the secretary replay's
every-seed mismatch guard.

Source: `sections/secretary.tex`, lines 68--78, SHA256
`3554fe0f7296782edf63cc7f1305c377e7a7b9d8f8948b9510ea4ad02a702d63`.
-/

namespace MatroidProphet.SourceSeedSupport

open MeasureTheory Secretary

theorem coupling_fiberMass_pos {n : ℕ} (M : Matroid (Fin n))
    (hE : M.E = Set.univ) (b : SourceObservation n) :
    0 < fiberMass (fun r => (sourceSeedLaw n).real {r}) (couplingObservation M hE) b := by
  have hpos : 0 < sourceSeedLaw n {r | couplingObservation M hE r = b} := by
    rcases b with ⟨j, P⟩
    simpa only [couplingObservation, Prod.mk.injEq] using
      sourceSeedLaw_actual_branch_mask_pos M hE j P
  have hr : 0 < ((sourceSeedLaw n).map (couplingObservation M hE)).real {b} := by
    rw [measureReal_def, Measure.map_apply (measurable_of_finite _) (measurableSet_singleton _)]
    exact ENNReal.toReal_pos hpos.ne' (measure_ne_top _ _)
  have hmass : fiberMass (fun r => (sourceSeedLaw n).real {r})
      (couplingObservation M hE) b =
      ((sourceSeedLaw n).map (couplingObservation M hE)).real {b} := by
    rw [FiniteLaw.map_real_singleton]
    unfold fiberMass
    apply Finset.sum_congr rfl
    intro r _
    by_cases h : couplingObservation M hE r = b <;> simp [h]
  rw [hmass]
  exact hr

/-- Each complete source seed has positive conditional mass exactly in its
advertised branch/mask fiber, including unused source coordinates. -/
theorem couplingKernel_singleton_pos_iff {n : ℕ} (M : Matroid (Fin n))
    (hE : M.E = Set.univ) (b : SourceObservation n) (r : Seed (mainSeedBits n)) :
    0 < couplingKernel M hE b {r} ↔ couplingObservation M hE r = b := by
  have hb := coupling_fiberMass_pos M hE b
  have hr : 0 < (sourceSeedLaw n).real {r} :=
    ENNReal.toReal_pos (sourceSeedLaw_singleton_pos n r).ne' (measure_ne_top _ _)
  rw [couplingKernel, conditionalSourceLaw, FiniteLaw.weightMeasure_singleton,
    ENNReal.ofReal_pos]
  simp only [fiberKernel, hb.ne', ite_false]
  by_cases h : couplingObservation M hE r = b
  · simp only [h, ite_true, iff_true]
    exact div_pos hr hb
  · simp [h]

end MatroidProphet.SourceSeedSupport

end OAI
