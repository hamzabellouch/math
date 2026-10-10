import OAI.Analysis.Mahler.ShellRegularity

namespace OAI

noncomputable section
open Set MeasureTheory
namespace MahlerStokes

lemma finite_radiusSq_slice {n : ℕ} (i : Fin (n+1)) (R : ℝ) (y : Fin n → ℝ) :
    Set.Finite {t : ℝ | radiusSq (i.insertNth t y) = R^2} := by
  apply (Set.toFinite ({chord R y, -chord R y} : Set ℝ)).subset
  intro t ht
  have hsq : t^2 = R^2 - radiusSq y := by
    change radiusSq (i.insertNth t y) = R^2 at ht
    rw [radiusSq_insertNth] at ht; linarith
  have hc : (chord R y)^2 = R^2 - radiusSq y := Real.sq_sqrt (hsq ▸ sq_nonneg t)
  have he : t = chord R y ∨ t = -chord R y := sq_eq_sq_iff_eq_or_eq_neg.mp (hsq.trans hc.symm)
  simpa only [mem_insert_iff, mem_singleton_iff] using he

/-- Coordinate Euclidean spheres have zero Lebesgue measure. -/
theorem volume_coordSphere {n : ℕ} (R : ℝ) :
    volume {x : Fin (n+1) → ℝ | radiusSq x = R^2} = 0 := by
  let s : Set (Fin (n+1) → ℝ) := {x | radiusSq x = R^2}
  have hs : MeasurableSet s := (isClosed_eq (continuous_radiusSq _) continuous_const).measurableSet
  have hsub : s ⊆ coordClosedBall (n+1) R := fun x hx => hx.le
  have hf : IntegrableOn (fun _ : Fin (n+1) → ℝ => (1 : ℝ)) s :=
    (continuous_const.continuousOn.integrableOn_compact (isCompact_coordClosedBall (n+1) R)).mono_set hsub
  have hi : (∫ x in s, (1 : ℝ)) = 0 := by
    rw [setIntegral_slice (0 : Fin (n+1)) hs _ hf]
    have hz (y : Fin n → ℝ) :
        (∫ t in {t | (0 : Fin (n+1)).insertNth t y ∈ s}, (1 : ℝ)) = 0 := by
      apply setIntegral_measure_zero
      exact (finite_radiusSq_slice 0 R y).measure_zero volume
    simp_rw [hz]
    simp
  have hfinite : volume s ≠ ⊤ :=
    ne_top_of_le_ne_top (isCompact_coordClosedBall (n+1) R).measure_ne_top (measure_mono hsub)
  have hr : (volume s).toReal = 0 := by simpa [measureReal_def] using hi
  exact (ENNReal.toReal_eq_zero_iff _).1 hr |>.resolve_right hfinite

/-- Removing the closed inner ball changes no volume integral. -/
theorem coordAnnulus_ae_eq_puncture {n : ℕ} (a R : ℝ) :
    coordAnnulus (n+1) a R =ᵐ[volume]
      coordBall (n+1) R \ coordClosedBall (n+1) a := by
  have hae : ∀ᵐ x : Fin (n+1) → ℝ ∂volume, x ∉ {x | radiusSq x = a^2} :=
    (ae_iff).2 (by simpa using volume_coordSphere (n := n) a)
  filter_upwards [hae] with x hx
  apply propext
  change (radiusSq x < R^2 ∧ ¬radiusSq x < a^2) ↔
    (radiusSq x < R^2 ∧ ¬radiusSq x ≤ a^2)
  have hn : radiusSq x ≠ a^2 := hx
  constructor
  · intro h; exact ⟨h.1, fun hh => hn (le_antisymm hh (le_of_not_gt h.2))⟩
  · intro h; exact ⟨h.1, fun hh => h.2 hh.le⟩

end MahlerStokes

end

end OAI
