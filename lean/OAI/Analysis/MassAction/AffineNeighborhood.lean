import OAI.Analysis.MassAction.AffineApproximation
import OAI.Analysis.MassAction.FixedMinimum

namespace OAI

noncomputable section

open Set Filter
open scoped Topology

namespace Problem326.Affine

variable {d : ℕ}

def coordinateMinimum [NeZero d] (p : Fin d → ℝ) : ℝ :=
  Finset.univ.inf' Finset.univ_nonempty p

theorem continuous_coordinateMinimum [NeZero d] :
    Continuous (coordinateMinimum (d := d)) := by
  exact Continuous.finset_inf'_apply Finset.univ_nonempty (fun i _ => continuous_apply i)

theorem hasMinimum_coordinateMinimum [NeZero d] (p : Fin d → ℝ) :
    HasMinimum p (coordinateMinimum p) := by
  refine ⟨fun i => Finset.inf'_le p (Finset.mem_univ i), ?_⟩
  obtain ⟨i, _, hi⟩ := Finset.exists_mem_eq_inf' Finset.univ_nonempty p
  exact ⟨i, hi.symm⟩

theorem hasMinimum_iff_coordinateMinimum_eq [NeZero d] (p : Fin d → ℝ) (t : ℝ) :
    HasMinimum p t ↔ coordinateMinimum p = t := by
  constructor
  · rintro ⟨hlower, i, hi⟩
    apply le_antisymm
    · exact (Finset.inf'_le p (Finset.mem_univ i)).trans hi.le
    · exact Finset.le_inf' Finset.univ_nonempty p (fun j _ => hlower j)
  · intro h
    rw [← h]
    exact hasMinimum_coordinateMinimum p

theorem isCompact_cube (a b : ℝ) : IsCompact {p : Fin d → ℝ | Cube a b p} := by
  have heq : {p : Fin d → ℝ | Cube a b p} = Icc (fun _ => a) (fun _ => b) := by
    ext p
    simp only [mem_ofPred_eq, Cube, mem_Icc, Pi.le_def, forall_and]
  rw [heq]
  exact isCompact_Icc

/-- Activity that approximates at a fixed minimum
continues to approximate for every limiting minimum in a positive band. -/
theorem ApproximatesAtMinimum.exists_nearby [NeZero d]
    {Λ : Finset (Label d)} {a b t : ℝ} {E : (Fin d → ℝ) → ℝ}
    (hΛ : ApproximatesAtMinimum Λ a b t E) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ L ∈ Λ,
      ∀ (h : ℕ → ℝ) (p : ℕ → (Fin d → ℝ)) (p₀ : Fin d → ℝ),
      (∀ n, 0 < h n) → Tendsto h atTop (𝓝 0) →
      Tendsto p atTop (𝓝 p₀) → Cube a b p₀ →
      |coordinateMinimum p₀ - t| < ρ →
      (∀ n, Active Λ L (h n) (powerPoint (h n) (p n))) →
      ‖p₀ - L.slope‖ < E L.slope := by
  classical
  let A : ℝ → (Fin d → ℝ) → ↥Λ → Prop :=
    fun h p L => Active Λ L.val h (powerPoint h p)
  obtain ⟨ρ, hρ, hnear⟩ := AffineApproximation.nearby_level_activity A
    (isCompact_cube (d := d) a b) coordinateMinimum continuous_coordinateMinimum t
    (fun L p => ‖p - L.val.slope‖)
    (fun _ => (continuous_id.sub continuous_const).norm)
    (fun L => E L.val.slope) (by
      intro L p₀ hp₀ hlim hmin
      obtain ⟨h, p, hpos, hh, hp, hactive⟩ :=
        (AffineApproximation.mem_limitActivity_iff_seq A L p₀).mp hlim
      exact hΛ L.val L.property h p p₀ hpos hh hp hp₀
        ((hasMinimum_iff_coordinateMinimum_eq p₀ t).mpr hmin) hactive)
  refine ⟨ρ, hρ, ?_⟩
  intro L hL h p p₀ hpos hh hp hp₀ hclose hactive
  apply hnear ⟨L, hL⟩ p₀ hp₀ _ hclose
  exact (AffineApproximation.mem_limitActivity_iff_seq A ⟨L, hL⟩ p₀).mpr
    ⟨h, p, hpos, hh, hp, hactive⟩

/-- The full sequential conclusion of the affine approximation lemma. -/
def ApproximatesOnCube (Λ : Finset (Label d))
    (a b : ℝ) (E : (Fin d → ℝ) → ℝ) : Prop :=
  ∀ L ∈ Λ, ∀ (h : ℕ → ℝ) (p : ℕ → (Fin d → ℝ)) (p₀ : Fin d → ℝ),
    (∀ n, 0 < h n) → Tendsto h atTop (𝓝 0) →
    Tendsto p atTop (𝓝 p₀) → Cube a b p₀ →
    (∀ n, Active Λ L (h n) (powerPoint (h n) (p n))) →
    ‖p₀ - L.slope‖ < E L.slope

/-- Uniform-activity corollary for the exact affine-label interface. -/
theorem ApproximatesOnCube.uniform_activity
    {Λ : Finset (Label d)} {a b : ℝ} {E : (Fin d → ℝ) → ℝ}
    (hΛ : ApproximatesOnCube Λ a b E) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ h, 0 < h → h < δ →
      ∀ p, Cube a b p → ∀ L ∈ Λ,
      Active Λ L h (powerPoint h p) → ‖p - L.slope‖ < E L.slope := by
  classical
  let A : ℝ → (Fin d → ℝ) → ↥Λ → Prop :=
    fun h p L => Active Λ L.val h (powerPoint h p)
  obtain ⟨δ, hδ, hbound⟩ := AffineApproximation.uniform_activity_of_sequence A
    (isCompact_cube (d := d) a b)
    (fun L p => ‖p - L.val.slope‖)
    (fun _ => (continuous_id.sub continuous_const).norm)
    (fun L => E L.val.slope) (by
      intro L p₀ hp₀ h p hpos hh hp hactive
      exact hΛ L.val L.property h p p₀ hpos hh hp hp₀ hactive)
  exact ⟨δ, hδ, fun h hh hsmall p hp L hL hactive =>
    hbound h hh hsmall p hp ⟨L, hL⟩ hactive⟩

end Problem326.Affine

end

end OAI
