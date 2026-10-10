import OAI.Analysis.MassAction.FixedMinimum
import OAI.Analysis.MassAction.ActivityLimits

namespace OAI

noncomputable section

open Set Filter
open scoped Topology

namespace Problem326.Affine

/-- The least coordinate in a positive-dimensional exponent vector. -/
def minimumCoordinate {d : ℕ} (hd : 0 < d) (p : Fin d → ℝ) : ℝ :=
  Finset.univ.inf' ⟨⟨0, hd⟩, Finset.mem_univ _⟩ p

theorem continuous_minimumCoordinate {d : ℕ} (hd : 0 < d) :
    Continuous (minimumCoordinate hd) := by
  exact Continuous.finset_inf'_apply _ (fun i _ => continuous_apply i)

theorem hasMinimum_minimumCoordinate {d : ℕ} (hd : 0 < d) (p : Fin d → ℝ) :
    HasMinimum p (minimumCoordinate hd p) := by
  refine ⟨fun i => Finset.inf'_le p (Finset.mem_univ i), ?_⟩
  obtain ⟨i, hi, heq⟩ := Finset.exists_mem_eq_inf'
    (⟨⟨0, hd⟩, Finset.mem_univ _⟩ : (Finset.univ : Finset (Fin d)).Nonempty) p
  exact ⟨i, heq.symm⟩

theorem minimumCoordinate_eq_of_hasMinimum {d : ℕ} (hd : 0 < d)
    {p : Fin d → ℝ} {t : ℝ} (hm : HasMinimum p t) :
    minimumCoordinate hd p = t := by
  apply le_antisymm
  · obtain ⟨i, hi⟩ := hm.2
    exact (Finset.inf'_le p (Finset.mem_univ i)).trans_eq hi
  · exact Finset.le_inf' _ p (fun i _ => hm.1 i)

theorem minimumCoordinate_mem_Icc {d : ℕ} (hd : 0 < d)
    {p : Fin d → ℝ} {a b : ℝ} (hp : Cube a b p) :
    minimumCoordinate hd p ∈ Icc a b := by
  obtain ⟨i, hi⟩ := (hasMinimum_minimumCoordinate hd p).2
  simpa only [← hi, Set.mem_Icc] using hp i

theorem isCompact_cube_localBand {d : ℕ} (a b : ℝ) :
    IsCompact {p : Fin d → ℝ | Cube a b p} := by
  exact isCompact_pi_infinite (fun _ => isCompact_Icc)

/-- Approximation at a fixed
minimum level extends to a band of nearby minimum levels. Approximating
sequences themselves may leave the exponent cube. -/
theorem exists_local_band_of_approximatesAtMinimum
    {d : ℕ} (hd : 0 < d) (Λ : Finset (Label d)) (a b t : ℝ)
    (E : (Fin d → ℝ) → ℝ) (happrox : ApproximatesAtMinimum Λ a b t E) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ L ∈ Λ,
      ∀ (h : ℕ → ℝ) (p : ℕ → (Fin d → ℝ)) (p₀ : Fin d → ℝ),
      (∀ n, 0 < h n) → Tendsto h atTop (𝓝 0) →
      Tendsto p atTop (𝓝 p₀) → Cube a b p₀ →
      |minimumCoordinate hd p₀ - t| < ρ →
      (∀ n, Active Λ L (h n) (powerPoint (h n) (p n))) →
      ‖p₀ - L.slope‖ < E L.slope := by
  classical
  let active : Λ → ℝ → (Fin d → ℝ) → Prop :=
    fun L h p => Active Λ L.val h (powerPoint h p)
  let good : Λ → Set (Fin d → ℝ) :=
    fun L => {p | ‖p - L.val.slope‖ < E L.val.slope}
  have hgood (L : Λ) : IsOpen (good L) :=
    isOpen_lt (continuous_id.sub continuous_const).norm continuous_const
  have hlevel (L : Λ) (z : Fin d → ℝ) (hz : Cube a b z)
      (heq : minimumCoordinate hd z = t)
      (ha : z ∈ activityLimitSet (active L)) : z ∈ good L := by
    obtain ⟨h, p, hhpos, hh, hp, hactive⟩ :=
      exists_active_sequence_of_mem_activityLimitSet ha
    apply happrox L.val L.property h p z hhpos hh hp hz
    · simpa only [heq] using hasMinimum_minimumCoordinate hd z
    · exact hactive
  obtain ⟨ρ, hρ, hband⟩ := activity_limits_good_near_level
    (isCompact_cube_localBand (d := d) a b) active good hgood
    (continuous_minimumCoordinate hd).continuousOn t hlevel
  refine ⟨ρ, hρ, ?_⟩
  intro L hL h p p₀ hhpos hh hp hp₀ hnear hactive
  exact hband p₀ hp₀ hnear ⟨L, hL⟩
    (mem_activityLimitSet_of_tendsto hhpos hh hp hactive)

/-- Convenient family-level interface for gluing: the same finite family
approximates at every minimum level in an open interval about `t`. -/
theorem approximatesAtMinimum_nearby
    {d : ℕ} (hd : 0 < d) (Λ : Finset (Label d)) (a b t : ℝ)
    (E : (Fin d → ℝ) → ℝ) (happrox : ApproximatesAtMinimum Λ a b t E) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ s ∈ Ioo (t - ρ) (t + ρ),
      ApproximatesAtMinimum Λ a b s E := by
  obtain ⟨ρ, hρ, hband⟩ :=
    exists_local_band_of_approximatesAtMinimum hd Λ a b t E happrox
  refine ⟨ρ, hρ, ?_⟩
  intro s hs L hL h p p₀ hhpos hh hp hp₀ hm hactive
  apply hband L hL h p p₀ hhpos hh hp hp₀ _ hactive
  rw [minimumCoordinate_eq_of_hasMinimum hd hm, abs_lt]
  constructor <;> linarith [hs.1, hs.2]

end Problem326.Affine

end

end OAI
