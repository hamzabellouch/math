import OAI.Analysis.CircleDomains.Transfer.FilledMetric
import OAI.Analysis.CircleDomains.Sobolev.StaircaseGradient

namespace OAI

/-!
# Analytic assembly after the finite disks are selected

A frequently small wedge integral and the eventual collar conditions
select one common width, one smooth filled coordinate family, and one
core-preserving metric. This is the analytic part of finite transfer;
the geometric disk and period constructions are separate inputs here.
-/

open Set Filter MeasureTheory
open scoped Topology ContDiff Matrix.Norms.Elementwise

noncomputable section

namespace CircleDomainRigidity.FiniteTransfer

theorem IsFilledCoordinateFamily.eventuallyEq_near_set
    {I L : Type*} [Fintype I] [Fintype L]
    {D : I → Set (ℝ × ℝ)} {Ω K : Set (ℝ × ℝ)}
    {v F : L → (ℝ × ℝ) → ℝ} (hF : IsFilledCoordinateFamily D Ω v F)
    (hD : ∀ i, IsOpen (D i)) (hK : ∀ x ∈ K, ∀ i, x ∉ D i) :
    ∀ᶠ x in 𝓝ˢ K, ∀ l, F l x = v l x := by
  apply eventually_nhdsSet_iff_forall.mpr
  intro x hx
  exact eventually_all.mpr (fun l => hF.eventuallyEq_outside hD (hK x hx) l)

theorem cutoffStaircase_eventuallyEq_original
    {X L : Type*} [TopologicalSpace X] {K : Set X}
    (u : L → X → ℝ) (P : L → ℝ → ℝ) (χ : X → ℝ)
    (hχ : ∀ᶠ x in 𝓝ˢ K, χ x = 0) :
    ∀ᶠ x in 𝓝ˢ K, ∀ l, cutoffStaircase (u l) χ (P l) x = u l x := by
  filter_upwards [hχ] with x hx l
  exact cutoffStaircase_of_zero hx

/-- Choose the same late width for the collar fillings and energy budget.
The output coordinates and metric agree with the originals near the core.
-/
theorem exists_filled_family_and_metric_at_good_width
    {I : Type*} [Fintype I] {n : ℕ}
    (D : I → Set (ℝ × ℝ)) (hD : ∀ i, IsOpen (D i))
    {Ω Q K U : Set (ℝ × ℝ)} (hΩ : IsOpen Ω) (hQ : IsCompact Q) (hQΩ : Q ⊆ Ω)
    (hK : IsCompact K) (hU : IsOpen U) (hKU : K ⊆ U)
    (hKD : ∀ x ∈ K, ∀ i, x ∉ D i)
    (v : ℝ → Fin n → (ℝ × ℝ) → ℝ) (u : Fin n → (ℝ × ℝ) → ℝ)
    (hretain : ∀ δ, ∀ᶠ x in 𝓝ˢ K, ∀ i, v δ i x = u i x)
    {h : ℝ} (hh : 0 < h)
    (hfill : ∀ᶠ δ : ℝ in 𝓝[>] 0, ∃ F : Fin n → (ℝ × ℝ) → ℝ,
      IsFilledCoordinateFamily D Ω (v δ) F)
    (hvi : ∀ k, IntegrableOn
      (fun z => 2 * coordinateWedges (natCoordinateFamily (v (staircaseWidth h k))) n z) (Q \ K))
    {ε : ℝ}
    (hgood : ∃ᶠ k in atTop,
      (∫ z in Q \ K, 2 * coordinateWedges (natCoordinateFamily (v (staircaseWidth h k))) n z) < ε)
    (k₀ : ℕ) :
    ∃ (k : ℕ) (F : Fin n → (ℝ × ℝ) → ℝ) (g : (ℝ × ℝ) → PlanarMetric),
      k₀ ≤ k ∧ IsFilledCoordinateFamily D Ω (v (staircaseWidth h k)) F ∧
      (∀ᶠ z in 𝓝ˢ K, ∀ i, F i z = u i z) ∧
      ContDiff ℝ ∞ g ∧ (∀ z, (g z).PosDef) ∧
      (∀ᶠ z in 𝓝ˢ K, g z = 1) ∧
      (∫ z in Q \ K, matrixEnergy (coordinateGram (natCoordinateFamily F) n z) (g z)) < ε := by
  obtain ⟨k, F, hk, hcost, hF⟩ :=
    exists_good_width_filled_coordinates D Ω v hh hfill _ hgood k₀
  obtain ⟨τ, N, g, _, _, _, _, hg, hPD, hcore, _, henergy⟩ :=
    hF.exists_small_energy_metric hD hΩ hQ hQΩ hK hU hKU (hvi k) hcost
  refine ⟨k, F, g, hk, hF, ?_, hg, hPD, hcore, henergy⟩
  filter_upwards [hF.eventuallyEq_near_set hD hKD, hretain (staircaseWidth h k)] with z hz hvz i
  exact (hz i).trans (hvz i)

end CircleDomainRigidity.FiniteTransfer

end

end OAI
