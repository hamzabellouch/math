import OAI.Analysis.CircleDomains.Topology.RegularJordanCollar

namespace OAI

/-! Select a genuine smooth inner mask while retaining a compact core,
remaining in a prescribed physical boundary neighborhood, and controlling
the parametrized displacement. The choices use a single collar. -/

open Set Function Filter Metric
open scoped Topology ENNReal

noncomputable section
namespace CircleDomainRigidity

 theorem RegularJordanInwardCollar.folded_continuous
    {H : ℂ ≃ₜ ℂ} (C : RegularJordanInwardCollar H) :
    ContinuousOn (fun p : ℝ × ℝ => C.curve |p.1| p.2)
      (Ioo (-C.width) C.width ×ˢ univ) := by
  apply C.continuous.comp (continuous_fst.abs.prodMk continuous_snd).continuousOn
  intro p hp
  exact ⟨⟨abs_nonneg _, (abs_lt.mpr hp.1).le⟩, mem_univ _⟩

 theorem RegularJordanInwardCollar.select_inner
    {H : ℂ ≃ₜ ℂ} (C : RegularJordanInwardCollar H)
    {K O : Set ℂ} (hK : IsCompact K) (hKH : K ⊆ jordanInterior H)
    (hO : IsOpen O) (hboundary : frontier (jordanInterior H) ⊆ O)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ ρ > 0, ρ ≤ C.width ∧ K ⊆ jordanInterior (C.disk ρ) ∧
      closure (jordanInterior (C.disk ρ)) ⊆ jordanInterior H ∧
      frontier (jordanInterior (C.disk ρ)) ⊆ O ∧
      ∀ t ∈ Icc (0 : ℝ) 1, dist (C.curve ρ t) (C.curve 0 t) < ε := by
  obtain ⟨a, ha, haw, hcore⟩ := C.retains_compact K hK hKH
  obtain ⟨b, hb, hbw, hnear⟩ := C.eventually_in_boundary_neighborhood hO hboundary
  obtain ⟨c, hc, hcw, hmove⟩ := C.uniform_approach ε hε
  let ρ := min a (min b c) / 2
  have hρ : 0 < ρ := half_pos (lt_min ha (lt_min hb hc))
  have hρa : ρ ≤ a := (half_le_self (le_of_lt (lt_min ha (lt_min hb hc)))).trans (min_le_left _ _)
  have hρb : ρ ≤ b := (half_le_self (le_of_lt (lt_min ha (lt_min hb hc)))).trans
    ((min_le_right _ _).trans (min_le_left _ _))
  have hρc : ρ ≤ c := (half_le_self (le_of_lt (lt_min ha (lt_min hb hc)))).trans
    ((min_le_right _ _).trans (min_le_right _ _))
  have hρw : ρ ≤ C.width := hρa.trans haw
  refine ⟨ρ, hρ, hρw, hcore ρ ⟨hρ, hρa⟩, C.inward ρ ⟨hρ, hρw⟩, ?_,
    hmove ρ ⟨hρ.le, hρc⟩⟩
  intro z hz
  obtain ⟨t, ht, rfl⟩ := (C.parametrization ρ ⟨hρ.le, hρw⟩).boundary.symm ▸ hz
  exact hnear ρ ⟨hρ.le, hρb⟩ t ht

 theorem WeightedCollar.exists_smooth_inner_mask
    (hcollar : SmoothRegularJordanCollars)
    {G : Set Sphere} {π : Sphere → Sphere} {B : Set Sphere} {p : Sphere} {g : ℂ → ℝ≥0∞}
    (D : WeightedCollar G π B p g) {K O : Set ℂ}
    (hK : IsCompact K) (hKD : K ⊆ jordanInterior D.disk)
    (hO : IsOpen O) (hboundary : frontier (jordanInterior D.disk) ⊆ O)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ (C : RegularJordanInwardCollar D.disk) (ρ : ℝ), 0 < ρ ∧ ρ ≤ C.width ∧
      K ⊆ jordanInterior (C.disk ρ) ∧
      closure (jordanInterior (C.disk ρ)) ⊆ jordanInterior D.disk ∧
      frontier (jordanInterior (C.disk ρ)) ⊆ O ∧
      ∀ t ∈ Icc (0 : ℝ) 1, dist (C.curve ρ t) (C.curve 0 t) < ε := by
  obtain ⟨C⟩ := D.exists_regular_inward_collar hcollar
  obtain ⟨ρ, hρ⟩ := C.select_inner hK hKD hO hboundary hε
  exact ⟨C, ρ, hρ⟩

end CircleDomainRigidity

end

end OAI
