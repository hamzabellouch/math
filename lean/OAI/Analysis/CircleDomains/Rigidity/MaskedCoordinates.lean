import OAI.Analysis.CircleDomains.Sobolev.CoordinateEstimates

namespace OAI

/-!
# Smooth auxiliary coordinates for closed masks

The mask boundaries lie strictly inside the retained core. Smooth
extensions therefore realize the masked coordinate differentials exactly
on the region where the metric is changed. Their arbitrary values in
the core never enter the tail energy estimate.
-/

open Set Filter MeasureTheory
open scoped Topology ContDiff Matrix.Norms.Elementwise

noncomputable section

namespace CircleDomainRigidity.FiniteTransfer

def maskedGradient (M : Set (ℝ × ℝ)) (f : (ℝ × ℝ) → ℝ) (z : ℝ × ℝ) : ℝ × ℝ :=
  M.indicator (planarGradient f) z

/-- Closed masks with boundaries in the interior of the retained core
admit globally smooth auxiliary coordinates with the exact masked
covectors everywhere outside that core in the completed piece. -/
theorem exists_smooth_masked_coordinate
    {Ω Q K M : Set (ℝ × ℝ)} (hΩ : IsOpen Ω) (hQ : IsCompact Q) (hQΩ : Q ⊆ Ω)
    (hM : IsClosed M) (hboundary : frontier M ⊆ interior K)
    {f : (ℝ × ℝ) → ℝ} (hf : ContDiffOn ℝ ∞ f (Ω ∩ interior M)) :
    ∃ F : (ℝ × ℝ) → ℝ, ContDiff ℝ ∞ F ∧
      ∀ z ∈ Q \ K, planarGradient F z = maskedGradient M f z := by
  let A := (Q ∩ (interior K)ᶜ) ∩ M
  have hA : IsClosed A := (hQ.isClosed.inter isOpen_interior.isClosed_compl).inter hM
  have hAU : A ⊆ Ω ∩ interior M := by
    intro z hz
    refine ⟨hQΩ hz.1.1, (mem_interior_iff_notMem_frontier hz.2).mpr ?_⟩
    exact fun hb => hz.1.2 (hboundary hb)
  obtain ⟨F, hF, heq, hzero⟩ :=
    exists_smooth_collar_extension (hΩ.inter isOpen_interior) hA hAU hf 0
  refine ⟨F, hF, ?_⟩
  intro z hz
  by_cases hzM : z ∈ M
  · have hzA : z ∈ A := ⟨⟨hz.1, fun hi => hz.2 (interior_subset hi)⟩, hzM⟩
    have hder := (heq.filter_mono (nhds_le_nhdsSet hzA)).fderiv_eq (𝕜 := ℝ)
    simp only [maskedGradient, indicator_of_mem hzM, planarGradient, hder]
  · have hlocal : F =ᶠ[𝓝 z] fun _ => 0 := by
      filter_upwards [hM.isOpen_compl.mem_nhds hzM] with w hw
      exact hzero w (fun h => hw (interior_subset h.2))
    have hder := hlocal.fderiv_eq (𝕜 := ℝ)
    simp only [maskedGradient, indicator_of_notMem hzM, planarGradient, hder,
      fderiv_const_apply, zero_apply]
    rfl

/-- A finite family of masked coordinates can be handled simultaneously.
The equality is an equality of actual planar covectors. -/
theorem exists_smooth_masked_family
    {n : ℕ} {Ω Q K : Set (ℝ × ℝ)} (hΩ : IsOpen Ω) (hQ : IsCompact Q) (hQΩ : Q ⊆ Ω)
    (M : Fin n → Set (ℝ × ℝ)) (hM : ∀ i, IsClosed (M i))
    (hboundary : ∀ i, frontier (M i) ⊆ interior K)
    (f : Fin n → (ℝ × ℝ) → ℝ) (hf : ∀ i, ContDiffOn ℝ ∞ (f i) (Ω ∩ interior (M i))) :
    ∃ F : Fin n → (ℝ × ℝ) → ℝ, (∀ i, ContDiff ℝ ∞ (F i)) ∧
      ∀ i z, z ∈ Q \ K → planarGradient (F i) z = maskedGradient (M i) (f i) z := by
  choose F hF hgrad using fun i =>
    exists_smooth_masked_coordinate hΩ hQ hQΩ (hM i) (hboundary i) (hf i)
  exact ⟨F, hF, hgrad⟩

end CircleDomainRigidity.FiniteTransfer

end

end OAI
